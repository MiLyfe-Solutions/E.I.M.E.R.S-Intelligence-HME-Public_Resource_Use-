import V185TrunkScan22Chunk239

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2139766 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2139766 : Nat := 118140960795 + 2139766 * 2 ^ 59
def prefixEnd_2139766 : Nat := 4983230072969 + 3 ^ 40 * 2139766 * 2
def baseEnd_2139766 : Nat := 732485630765720259589601

theorem tailTrace_2139766 : CollatzResearch.WordTrace tailWord_2139766 prefixEnd_2139766 732485630765720259589601 := by
  unfold tailWord_2139766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877729847875043736469447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52029118377333799855674101 4877729847875043736469447)
  ·
    refine ⟨7316594771812565604704171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4877729847875043736469447 7316594771812565604704171)
    ·
      refine ⟨10974892157718848407056257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7316594771812565604704171 10974892157718848407056257)
      ·
        refine ⟨8231169118289136305292193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10974892157718848407056257 8231169118289136305292193)
        ·
          refine ⟨6173376838716852228969145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8231169118289136305292193 6173376838716852228969145)
          ·
            refine ⟨4630032629037639171726859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173376838716852228969145 4630032629037639171726859)
            ·
              refine ⟨6945048943556458757590289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630032629037639171726859 6945048943556458757590289)
              ·
                refine ⟨5208786707667344068192717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945048943556458757590289 5208786707667344068192717)
                ·
                  refine ⟨1953295015375254025572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5208786707667344068192717 1953295015375254025572269)
                  ·
                    refine ⟨732485630765720259589601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953295015375254025572269 732485630765720259589601)
                    ·
                      rfl

theorem cell22_2139766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2139766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139766 prefixEnd_2139766 := by exact prefixLift 2139766
  have htrace : WordTrace (prefixWord ++ tailWord_2139766) baseStart_2139766 baseEnd_2139766 := by
    simpa [prefixWord, tailWord_2139766, baseEnd_2139766] using wordTrace_append hprefix tailTrace_2139766
  have hstable : (prefixWord ++ tailWord_2139766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139766).length < 2 ^ (prefixWord ++ tailWord_2139766).sum := by decide
  have hdescent : baseEnd_2139766 < baseStart_2139766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139837 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2139837 : Nat := 118140960795 + 2139837 * 2 ^ 59
def prefixEnd_2139837 : Nat := 4983230072969 + 3 ^ 40 * 2139837 * 2
def baseEnd_2139837 : Nat := 732509935516699741064383

theorem tailTrace_2139837 : CollatzResearch.WordTrace tailWord_2139837 prefixEnd_2139837 732509935516699741064383 := by
  unfold tailWord_2139837
  simp only [CollatzResearch.WordTrace]
  refine ⟨78046267148743478909345765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52030844765828985939563843 78046267148743478909345765)
  ·
    refine ⟨14633675090389402295502331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78046267148743478909345765 14633675090389402295502331)
    ·
      refine ⟨21950512635584103443253497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14633675090389402295502331 21950512635584103443253497)
      ·
        refine ⟨16462884476688077582440123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21950512635584103443253497 16462884476688077582440123)
        ·
          refine ⟨24694326715032116373660185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16462884476688077582440123 24694326715032116373660185)
          ·
            refine ⟨18520745036274087280245139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24694326715032116373660185 18520745036274087280245139)
            ·
              refine ⟨27781117554411130920367709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18520745036274087280245139 27781117554411130920367709)
              ·
                refine ⟨10417919082904174095137891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27781117554411130920367709 10417919082904174095137891)
                ·
                  refine ⟨15626878624356261142706837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10417919082904174095137891 15626878624356261142706837)
                  ·
                    refine ⟨732509935516699741064383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15626878624356261142706837 732509935516699741064383)
                    ·
                      rfl

theorem cell22_2139837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2139837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139837 prefixEnd_2139837 := by exact prefixLift 2139837
  have htrace : WordTrace (prefixWord ++ tailWord_2139837) baseStart_2139837 baseEnd_2139837 := by
    simpa [prefixWord, tailWord_2139837, baseEnd_2139837] using wordTrace_append hprefix tailTrace_2139837
  have hstable : (prefixWord ++ tailWord_2139837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139837).length < 2 ^ (prefixWord ++ tailWord_2139837).sum := by decide
  have hdescent : baseEnd_2139837 < baseStart_2139837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139854 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2139854 : Nat := 118140960795 + 2139854 * 2 ^ 59
def prefixEnd_2139854 : Nat := 4983230072969 + 3 ^ 40 * 2139854 * 2
def baseEnd_2139854 : Nat := 732515754964117363389331

theorem tailTrace_2139854 : CollatzResearch.WordTrace tailWord_2139854 prefixEnd_2139854 732515754964117363389331 := by
  unfold tailWord_2139854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755860898710236351589327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52031258126454593875143077 9755860898710236351589327)
  ·
    refine ⟨14633791348065354527383991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9755860898710236351589327 14633791348065354527383991)
    ·
      refine ⟨21950687022098031791075987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14633791348065354527383991 21950687022098031791075987)
      ·
        refine ⟨32926030533147047686613981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21950687022098031791075987 32926030533147047686613981)
        ·
          refine ⟨12347261449930142882480243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32926030533147047686613981 12347261449930142882480243)
          ·
            refine ⟨18520892174895214323720365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12347261449930142882480243 18520892174895214323720365)
            ·
              refine ⟨6945334565585705371395137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18520892174895214323720365 6945334565585705371395137)
              ·
                refine ⟨5209000924189279028546353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6945334565585705371395137 5209000924189279028546353)
                ·
                  refine ⟨3906750693141959271409765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5209000924189279028546353 3906750693141959271409765)
                  ·
                    refine ⟨732515754964117363389331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3906750693141959271409765 732515754964117363389331)
                    ·
                      rfl

theorem cell22_2139854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2139854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139854 prefixEnd_2139854 := by exact prefixLift 2139854
  have htrace : WordTrace (prefixWord ++ tailWord_2139854) baseStart_2139854 baseEnd_2139854 := by
    simpa [prefixWord, tailWord_2139854, baseEnd_2139854] using wordTrace_append hprefix tailTrace_2139854
  have hstable : (prefixWord ++ tailWord_2139854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139854).length < 2 ^ (prefixWord ++ tailWord_2139854).sum := by decide
  have hdescent : baseEnd_2139854 < baseStart_2139854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139858 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2139858 : Nat := 118140960795 + 2139858 * 2 ^ 59
def prefixEnd_2139858 : Nat := 4983230072969 + 3 ^ 40 * 2139858 * 2
def baseEnd_2139858 : Nat := 244172374748620895429773

theorem tailTrace_2139858 : CollatzResearch.WordTrace tailWord_2139858 prefixEnd_2139858 244172374748620895429773 := by
  unfold tailWord_2139858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511758270416849873965057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52031355387778266330573485 19511758270416849873965057)
  ·
    refine ⟨14633818702812637405473793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19511758270416849873965057 14633818702812637405473793)
    ·
      refine ⟨10975364027109478054105345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14633818702812637405473793 10975364027109478054105345)
      ·
        refine ⟨8231523020332108540579009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10975364027109478054105345 8231523020332108540579009)
        ·
          refine ⟨6173642265249081405434257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8231523020332108540579009 6173642265249081405434257)
          ·
            refine ⟨4630231698936811054075693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173642265249081405434257 4630231698936811054075693)
            ·
              refine ⟨1736336887101304145278385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4630231698936811054075693 1736336887101304145278385)
              ·
                refine ⟨1302252665325978108958789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736336887101304145278385 1302252665325978108958789)
                ·
                  refine ⟨244172374748620895429773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302252665325978108958789 244172374748620895429773)
                  ·
                    rfl

theorem cell22_2139858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2139858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139858 prefixEnd_2139858 := by exact prefixLift 2139858
  have htrace : WordTrace (prefixWord ++ tailWord_2139858) baseStart_2139858 baseEnd_2139858 := by
    simpa [prefixWord, tailWord_2139858, baseEnd_2139858] using wordTrace_append hprefix tailTrace_2139858
  have hstable : (prefixWord ++ tailWord_2139858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139858).length < 2 ^ (prefixWord ++ tailWord_2139858).sum := by decide
  have hdescent : baseEnd_2139858 < baseStart_2139858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139884 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_2139884 : Nat := 118140960795 + 2139884 * 2 ^ 59
def prefixEnd_2139884 : Nat := 4983230072969 + 3 ^ 40 * 2139884 * 2
def baseEnd_2139884 : Nat := 732526024577207285139239

theorem tailTrace_2139884 : CollatzResearch.WordTrace tailWord_2139884 prefixEnd_2139884 732526024577207285139239 := by
  unfold tailWord_2139884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39023990689786602968153353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52031987586382137290871137 39023990689786602968153353)
  ·
    refine ⟨29267993017339952226115015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39023990689786602968153353 29267993017339952226115015)
    ·
      refine ⟨43901989526009928339172523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29267993017339952226115015 43901989526009928339172523)
      ·
        refine ⟨65852984289014892508758785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43901989526009928339172523 65852984289014892508758785)
        ·
          refine ⟨49389738216761169381569089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65852984289014892508758785 49389738216761169381569089)
          ·
            refine ⟨37042303662570877036176817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49389738216761169381569089 37042303662570877036176817)
            ·
              refine ⟨27781727746928157777132613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37042303662570877036176817 27781727746928157777132613)
              ·
                refine ⟨5209073952549029583212365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27781727746928157777132613 5209073952549029583212365)
                ·
                  refine ⟨1953402732205886093704637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5209073952549029583212365 1953402732205886093704637)
                  ·
                    refine ⟨732526024577207285139239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953402732205886093704637 732526024577207285139239)
                    ·
                      rfl

theorem cell22_2139884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_2139884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139884 prefixEnd_2139884 := by exact prefixLift 2139884
  have htrace : WordTrace (prefixWord ++ tailWord_2139884) baseStart_2139884 baseEnd_2139884 := by
    simpa [prefixWord, tailWord_2139884, baseEnd_2139884] using wordTrace_append hprefix tailTrace_2139884
  have hstable : (prefixWord ++ tailWord_2139884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139884).length < 2 ^ (prefixWord ++ tailWord_2139884).sum := by decide
  have hdescent : baseEnd_2139884 < baseStart_2139884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139914 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_2139914 : Nat := 118140960795 + 2139914 * 2 ^ 59
def prefixEnd_2139914 : Nat := 4983230072969 + 3 ^ 40 * 2139914 * 2
def baseEnd_2139914 : Nat := 244178764730099068963049

theorem tailTrace_2139914 : CollatzResearch.WordTrace tailWord_2139914 prefixEnd_2139914 244178764730099068963049 := by
  unfold tailWord_2139914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19512268892366130264974699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52032717046309680706599197 19512268892366130264974699)
  ·
    refine ⟨29268403338549195397462049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19512268892366130264974699 29268403338549195397462049)
    ·
      refine ⟨21951302503911896548096537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29268403338549195397462049 21951302503911896548096537)
      ·
        refine ⟨16463476877933922411072403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21951302503911896548096537 16463476877933922411072403)
        ·
          refine ⟨24695215316900883616608605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16463476877933922411072403 24695215316900883616608605)
          ·
            refine ⟨9260705743837831356228227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24695215316900883616608605 9260705743837831356228227)
            ·
              refine ⟨13891058615756747034342341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9260705743837831356228227 13891058615756747034342341)
              ·
                refine ⟨2604573490454390068939189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13891058615756747034342341 2604573490454390068939189)
                ·
                  refine ⟨244178764730099068963049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604573490454390068939189 244178764730099068963049)
                  ·
                    rfl

theorem cell22_2139914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_2139914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139914 prefixEnd_2139914 := by exact prefixLift 2139914
  have htrace : WordTrace (prefixWord ++ tailWord_2139914) baseStart_2139914 baseEnd_2139914 := by
    simpa [prefixWord, tailWord_2139914, baseEnd_2139914] using wordTrace_append hprefix tailTrace_2139914
  have hstable : (prefixWord ++ tailWord_2139914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139914).length < 2 ^ (prefixWord ++ tailWord_2139914).sum := by decide
  have hdescent : baseEnd_2139914 < baseStart_2139914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139976 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_2139976 : Nat := 118140960795 + 2139976 * 2 ^ 59
def prefixEnd_2139976 : Nat := 4983230072969 + 3 ^ 40 * 2139976 * 2
def baseEnd_2139976 : Nat := 244185839352449903946319

theorem tailTrace_2139976 : CollatzResearch.WordTrace tailWord_2139976 prefixEnd_2139976 244185839352449903946319 := by
  unfold tailWord_2139976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025668447619952824327891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52034224596826603765770521 39025668447619952824327891)
  ·
    refine ⟨58538502671429929236491837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39025668447619952824327891 58538502671429929236491837)
    ·
      refine ⟨21951938501786223463684439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58538502671429929236491837 21951938501786223463684439)
      ·
        refine ⟨32927907752679335195526659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21951938501786223463684439 32927907752679335195526659)
        ·
          refine ⟨49391861629019002793289989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32927907752679335195526659 49391861629019002793289989)
          ·
            refine ⟨9260974055441063023741873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49391861629019002793289989 9260974055441063023741873)
            ·
              refine ⟨6945730541580797267806405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9260974055441063023741873 6945730541580797267806405)
              ·
                refine ⟨1302324476546399487713701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6945730541580797267806405 1302324476546399487713701)
                ·
                  refine ⟨244185839352449903946319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302324476546399487713701 244185839352449903946319)
                  ·
                    rfl

theorem cell22_2139976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_2139976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139976 prefixEnd_2139976 := by exact prefixLift 2139976
  have htrace : WordTrace (prefixWord ++ tailWord_2139976) baseStart_2139976 baseEnd_2139976 := by
    simpa [prefixWord, tailWord_2139976, baseEnd_2139976] using wordTrace_append hprefix tailTrace_2139976
  have hstable : (prefixWord ++ tailWord_2139976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139976).length < 2 ^ (prefixWord ++ tailWord_2139976).sum := by decide
  have hdescent : baseEnd_2139976 < baseStart_2139976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2139989 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2139989 : Nat := 118140960795 + 2139989 * 2 ^ 59
def prefixEnd_2139989 : Nat := 4983230072969 + 3 ^ 40 * 2139989 * 2
def baseEnd_2139989 : Nat := 732561968223022011263917

theorem tailTrace_2139989 : CollatzResearch.WordTrace tailWord_2139989 prefixEnd_2139989 732561968223022011263917 := by
  unfold tailWord_2139989
  simp only [CollatzResearch.WordTrace]
  refine ⟨78051811044192808868879021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52034540696128539245919347 78051811044192808868879021)
  ·
    refine ⟨29269429141572303325829633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78051811044192808868879021 29269429141572303325829633)
    ·
      refine ⟨21952071856179227494372225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29269429141572303325829633 21952071856179227494372225)
      ·
        refine ⟨16464053892134420620779169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21952071856179227494372225 16464053892134420620779169)
        ·
          refine ⟨12348040419100815465584377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16464053892134420620779169 12348040419100815465584377)
          ·
            refine ⟨9261030314325611599188283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12348040419100815465584377 9261030314325611599188283)
            ·
              refine ⟨13891545471488417398782425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9261030314325611599188283 13891545471488417398782425)
              ·
                refine ⟨10418659103616313049086819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13891545471488417398782425 10418659103616313049086819)
                ·
                  refine ⟨15627988655424469573630229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10418659103616313049086819 15627988655424469573630229)
                  ·
                    refine ⟨732561968223022011263917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15627988655424469573630229 732561968223022011263917)
                    ·
                      rfl

theorem cell22_2139989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2139989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2139989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2139989 prefixEnd_2139989 := by exact prefixLift 2139989
  have htrace : WordTrace (prefixWord ++ tailWord_2139989) baseStart_2139989 baseEnd_2139989 := by
    simpa [prefixWord, tailWord_2139989, baseEnd_2139989] using wordTrace_append hprefix tailTrace_2139989
  have hstable : (prefixWord ++ tailWord_2139989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2139989).length < 2 ^ (prefixWord ++ tailWord_2139989).sum := by decide
  have hdescent : baseEnd_2139989 < baseStart_2139989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2139989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140042 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_2140042 : Nat := 118140960795 + 2140042 * 2 ^ 59
def prefixEnd_2140042 : Nat := 4983230072969 + 3 ^ 40 * 2140042 * 2
def baseEnd_2140042 : Nat := 732580111206147539688755

theorem tailTrace_2140042 : CollatzResearch.WordTrace tailWord_2140042 prefixEnd_2140042 732580111206147539688755 := by
  unfold tailWord_2140042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513436028250199730139595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52035829408667199280372253 19513436028250199730139595)
  ·
    refine ⟨29270154042375299595209393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19513436028250199730139595 29270154042375299595209393)
    ·
      refine ⟨21952615531781474696407045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29270154042375299595209393 21952615531781474696407045)
      ·
        refine ⟨4116115412209026505576321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21952615531781474696407045 4116115412209026505576321)
        ·
          refine ⟨3087086559156769879182241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116115412209026505576321 3087086559156769879182241)
          ·
            refine ⟨2315314919367577409386681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3087086559156769879182241 2315314919367577409386681)
            ·
              refine ⟨1736486189525683057040011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315314919367577409386681 1736486189525683057040011)
              ·
                refine ⟨2604729284288524585560017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736486189525683057040011 2604729284288524585560017)
                ·
                  refine ⟨1953546963216393439170013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2604729284288524585560017 1953546963216393439170013)
                  ·
                    refine ⟨732580111206147539688755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953546963216393439170013 732580111206147539688755)
                    ·
                      rfl

theorem cell22_2140042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_2140042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140042 prefixEnd_2140042 := by exact prefixLift 2140042
  have htrace : WordTrace (prefixWord ++ tailWord_2140042) baseStart_2140042 baseEnd_2140042 := by
    simpa [prefixWord, tailWord_2140042, baseEnd_2140042] using wordTrace_append hprefix tailTrace_2140042
  have hstable : (prefixWord ++ tailWord_2140042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140042).length < 2 ^ (prefixWord ++ tailWord_2140042).sum := by decide
  have hdescent : baseEnd_2140042 < baseStart_2140042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140064 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_2140064 : Nat := 118140960795 + 2140064 * 2 ^ 59
def prefixEnd_2140064 : Nat := 4983230072969 + 3 ^ 40 * 2140064 * 2
def baseEnd_2140064 : Nat := 732587642255746815638687

theorem tailTrace_2140064 : CollatzResearch.WordTrace tailWord_2140064 prefixEnd_2140064 732587642255746815638687 := by
  unfold tailWord_2140064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39027273259460548338929623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52036364345947397785239497 39027273259460548338929623)
  ·
    refine ⟨58540909889190822508394435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39027273259460548338929623 58540909889190822508394435)
    ·
      refine ⟨87811364833786233762591653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58540909889190822508394435 87811364833786233762591653)
      ·
        refine ⟨16464630906334918830485935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87811364833786233762591653 16464630906334918830485935)
        ·
          refine ⟨24696946359502378245728903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16464630906334918830485935 24696946359502378245728903)
          ·
            refine ⟨37045419539253567368593355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24696946359502378245728903 37045419539253567368593355)
            ·
              refine ⟨55568129308880351052890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37045419539253567368593355 55568129308880351052890033)
              ·
                refine ⟨41676096981660263289667525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55568129308880351052890033 41676096981660263289667525)
                ·
                  refine ⟨7814268184061299366812661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41676096981660263289667525 7814268184061299366812661)
                  ·
                    refine ⟨732587642255746815638687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7814268184061299366812661 732587642255746815638687)
                    ·
                      rfl

theorem cell22_2140064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_2140064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140064 prefixEnd_2140064 := by exact prefixLift 2140064
  have htrace : WordTrace (prefixWord ++ tailWord_2140064) baseStart_2140064 baseEnd_2140064 := by
    simpa [prefixWord, tailWord_2140064, baseEnd_2140064] using wordTrace_append hprefix tailTrace_2140064
  have hstable : (prefixWord ++ tailWord_2140064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140064).length < 2 ^ (prefixWord ++ tailWord_2140064).sum := by decide
  have hdescent : baseEnd_2140064 < baseStart_2140064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140158 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2140158 : Nat := 118140960795 + 2140158 * 2 ^ 59
def prefixEnd_2140158 : Nat := 4983230072969 + 3 ^ 40 * 2140158 * 2
def baseEnd_2140158 : Nat := 732619820376761903788399

theorem tailTrace_2140158 : CollatzResearch.WordTrace tailWord_2140158 prefixEnd_2140158 732619820376761903788399 := by
  unfold tailWord_2140158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757246872572568841472641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52038649987053700487854085 9757246872572568841472641)
  ·
    refine ⟨7317935154429426631104481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9757246872572568841472641 7317935154429426631104481)
    ·
      refine ⟨5488451365822069973328361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7317935154429426631104481 5488451365822069973328361)
      ·
        refine ⟨4116338524366552479996271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5488451365822069973328361 4116338524366552479996271)
        ·
          refine ⟨6174507786549828719994407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116338524366552479996271 6174507786549828719994407)
          ·
            refine ⟨9261761679824743079991611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6174507786549828719994407 9261761679824743079991611)
            ·
              refine ⟨13892642519737114619987417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9261761679824743079991611 13892642519737114619987417)
              ·
                refine ⟨10419481889802835964990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13892642519737114619987417 10419481889802835964990563)
                ·
                  refine ⟨15629222834704253947485845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10419481889802835964990563 15629222834704253947485845)
                  ·
                    refine ⟨732619820376761903788399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15629222834704253947485845 732619820376761903788399)
                    ·
                      rfl

theorem cell22_2140158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2140158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140158 prefixEnd_2140158 := by exact prefixLift 2140158
  have htrace : WordTrace (prefixWord ++ tailWord_2140158) baseStart_2140158 baseEnd_2140158 := by
    simpa [prefixWord, tailWord_2140158, baseEnd_2140158] using wordTrace_append hprefix tailTrace_2140158
  have hstable : (prefixWord ++ tailWord_2140158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140158).length < 2 ^ (prefixWord ++ tailWord_2140158).sum := by decide
  have hdescent : baseEnd_2140158 < baseStart_2140158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140293 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_2140293 : Nat := 118140960795 + 2140293 * 2 ^ 59
def prefixEnd_2140293 : Nat := 4983230072969 + 3 ^ 40 * 2140293 * 2
def baseEnd_2140293 : Nat := 732666033635666551662985

theorem tailTrace_2140293 : CollatzResearch.WordTrace tailWord_2140293 prefixEnd_2140293 732666033635666551662985 := by
  unfold tailWord_2140293
  simp only [CollatzResearch.WordTrace]
  refine ⟨78062898835091468787945533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52041932556727645858630355 78062898835091468787945533)
  ·
    refine ⟨29273587063159300795479575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78062898835091468787945533 29273587063159300795479575)
    ·
      refine ⟨43910380594738951193219363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29273587063159300795479575 43910380594738951193219363)
      ·
        refine ⟨65865570892108426789829045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43910380594738951193219363 65865570892108426789829045)
        ·
          refine ⟨6174897271135165011546473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65865570892108426789829045 6174897271135165011546473)
          ·
            refine ⟨4631172953351373758659855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174897271135165011546473 4631172953351373758659855)
            ·
              refine ⟨6946759430027060637989783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631172953351373758659855 6946759430027060637989783)
              ·
                refine ⟨10420139145040590956984675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6946759430027060637989783 10420139145040590956984675)
                ·
                  refine ⟨15630208717560886435477013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10420139145040590956984675 15630208717560886435477013)
                  ·
                    refine ⟨732666033635666551662985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15630208717560886435477013 732666033635666551662985)
                    ·
                      rfl

theorem cell22_2140293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_2140293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140293 prefixEnd_2140293 := by exact prefixLift 2140293
  have htrace : WordTrace (prefixWord ++ tailWord_2140293) baseStart_2140293 baseEnd_2140293 := by
    simpa [prefixWord, tailWord_2140293, baseEnd_2140293] using wordTrace_append hprefix tailTrace_2140293
  have hstable : (prefixWord ++ tailWord_2140293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140293).length < 2 ^ (prefixWord ++ tailWord_2140293).sum := by decide
  have hdescent : baseEnd_2140293 < baseStart_2140293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140336 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_2140336 : Nat := 118140960795 + 2140336 * 2 ^ 59
def prefixEnd_2140336 : Nat := 4983230072969 + 3 ^ 40 * 2140336 * 2
def baseEnd_2140336 : Nat := 244226917804809590945951

theorem tailTrace_2140336 : CollatzResearch.WordTrace tailWord_2140336 prefixEnd_2140336 244226917804809590945951 := by
  unfold tailWord_2140336
  simp only [CollatzResearch.WordTrace]
  refine ⟨39032233586967843565880431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52042978115957124754507241 39032233586967843565880431)
  ·
    refine ⟨58548350380451765348820647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39032233586967843565880431 58548350380451765348820647)
    ·
      refine ⟨87822525570677648023230971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58548350380451765348820647 87822525570677648023230971)
      ·
        refine ⟨131733788356016472034846457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87822525570677648023230971 131733788356016472034846457)
        ·
          refine ⟨98800341267012354026134843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131733788356016472034846457 98800341267012354026134843)
          ·
            refine ⟨148200511900518531039202265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98800341267012354026134843 148200511900518531039202265)
            ·
              refine ⟨111150383925388898279401699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148200511900518531039202265 111150383925388898279401699)
              ·
                refine ⟨166725575888083347419102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111150383925388898279401699 166725575888083347419102549)
                ·
                  refine ⟨244226917804809590945951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 166725575888083347419102549 244226917804809590945951)
                  ·
                    rfl

theorem cell22_2140336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_2140336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140336 prefixEnd_2140336 := by exact prefixLift 2140336
  have htrace : WordTrace (prefixWord ++ tailWord_2140336) baseStart_2140336 baseEnd_2140336 := by
    simpa [prefixWord, tailWord_2140336, baseEnd_2140336] using wordTrace_append hprefix tailTrace_2140336
  have hstable : (prefixWord ++ tailWord_2140336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140336).length < 2 ^ (prefixWord ++ tailWord_2140336).sum := by decide
  have hdescent : baseEnd_2140336 < baseStart_2140336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140357 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_2140357 : Nat := 118140960795 + 2140357 * 2 ^ 59
def prefixEnd_2140357 : Nat := 4983230072969 + 3 ^ 40 * 2140357 * 2
def baseEnd_2140357 : Nat := 732687942143591718062789

theorem tailTrace_2140357 : CollatzResearch.WordTrace tailWord_2140357 prefixEnd_2140357 732687942143591718062789 := by
  unfold tailWord_2140357
  simp only [CollatzResearch.WordTrace]
  refine ⟨78065233106859607718275325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52043488737906405145516883 78065233106859607718275325)
  ·
    refine ⟨29274462415072352894353247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78065233106859607718275325 29274462415072352894353247)
    ·
      refine ⟨43911693622608529341529871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29274462415072352894353247 43911693622608529341529871)
      ·
        refine ⟨65867540433912794012294807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43911693622608529341529871 65867540433912794012294807)
        ·
          refine ⟨98801310650869191018442211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65867540433912794012294807 98801310650869191018442211)
          ·
            refine ⟨148201965976303786527663317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98801310650869191018442211 148201965976303786527663317)
            ·
              refine ⟨3473483577569619996742109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148201965976303786527663317 3473483577569619996742109)
              ·
                refine ⟨1302556341588607498778291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3473483577569619996742109 1302556341588607498778291)
                ·
                  refine ⟨1953834512382911248167437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302556341588607498778291 1953834512382911248167437)
                  ·
                    refine ⟨732687942143591718062789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953834512382911248167437 732687942143591718062789)
                    ·
                      rfl

theorem cell22_2140357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_2140357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140357 prefixEnd_2140357 := by exact prefixLift 2140357
  have htrace : WordTrace (prefixWord ++ tailWord_2140357) baseStart_2140357 baseEnd_2140357 := by
    simpa [prefixWord, tailWord_2140357, baseEnd_2140357] using wordTrace_append hprefix tailTrace_2140357
  have hstable : (prefixWord ++ tailWord_2140357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140357).length < 2 ^ (prefixWord ++ tailWord_2140357).sum := by decide
  have hdescent : baseEnd_2140357 < baseStart_2140357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140374 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2140374 : Nat := 118140960795 + 2140374 * 2 ^ 59
def prefixEnd_2140374 : Nat := 4983230072969 + 3 ^ 40 * 2140374 * 2
def baseEnd_2140374 : Nat := 732693761591009340387737

theorem tailTrace_2140374 : CollatzResearch.WordTrace tailWord_2140374 prefixEnd_2140374 732693761591009340387737 := by
  unfold tailWord_2140374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879115821737376226352761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52043902098532013081096117 4879115821737376226352761)
  ·
    refine ⟨3659336866303032169764571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4879115821737376226352761 3659336866303032169764571)
    ·
      refine ⟨5489005299454548254646857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3659336866303032169764571 5489005299454548254646857)
      ·
        refine ⟨4116753974590911190985143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5489005299454548254646857 4116753974590911190985143)
        ·
          refine ⟨6175130961886366786477715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116753974590911190985143 6175130961886366786477715)
          ·
            refine ⟨9262696442829550179716573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175130961886366786477715 9262696442829550179716573)
            ·
              refine ⟨3473511166061081317393715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9262696442829550179716573 3473511166061081317393715)
              ·
                refine ⟨5210266749091621976090573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473511166061081317393715 5210266749091621976090573)
                ·
                  refine ⟨1953850030909358241033965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210266749091621976090573 1953850030909358241033965)
                  ·
                    refine ⟨732693761591009340387737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953850030909358241033965 732693761591009340387737)
                    ·
                      rfl

theorem cell22_2140374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2140374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140374 prefixEnd_2140374 := by exact prefixLift 2140374
  have htrace : WordTrace (prefixWord ++ tailWord_2140374) baseStart_2140374 baseEnd_2140374 := by
    simpa [prefixWord, tailWord_2140374, baseEnd_2140374] using wordTrace_append hprefix tailTrace_2140374
  have hstable : (prefixWord ++ tailWord_2140374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140374).length < 2 ^ (prefixWord ++ tailWord_2140374).sum := by decide
  have hdescent : baseEnd_2140374 < baseStart_2140374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140383 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_2140383 : Nat := 118140960795 + 2140383 * 2 ^ 59
def prefixEnd_2140383 : Nat := 4983230072969 + 3 ^ 40 * 2140383 * 2
def baseEnd_2140383 : Nat := 732696842474936316912709

theorem tailTrace_2140383 : CollatzResearch.WordTrace tailWord_2140383 prefixEnd_2140383 732696842474936316912709 := by
  unfold tailWord_2140383
  simp only [CollatzResearch.WordTrace]
  refine ⟨78066181404765414158721803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52044120936510276105814535 78066181404765414158721803)
  ·
    refine ⟨117099272107148121238082705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78066181404765414158721803 117099272107148121238082705)
    ·
      refine ⟨87824454080361090928562029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117099272107148121238082705 87824454080361090928562029)
      ·
        refine ⟨32934170280135409098210761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87824454080361090928562029 32934170280135409098210761)
        ·
          refine ⟨24700627710101556823658071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32934170280135409098210761 24700627710101556823658071)
          ·
            refine ⟨37050941565152335235487107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24700627710101556823658071 37050941565152335235487107)
            ·
              refine ⟨55576412347728502853230661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37050941565152335235487107 55576412347728502853230661)
              ·
                refine ⟨10420577315199094284980749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55576412347728502853230661 10420577315199094284980749)
                ·
                  refine ⟨3907716493199660356867781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10420577315199094284980749 3907716493199660356867781)
                  ·
                    refine ⟨732696842474936316912709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907716493199660356867781 732696842474936316912709)
                    ·
                      rfl

theorem cell22_2140383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_2140383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140383 prefixEnd_2140383 := by exact prefixLift 2140383
  have htrace : WordTrace (prefixWord ++ tailWord_2140383) baseStart_2140383 baseEnd_2140383 := by
    simpa [prefixWord, tailWord_2140383, baseEnd_2140383] using wordTrace_append hprefix tailTrace_2140383
  have hstable : (prefixWord ++ tailWord_2140383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140383).length < 2 ^ (prefixWord ++ tailWord_2140383).sum := by decide
  have hdescent : baseEnd_2140383 < baseStart_2140383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140387 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 5]
def baseStart_2140387 : Nat := 118140960795 + 2140387 * 2 ^ 59
def prefixEnd_2140387 : Nat := 4983230072969 + 3 ^ 40 * 2140387 * 2
def baseEnd_2140387 : Nat := 244232737252227213270899

theorem tailTrace_2140387 : CollatzResearch.WordTrace tailWord_2140387 prefixEnd_2140387 244232737252227213270899 := by
  unfold tailWord_2140387
  simp only [CollatzResearch.WordTrace]
  refine ⟨78066327296750922841867415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52044218197833948561244943 78066327296750922841867415)
  ·
    refine ⟨117099490945126384262801123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78066327296750922841867415 117099490945126384262801123)
    ·
      refine ⟨175649236417689576394201685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117099490945126384262801123 175649236417689576394201685)
      ·
        refine ⟨2058389489269799723369551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 175649236417689576394201685 2058389489269799723369551)
        ·
          refine ⟨3087584233904699585054327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058389489269799723369551 3087584233904699585054327)
          ·
            refine ⟨4631376350857049377581491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087584233904699585054327 4631376350857049377581491)
            ·
              refine ⟨6947064526285574066372237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631376350857049377581491 6947064526285574066372237)
              ·
                refine ⟨2605149197357090274889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947064526285574066372237 2605149197357090274889589)
                ·
                  refine ⟨244232737252227213270899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605149197357090274889589 244232737252227213270899)
                  ·
                    rfl

theorem cell22_2140387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].length) (baseStart_2140387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140387 prefixEnd_2140387 := by exact prefixLift 2140387
  have htrace : WordTrace (prefixWord ++ tailWord_2140387) baseStart_2140387 baseEnd_2140387 := by
    simpa [prefixWord, tailWord_2140387, baseEnd_2140387] using wordTrace_append hprefix tailTrace_2140387
  have hstable : (prefixWord ++ tailWord_2140387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140387).length < 2 ^ (prefixWord ++ tailWord_2140387).sum := by decide
  have hdescent : baseEnd_2140387 < baseStart_2140387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140398 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2140398 : Nat := 118140960795 + 2140398 * 2 ^ 59
def prefixEnd_2140398 : Nat := 4983230072969 + 3 ^ 40 * 2140398 * 2
def baseEnd_2140398 : Nat := 244233992427160425929221

theorem tailTrace_2140398 : CollatzResearch.WordTrace tailWord_2140398 prefixEnd_2140398 244233992427160425929221 := by
  unfold tailWord_2140398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9758341062463883965064731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52044485666474047813678565 9758341062463883965064731)
  ·
    refine ⟨14637511593695825947597097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9758341062463883965064731 14637511593695825947597097)
    ·
      refine ⟨10978133695271869460697823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14637511593695825947597097 10978133695271869460697823)
      ·
        refine ⟨16467200542907804191046735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978133695271869460697823 16467200542907804191046735)
        ·
          refine ⟨24700800814361706286570103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16467200542907804191046735 24700800814361706286570103)
          ·
            refine ⟨37051201221542559429855155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24700800814361706286570103 37051201221542559429855155)
            ·
              refine ⟨55576801832313839144782733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37051201221542559429855155 55576801832313839144782733)
              ·
                refine ⟨20841300687117689679293525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55576801832313839144782733 20841300687117689679293525)
                ·
                  refine ⟨244233992427160425929221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20841300687117689679293525 244233992427160425929221)
                  ·
                    rfl

theorem cell22_2140398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2140398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140398 prefixEnd_2140398 := by exact prefixLift 2140398
  have htrace : WordTrace (prefixWord ++ tailWord_2140398) baseStart_2140398 baseEnd_2140398 := by
    simpa [prefixWord, tailWord_2140398, baseEnd_2140398] using wordTrace_append hprefix tailTrace_2140398
  have hstable : (prefixWord ++ tailWord_2140398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140398).length < 2 ^ (prefixWord ++ tailWord_2140398).sum := by decide
  have hdescent : baseEnd_2140398 < baseStart_2140398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140415 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 4]
def baseStart_2140415 : Nat := 118140960795 + 2140415 * 2 ^ 59
def prefixEnd_2140415 : Nat := 4983230072969 + 3 ^ 40 * 2140415 * 2
def baseEnd_2140415 : Nat := 244235932242966300037537

theorem tailTrace_2140415 : CollatzResearch.WordTrace tailWord_2140415 prefixEnd_2140415 244235932242966300037537 := by
  unfold tailWord_2140415
  simp only [CollatzResearch.WordTrace]
  refine ⟨78067348540649483623886699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52044899027099655749257799 78067348540649483623886699)
  ·
    refine ⟨117101022810974225435830049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78067348540649483623886699 117101022810974225435830049)
    ·
      refine ⟨87825767108230669076872537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117101022810974225435830049 87825767108230669076872537)
      ·
        refine ⟨65869325331173001807654403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87825767108230669076872537 65869325331173001807654403)
        ·
          refine ⟨98803987996759502711481605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65869325331173001807654403 98803987996759502711481605)
          ·
            refine ⟨18525747749392406758402801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98803987996759502711481605 18525747749392406758402801)
            ·
              refine ⟨13894310812044305068802101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18525747749392406758402801 13894310812044305068802101)
              ·
                refine ⟨1302591638629153600200197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13894310812044305068802101 1302591638629153600200197)
                ·
                  refine ⟨244235932242966300037537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302591638629153600200197 244235932242966300037537)
                  ·
                    rfl

theorem cell22_2140415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 4].length) (baseStart_2140415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140415 prefixEnd_2140415 := by exact prefixLift 2140415
  have htrace : WordTrace (prefixWord ++ tailWord_2140415) baseStart_2140415 baseEnd_2140415 := by
    simpa [prefixWord, tailWord_2140415, baseEnd_2140415] using wordTrace_append hprefix tailTrace_2140415
  have hstable : (prefixWord ++ tailWord_2140415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140415).length < 2 ^ (prefixWord ++ tailWord_2140415).sum := by decide
  have hdescent : baseEnd_2140415 < baseStart_2140415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140417 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2140417 : Nat := 118140960795 + 2140417 * 2 ^ 59
def prefixEnd_2140417 : Nat := 4983230072969 + 3 ^ 40 * 2140417 * 2
def baseEnd_2140417 : Nat := 732708481369771561562605

theorem tailTrace_2140417 : CollatzResearch.WordTrace tailWord_2140417 prefixEnd_2140417 732708481369771561562605 := by
  unfold tailWord_2140417
  simp only [CollatzResearch.WordTrace]
  refine ⟨78067421486642237965459505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52044947657761491976973003 78067421486642237965459505)
  ·
    refine ⟨58550566114981678474094629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78067421486642237965459505 58550566114981678474094629)
    ·
      refine ⟨10978231146559064713892743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58550566114981678474094629 10978231146559064713892743)
      ·
        refine ⟨16467346719838597070839115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978231146559064713892743 16467346719838597070839115)
        ·
          refine ⟨24701020079757895606258673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16467346719838597070839115 24701020079757895606258673)
          ·
            refine ⟨18525765059818421704694005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24701020079757895606258673 18525765059818421704694005)
            ·
              refine ⟨1736790474357977034815063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18525765059818421704694005 1736790474357977034815063)
              ·
                refine ⟨2605185711536965552222595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1736790474357977034815063 2605185711536965552222595)
                ·
                  refine ⟨3907778567305448328333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605185711536965552222595 3907778567305448328333893)
                  ·
                    refine ⟨732708481369771561562605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3907778567305448328333893 732708481369771561562605)
                    ·
                      rfl

theorem cell22_2140417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2140417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140417 prefixEnd_2140417 := by exact prefixLift 2140417
  have htrace : WordTrace (prefixWord ++ tailWord_2140417) baseStart_2140417 baseEnd_2140417 := by
    simpa [prefixWord, tailWord_2140417, baseEnd_2140417] using wordTrace_append hprefix tailTrace_2140417
  have hstable : (prefixWord ++ tailWord_2140417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140417).length < 2 ^ (prefixWord ++ tailWord_2140417).sum := by decide
  have hdescent : baseEnd_2140417 < baseStart_2140417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140443 : List Nat := [1, 1, 1, 1, 1, 1, 9, 7]
def baseStart_2140443 : Nat := 118140960795 + 2140443 * 2 ^ 59
def prefixEnd_2140443 : Nat := 4983230072969 + 3 ^ 40 * 2140443 * 2
def baseEnd_2140443 : Nat := 81413042411235128934725

theorem tailTrace_2140443 : CollatzResearch.WordTrace tailWord_2140443 prefixEnd_2140443 81413042411235128934725 := by
  unfold tailWord_2140443
  simp only [CollatzResearch.WordTrace]
  refine ⟨78068369784548044405905983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52045579856365362937270655 78068369784548044405905983)
  ·
    refine ⟨117102554676822066608858975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78068369784548044405905983 117102554676822066608858975)
    ·
      refine ⟨175653832015233099913288463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117102554676822066608858975 175653832015233099913288463)
      ·
        refine ⟨263480748022849649869932695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175653832015233099913288463 263480748022849649869932695)
        ·
          refine ⟨395221122034274474804899043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263480748022849649869932695 395221122034274474804899043)
          ·
            refine ⟨592831683051411712207348565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395221122034274474804899043 592831683051411712207348565)
            ·
              refine ⟨3473623142879365501214933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 592831683051411712207348565 3473623142879365501214933)
              ·
                refine ⟨81413042411235128934725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3473623142879365501214933 81413042411235128934725)
                ·
                  rfl

theorem cell22_2140443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 7].length) (baseStart_2140443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140443 prefixEnd_2140443 := by exact prefixLift 2140443
  have htrace : WordTrace (prefixWord ++ tailWord_2140443) baseStart_2140443 baseEnd_2140443 := by
    simpa [prefixWord, tailWord_2140443, baseEnd_2140443] using wordTrace_append hprefix tailTrace_2140443
  have hstable : (prefixWord ++ tailWord_2140443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140443).length < 2 ^ (prefixWord ++ tailWord_2140443).sum := by decide
  have hdescent : baseEnd_2140443 < baseStart_2140443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140447 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 2, 3]
def baseStart_2140447 : Nat := 118140960795 + 2140447 * 2 ^ 59
def prefixEnd_2140447 : Nat := 4983230072969 + 3 ^ 40 * 2140447 * 2
def baseEnd_2140447 : Nat := 732718750982861483312513

theorem tailTrace_2140447 : CollatzResearch.WordTrace tailWord_2140447 prefixEnd_2140447 732718750982861483312513 := by
  unfold tailWord_2140447
  simp only [CollatzResearch.WordTrace]
  refine ⟨78068515676533553089051595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52045677117689035392701063 78068515676533553089051595)
  ·
    refine ⟨117102773514800329633577393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78068515676533553089051595 117102773514800329633577393)
    ·
      refine ⟨87827080136100247225183045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117102773514800329633577393 87827080136100247225183045)
      ·
        refine ⟨16467577525518796354721821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87827080136100247225183045 16467577525518796354721821)
        ·
          refine ⟨6175341572069548633020683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16467577525518796354721821 6175341572069548633020683)
          ·
            refine ⟨9263012358104322949531025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175341572069548633020683 9263012358104322949531025)
            ·
              refine ⟨6947259268578242212148269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9263012358104322949531025 6947259268578242212148269)
              ·
                refine ⟨2605222225716840829555601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6947259268578242212148269 2605222225716840829555601)
                ·
                  refine ⟨1953916669287630622166701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605222225716840829555601 1953916669287630622166701)
                  ·
                    refine ⟨732718750982861483312513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953916669287630622166701 732718750982861483312513)
                    ·
                      rfl

theorem cell22_2140447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_2140447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140447 prefixEnd_2140447 := by exact prefixLift 2140447
  have htrace : WordTrace (prefixWord ++ tailWord_2140447) baseStart_2140447 baseEnd_2140447 := by
    simpa [prefixWord, tailWord_2140447, baseEnd_2140447] using wordTrace_append hprefix tailTrace_2140447
  have hstable : (prefixWord ++ tailWord_2140447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140447).length < 2 ^ (prefixWord ++ tailWord_2140447).sum := by decide
  have hdescent : baseEnd_2140447 < baseStart_2140447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140481 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2140481 : Nat := 118140960795 + 2140481 * 2 ^ 59
def prefixEnd_2140481 : Nat := 4983230072969 + 3 ^ 40 * 2140481 * 2
def baseEnd_2140481 : Nat := 732730389877696727962409

theorem tailTrace_2140481 : CollatzResearch.WordTrace tailWord_2140481 prefixEnd_2140481 732730389877696727962409 := by
  unfold tailWord_2140481
  simp only [CollatzResearch.WordTrace]
  refine ⟨78069755758410376895789297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52046503838940251263859531 78069755758410376895789297)
  ·
    refine ⟨58552316818807782671841973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78069755758410376895789297 58552316818807782671841973)
    ·
      refine ⟨5489279701763229625485185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58552316818807782671841973 5489279701763229625485185)
      ·
        refine ⟨4116959776322422219113889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5489279701763229625485185 4116959776322422219113889)
        ·
          refine ⟨3087719832241816664335417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116959776322422219113889 3087719832241816664335417)
          ·
            refine ⟨2315789874181362498251563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3087719832241816664335417 2315789874181362498251563)
            ·
              refine ⟨3473684811272043747377345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315789874181362498251563 3473684811272043747377345)
              ·
                refine ⟨2605263608454032810533009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473684811272043747377345 2605263608454032810533009)
                ·
                  refine ⟨1953947706340524607899757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605263608454032810533009 1953947706340524607899757)
                  ·
                    refine ⟨732730389877696727962409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953947706340524607899757 732730389877696727962409)
                    ·
                      rfl

theorem cell22_2140481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2140481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140481 prefixEnd_2140481 := by exact prefixLift 2140481
  have htrace : WordTrace (prefixWord ++ tailWord_2140481) baseStart_2140481 baseEnd_2140481 := by
    simpa [prefixWord, tailWord_2140481, baseEnd_2140481] using wordTrace_append hprefix tailTrace_2140481
  have hstable : (prefixWord ++ tailWord_2140481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140481).length < 2 ^ (prefixWord ++ tailWord_2140481).sum := by decide
  have hdescent : baseEnd_2140481 < baseStart_2140481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140492 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_2140492 : Nat := 118140960795 + 2140492 * 2 ^ 59
def prefixEnd_2140492 : Nat := 4983230072969 + 3 ^ 40 * 2140492 * 2
def baseEnd_2140492 : Nat := 732734155402496365937375

theorem tailTrace_2140492 : CollatzResearch.WordTrace tailWord_2140492 prefixEnd_2140492 732734155402496365937375 := by
  unfold tailWord_2140492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39035078480685262887219865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52046771307580350516293153 39035078480685262887219865)
  ·
    refine ⟨29276308860513947165414899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39035078480685262887219865 29276308860513947165414899)
    ·
      refine ⟨43914463290770920748122349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29276308860513947165414899 43914463290770920748122349)
      ·
        refine ⟨16467923734039095280545881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43914463290770920748122349 16467923734039095280545881)
        ·
          refine ⟨12350942800529321460409411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16467923734039095280545881 12350942800529321460409411)
          ·
            refine ⟨18526414200793982190614117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12350942800529321460409411 18526414200793982190614117)
            ·
              refine ⟨3473702662648871660740147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18526414200793982190614117 3473702662648871660740147)
              ·
                refine ⟨5210553993973307491110221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3473702662648871660740147 5210553993973307491110221)
                ·
                  refine ⟨1953957747739990309166333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5210553993973307491110221 1953957747739990309166333)
                  ·
                    refine ⟨732734155402496365937375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1953957747739990309166333 732734155402496365937375)
                    ·
                      rfl

theorem cell22_2140492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_2140492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140492 prefixEnd_2140492 := by exact prefixLift 2140492
  have htrace : WordTrace (prefixWord ++ tailWord_2140492) baseStart_2140492 baseEnd_2140492 := by
    simpa [prefixWord, tailWord_2140492, baseEnd_2140492] using wordTrace_append hprefix tailTrace_2140492
  have hstable : (prefixWord ++ tailWord_2140492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140492).length < 2 ^ (prefixWord ++ tailWord_2140492).sum := by decide
  have hdescent : baseEnd_2140492 < baseStart_2140492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140565 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2140565 : Nat := 118140960795 + 2140565 * 2 ^ 59
def prefixEnd_2140565 : Nat := 4983230072969 + 3 ^ 40 * 2140565 * 2
def baseEnd_2140565 : Nat := 732759144794348508862151

theorem tailTrace_2140565 : CollatzResearch.WordTrace tailWord_2140565 prefixEnd_2140565 732759144794348508862151 := by
  unfold tailWord_2140565
  simp only [CollatzResearch.WordTrace]
  refine ⟨78072819490106059241847149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52048546326737372827898099 78072819490106059241847149)
  ·
    refine ⟨29277307308789772215692681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78072819490106059241847149 29277307308789772215692681)
    ·
      refine ⟨21957980481592329161769511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29277307308789772215692681 21957980481592329161769511)
      ·
        refine ⟨32936970722388493742654267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21957980481592329161769511 32936970722388493742654267)
        ·
          refine ⟨49405456083582740613981401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32936970722388493742654267 49405456083582740613981401)
          ·
            refine ⟨37054092062687055460486051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49405456083582740613981401 37054092062687055460486051)
            ·
              refine ⟨55581138094030583190729077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37054092062687055460486051 55581138094030583190729077)
              ·
                refine ⟨5210731696315367174130851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55581138094030583190729077 5210731696315367174130851)
                ·
                  refine ⟨7816097544473050761196277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5210731696315367174130851 7816097544473050761196277)
                  ·
                    refine ⟨732759144794348508862151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7816097544473050761196277 732759144794348508862151)
                    ·
                      rfl

theorem cell22_2140565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2140565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140565 prefixEnd_2140565 := by exact prefixLift 2140565
  have htrace : WordTrace (prefixWord ++ tailWord_2140565) baseStart_2140565 baseEnd_2140565 := by
    simpa [prefixWord, tailWord_2140565, baseEnd_2140565] using wordTrace_append hprefix tailTrace_2140565
  have hstable : (prefixWord ++ tailWord_2140565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140565).length < 2 ^ (prefixWord ++ tailWord_2140565).sum := by decide
  have hdescent : baseEnd_2140565 < baseStart_2140565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140580 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_2140580 : Nat := 118140960795 + 2140580 * 2 ^ 59
def prefixEnd_2140580 : Nat := 4983230072969 + 3 ^ 40 * 2140580 * 2
def baseEnd_2140580 : Nat := 732764279600893469737105

theorem tailTrace_2140580 : CollatzResearch.WordTrace tailWord_2140580 prefixEnd_2140580 732764279600893469737105 := by
  unfold tailWord_2140580
  simp only [CollatzResearch.WordTrace]
  refine ⟨39036683292525858401821597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52048911056701144535762129 39036683292525858401821597)
  ·
    refine ⟨14638756234697196900683099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39036683292525858401821597 14638756234697196900683099)
    ·
      refine ⟨21958134352045795351024649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14638756234697196900683099 21958134352045795351024649)
      ·
        refine ⟨16468600764034346513268487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21958134352045795351024649 16468600764034346513268487)
        ·
          refine ⟨24702901146051519769902731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16468600764034346513268487 24702901146051519769902731)
          ·
            refine ⟨37054351719077279654854097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24702901146051519769902731 37054351719077279654854097)
            ·
              refine ⟨27790763789307959741140573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37054351719077279654854097 27790763789307959741140573)
              ·
                refine ⟨10421536420990484902927715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27790763789307959741140573 10421536420990484902927715)
                ·
                  refine ⟨15632304631485727354391573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10421536420990484902927715 15632304631485727354391573)
                  ·
                    refine ⟨732764279600893469737105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15632304631485727354391573 732764279600893469737105)
                    ·
                      rfl

theorem cell22_2140580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_2140580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140580 prefixEnd_2140580 := by exact prefixLift 2140580
  have htrace : WordTrace (prefixWord ++ tailWord_2140580) baseStart_2140580 baseEnd_2140580 := by
    simpa [prefixWord, tailWord_2140580, baseEnd_2140580] using wordTrace_append hprefix tailTrace_2140580
  have hstable : (prefixWord ++ tailWord_2140580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140580).length < 2 ^ (prefixWord ++ tailWord_2140580).sum := by decide
  have hdescent : baseEnd_2140580 < baseStart_2140580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140599 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 2, 3]
def baseStart_2140599 : Nat := 118140960795 + 2140599 * 2 ^ 59
def prefixEnd_2140599 : Nat := 4983230072969 + 3 ^ 40 * 2140599 * 2
def baseEnd_2140599 : Nat := 732770783689183753512047

theorem tailTrace_2140599 : CollatzResearch.WordTrace tailWord_2140599 prefixEnd_2140599 732770783689183753512047 := by
  unfold tailWord_2140599
  simp only [CollatzResearch.WordTrace]
  refine ⟨78074059571982883048584851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52049373047988588699056567 78074059571982883048584851)
  ·
    refine ⟨117111089357974324572877277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78074059571982883048584851 117111089357974324572877277)
    ·
      refine ⟨43916658509240371714828979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117111089357974324572877277 43916658509240371714828979)
      ·
        refine ⟨65874987763860557572243469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43916658509240371714828979 65874987763860557572243469)
        ·
          refine ⟨24703120411447709089591301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65874987763860557572243469 24703120411447709089591301)
          ·
            refine ⟨4631835077146445454298369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24703120411447709089591301 4631835077146445454298369)
            ·
              refine ⟨3473876307859834090723777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631835077146445454298369 3473876307859834090723777)
              ·
                refine ⟨2605407230894875568042833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473876307859834090723777 2605407230894875568042833)
                ·
                  refine ⟨1954055423171156676032125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2605407230894875568042833 1954055423171156676032125)
                  ·
                    refine ⟨732770783689183753512047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954055423171156676032125 732770783689183753512047)
                    ·
                      rfl

theorem cell22_2140599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_2140599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140599 prefixEnd_2140599 := by exact prefixLift 2140599
  have htrace : WordTrace (prefixWord ++ tailWord_2140599) baseStart_2140599 baseEnd_2140599 := by
    simpa [prefixWord, tailWord_2140599, baseEnd_2140599] using wordTrace_append hprefix tailTrace_2140599
  have hstable : (prefixWord ++ tailWord_2140599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140599).length < 2 ^ (prefixWord ++ tailWord_2140599).sum := by decide
  have hdescent : baseEnd_2140599 < baseStart_2140599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140601 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 4]
def baseStart_2140601 : Nat := 118140960795 + 2140601 * 2 ^ 59
def prefixEnd_2140601 : Nat := 4983230072969 + 3 ^ 40 * 2140601 * 2
def baseEnd_2140601 : Nat := 244257156110018804987347

theorem tailTrace_2140601 : CollatzResearch.WordTrace tailWord_2140601 prefixEnd_2140601 244257156110018804987347 := by
  unfold tailWord_2140601
  simp only [CollatzResearch.WordTrace]
  refine ⟨78074132517975637390157657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52049421678650424926771771 78074132517975637390157657)
  ·
    refine ⟨58555599388481728042618243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78074132517975637390157657 58555599388481728042618243)
    ·
      refine ⟨87833399082722592063927365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58555599388481728042618243 87833399082722592063927365)
      ·
        refine ⟨16468762328010486011986381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87833399082722592063927365 16468762328010486011986381)
        ·
          refine ⟨6175785873003932254494893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16468762328010486011986381 6175785873003932254494893)
          ·
            refine ⟨2315919702376474595435585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6175785873003932254494893 2315919702376474595435585)
            ·
              refine ⟨1736939776782355946576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315919702376474595435585 1736939776782355946576689)
              ·
                refine ⟨1302704832586766959932517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736939776782355946576689 1302704832586766959932517)
                ·
                  refine ⟨244257156110018804987347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302704832586766959932517 244257156110018804987347)
                  ·
                    rfl

theorem cell22_2140601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_2140601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140601 prefixEnd_2140601 := by exact prefixLift 2140601
  have htrace : WordTrace (prefixWord ++ tailWord_2140601) baseStart_2140601 baseEnd_2140601 := by
    simpa [prefixWord, tailWord_2140601, baseEnd_2140601] using wordTrace_append hprefix tailTrace_2140601
  have hstable : (prefixWord ++ tailWord_2140601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140601).length < 2 ^ (prefixWord ++ tailWord_2140601).sum := by decide
  have hdescent : baseEnd_2140601 < baseStart_2140601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140640 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_2140640 : Nat := 118140960795 + 2140640 * 2 ^ 59
def prefixEnd_2140640 : Nat := 4983230072969 + 3 ^ 40 * 2140640 * 2
def baseEnd_2140640 : Nat := 244261606275691104412307

theorem tailTrace_2140640 : CollatzResearch.WordTrace tailWord_2140640 prefixEnd_2140640 244261606275691104412307 := by
  unfold tailWord_2140640
  simp only [CollatzResearch.WordTrace]
  refine ⟨39037777482417173525413687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52050369976556231367218249 39037777482417173525413687)
  ·
    refine ⟨58556666223625760288120531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39037777482417173525413687 58556666223625760288120531)
    ·
      refine ⟨87834999335438640432180797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58556666223625760288120531 87834999335438640432180797)
      ·
        refine ⟨32938124750789490162067799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87834999335438640432180797 32938124750789490162067799)
        ·
          refine ⟨49407187126184235243101699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32938124750789490162067799 49407187126184235243101699)
          ·
            refine ⟨74110780689276352864652549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49407187126184235243101699 74110780689276352864652549)
            ·
              refine ⟨13895771379239316162122353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74110780689276352864652549 13895771379239316162122353)
              ·
                refine ⟨10421828534429487121591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13895771379239316162122353 10421828534429487121591765)
                ·
                  refine ⟨244261606275691104412307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10421828534429487121591765 244261606275691104412307)
                  ·
                    rfl

theorem cell22_2140640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_2140640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140640 prefixEnd_2140640 := by exact prefixLift 2140640
  have htrace : WordTrace (prefixWord ++ tailWord_2140640) baseStart_2140640 baseEnd_2140640 := by
    simpa [prefixWord, tailWord_2140640, baseEnd_2140640] using wordTrace_append hprefix tailTrace_2140640
  have hstable : (prefixWord ++ tailWord_2140640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140640).length < 2 ^ (prefixWord ++ tailWord_2140640).sum := by decide
  have hdescent : baseEnd_2140640 < baseStart_2140640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140687 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 1, 4]
def baseStart_2140687 : Nat := 118140960795 + 2140687 * 2 ^ 59
def prefixEnd_2140687 : Nat := 4983230072969 + 3 ^ 40 * 2140687 * 2
def baseEnd_2140687 : Nat := 732800907887580857311777

theorem tailTrace_2140687 : CollatzResearch.WordTrace tailWord_2140687 prefixEnd_2140687 732800907887580857311777 := by
  unfold tailWord_2140687
  simp only [CollatzResearch.WordTrace]
  refine ⟨78077269195664074077788315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52051512797109382718525543 78077269195664074077788315)
  ·
    refine ⟨117115903793496111116682473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78077269195664074077788315 117115903793496111116682473)
    ·
      refine ⟨87836927845122083337511855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117115903793496111116682473 87836927845122083337511855)
      ·
        refine ⟨131755391767683125006267783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87836927845122083337511855 131755391767683125006267783)
        ·
          refine ⟨197633087651524687509401675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131755391767683125006267783 197633087651524687509401675)
          ·
            refine ⟨296449631477287031264102513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197633087651524687509401675 296449631477287031264102513)
            ·
              refine ⟨222337223607965273448076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296449631477287031264102513 222337223607965273448076885)
              ·
                refine ⟨2605514339155843048219651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 222337223607965273448076885 2605514339155843048219651)
                ·
                  refine ⟨3908271508733764572329477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605514339155843048219651 3908271508733764572329477)
                  ·
                    refine ⟨732800907887580857311777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908271508733764572329477 732800907887580857311777)
                    ·
                      rfl

theorem cell22_2140687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_2140687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140687 prefixEnd_2140687 := by exact prefixLift 2140687
  have htrace : WordTrace (prefixWord ++ tailWord_2140687) baseStart_2140687 baseEnd_2140687 := by
    simpa [prefixWord, tailWord_2140687, baseEnd_2140687] using wordTrace_append hprefix tailTrace_2140687
  have hstable : (prefixWord ++ tailWord_2140687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140687).length < 2 ^ (prefixWord ++ tailWord_2140687).sum := by decide
  have hdescent : baseEnd_2140687 < baseStart_2140687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140695 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 1, 3]
def baseStart_2140695 : Nat := 118140960795 + 2140695 * 2 ^ 59
def prefixEnd_2140695 : Nat := 4983230072969 + 3 ^ 40 * 2140695 * 2
def baseEnd_2140695 : Nat := 732803646451071503111753

theorem tailTrace_2140695 : CollatzResearch.WordTrace tailWord_2140695 prefixEnd_2140695 732803646451071503111753 := by
  unfold tailWord_2140695
  simp only [CollatzResearch.WordTrace]
  refine ⟨78077560979635091444079539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52051707319756727629386359 78077560979635091444079539)
  ·
    refine ⟨117116341469452637166119309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78077560979635091444079539 117116341469452637166119309)
    ·
      refine ⟨43918628051044738937294741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117116341469452637166119309 43918628051044738937294741)
      ·
        refine ⟨2058685689892722137685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43918628051044738937294741 2058685689892722137685691)
        ·
          refine ⟨3088028534839083206528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058685689892722137685691 3088028534839083206528537)
          ·
            refine ⟨2316021401129312404896403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3088028534839083206528537 2316021401129312404896403)
            ·
              refine ⟨3474032101693968607344605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316021401129312404896403 3474032101693968607344605)
              ·
                refine ⟨1302762038135238227754227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3474032101693968607344605 1302762038135238227754227)
                ·
                  refine ⟨1954143057202857341631341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302762038135238227754227 1954143057202857341631341)
                  ·
                    refine ⟨732803646451071503111753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954143057202857341631341 732803646451071503111753)
                    ·
                      rfl

theorem cell22_2140695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_2140695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140695 prefixEnd_2140695 := by exact prefixLift 2140695
  have htrace : WordTrace (prefixWord ++ tailWord_2140695) baseStart_2140695 baseEnd_2140695 := by
    simpa [prefixWord, tailWord_2140695, baseEnd_2140695] using wordTrace_append hprefix tailTrace_2140695
  have hstable : (prefixWord ++ tailWord_2140695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140695).length < 2 ^ (prefixWord ++ tailWord_2140695).sum := by decide
  have hdescent : baseEnd_2140695 < baseStart_2140695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140764 : List Nat := [2, 2, 4, 1, 4, 9]
def baseStart_2140764 : Nat := 118140960795 + 2140764 * 2 ^ 59
def prefixEnd_2140764 : Nat := 4983230072969 + 3 ^ 40 * 2140764 * 2
def baseEnd_2140764 : Nat := 9047250204458991643661

theorem tailTrace_2140764 : CollatzResearch.WordTrace tailWord_2140764 prefixEnd_2140764 9047250204458991643661 := by
  unfold tailWord_2140764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39040038808192558114170673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52053385077590077485560897 39040038808192558114170673)
  ·
    refine ⟨29280029106144418585628005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39040038808192558114170673 29280029106144418585628005)
    ·
      refine ⟨5490005457402078484805251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29280029106144418585628005 5490005457402078484805251)
      ·
        refine ⟨8235008186103117727207877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490005457402078484805251 8235008186103117727207877)
        ·
          refine ⟨1544064034894334573851477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8235008186103117727207877 1544064034894334573851477)
          ·
            refine ⟨9047250204458991643661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1544064034894334573851477 9047250204458991643661)
            ·
              rfl

theorem cell22_2140764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 9].length) (baseStart_2140764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140764 prefixEnd_2140764 := by exact prefixLift 2140764
  have htrace : WordTrace (prefixWord ++ tailWord_2140764) baseStart_2140764 baseEnd_2140764 := by
    simpa [prefixWord, tailWord_2140764, baseEnd_2140764] using wordTrace_append hprefix tailTrace_2140764
  have hstable : (prefixWord ++ tailWord_2140764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140764).length < 2 ^ (prefixWord ++ tailWord_2140764).sum := by decide
  have hdescent : baseEnd_2140764 < baseStart_2140764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140807 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2140807 : Nat := 118140960795 + 2140807 * 2 ^ 59
def prefixEnd_2140807 : Nat := 4983230072969 + 3 ^ 40 * 2140807 * 2
def baseEnd_2140807 : Nat := 732841986339940544311409

theorem tailTrace_2140807 : CollatzResearch.WordTrace tailWord_2140807 prefixEnd_2140807 732841986339940544311409 := by
  unfold tailWord_2140807
  simp only [CollatzResearch.WordTrace]
  refine ⟨78081645955229334572156675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52054430636819556381437783 78081645955229334572156675)
  ·
    refine ⟨117122468932844001858235013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78081645955229334572156675 117122468932844001858235013)
    ·
      refine ⟨21960462924908250348419065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117122468932844001858235013 21960462924908250348419065)
      ·
        refine ⟨16470347193681187761314299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21960462924908250348419065 16470347193681187761314299)
        ·
          refine ⟨24705520790521781641971449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16470347193681187761314299 24705520790521781641971449)
          ·
            refine ⟨18529140592891336231478587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24705520790521781641971449 18529140592891336231478587)
            ·
              refine ⟨27793710889337004347217881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18529140592891336231478587 27793710889337004347217881)
              ·
                refine ⟨20845283167002753260413411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27793710889337004347217881 20845283167002753260413411)
                ·
                  refine ⟨31267924750504129890620117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20845283167002753260413411 31267924750504129890620117)
                  ·
                    refine ⟨732841986339940544311409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31267924750504129890620117 732841986339940544311409)
                    ·
                      rfl

theorem cell22_2140807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2140807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140807 prefixEnd_2140807 := by exact prefixLift 2140807
  have htrace : WordTrace (prefixWord ++ tailWord_2140807) baseStart_2140807 baseEnd_2140807 := by
    simpa [prefixWord, tailWord_2140807, baseEnd_2140807] using wordTrace_append hprefix tailTrace_2140807
  have hstable : (prefixWord ++ tailWord_2140807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140807).length < 2 ^ (prefixWord ++ tailWord_2140807).sum := by decide
  have hdescent : baseEnd_2140807 < baseStart_2140807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140826 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_2140826 : Nat := 118140960795 + 2140826 * 2 ^ 59
def prefixEnd_2140826 : Nat := 4983230072969 + 3 ^ 40 * 2140826 * 2
def baseEnd_2140826 : Nat := 244282830142743609362117

theorem tailTrace_2140826 : CollatzResearch.WordTrace tailWord_2140826 prefixEnd_2140826 244282830142743609362117 := by
  unfold tailWord_2140826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19520584735540125204274583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52054892628107000544732221 19520584735540125204274583)
  ·
    refine ⟨29280877103310187806411875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19520584735540125204274583 29280877103310187806411875)
    ·
      refine ⟨43921315654965281709617813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29280877103310187806411875 43921315654965281709617813)
      ·
        refine ⟨2058811671326497580138335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43921315654965281709617813 2058811671326497580138335)
        ·
          refine ⟨3088217506989746370207503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058811671326497580138335 3088217506989746370207503)
          ·
            refine ⟨4632326260484619555311255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088217506989746370207503 4632326260484619555311255)
            ·
              refine ⟨6948489390726929332966883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632326260484619555311255 6948489390726929332966883)
              ·
                refine ⟨10422734086090393999450325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6948489390726929332966883 10422734086090393999450325)
                ·
                  refine ⟨244282830142743609362117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10422734086090393999450325 244282830142743609362117)
                  ·
                    rfl

theorem cell22_2140826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_2140826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140826 prefixEnd_2140826 := by exact prefixLift 2140826
  have htrace : WordTrace (prefixWord ++ tailWord_2140826) baseStart_2140826 baseEnd_2140826 := by
    simpa [prefixWord, tailWord_2140826, baseEnd_2140826] using wordTrace_append hprefix tailTrace_2140826
  have hstable : (prefixWord ++ tailWord_2140826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140826).length < 2 ^ (prefixWord ++ tailWord_2140826).sum := by decide
  have hdescent : baseEnd_2140826 < baseStart_2140826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140888 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_2140888 : Nat := 118140960795 + 2140888 * 2 ^ 59
def prefixEnd_2140888 : Nat := 4983230072969 + 3 ^ 40 * 2140888 * 2
def baseEnd_2140888 : Nat := 244289904765094444345387

theorem tailTrace_2140888 : CollatzResearch.WordTrace tailWord_2140888 prefixEnd_2140888 244289904765094444345387 := by
  unfold tailWord_2140888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39042300133967942702927659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52056400178623923603903545 39042300133967942702927659)
  ·
    refine ⟨58563450200951914054391489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39042300133967942702927659 58563450200951914054391489)
    ·
      refine ⟨43922587650713935540793617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58563450200951914054391489 43922587650713935540793617)
      ·
        refine ⟨32941940738035451655595213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43922587650713935540793617 32941940738035451655595213)
        ·
          refine ⟨12353227776763294370848205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32941940738035451655595213 12353227776763294370848205)
          ·
            refine ⟨4632460416286235389068077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12353227776763294370848205 4632460416286235389068077)
            ·
              refine ⟨1737172656107338270900529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4632460416286235389068077 1737172656107338270900529)
              ·
                refine ⟨1302879492080503703175397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737172656107338270900529 1302879492080503703175397)
                ·
                  refine ⟨244289904765094444345387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302879492080503703175397 244289904765094444345387)
                  ·
                    rfl

theorem cell22_2140888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_2140888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140888 prefixEnd_2140888 := by exact prefixLift 2140888
  have htrace : WordTrace (prefixWord ++ tailWord_2140888) baseStart_2140888 baseEnd_2140888 := by
    simpa [prefixWord, tailWord_2140888, baseEnd_2140888] using wordTrace_append hprefix tailTrace_2140888
  have hstable : (prefixWord ++ tailWord_2140888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140888).length < 2 ^ (prefixWord ++ tailWord_2140888).sum := by decide
  have hdescent : baseEnd_2140888 < baseStart_2140888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140899 : List Nat := [1, 1, 1, 7, 1, 1, 1, 9]
def baseStart_2140899 : Nat := 118140960795 + 2140899 * 2 ^ 59
def prefixEnd_2140899 : Nat := 4983230072969 + 3 ^ 40 * 2140899 * 2
def baseEnd_2140899 : Nat := 81430386646675885667903

theorem tailTrace_2140899 : CollatzResearch.WordTrace tailWord_2140899 prefixEnd_2140899 81430386646675885667903 := by
  unfold tailWord_2140899
  simp only [CollatzResearch.WordTrace]
  refine ⟨78085001470896034284505751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52056667647264022856337167 78085001470896034284505751)
  ·
    refine ⟨117127502206344051426758627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78085001470896034284505751 117127502206344051426758627)
    ·
      refine ⟨175691253309516077140137941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117127502206344051426758627 175691253309516077140137941)
      ·
        refine ⟨4117763749441783057971983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 175691253309516077140137941 4117763749441783057971983)
        ·
          refine ⟨6176645624162674586957975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4117763749441783057971983 6176645624162674586957975)
          ·
            refine ⟨9264968436244011880436963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6176645624162674586957975 9264968436244011880436963)
            ·
              refine ⟨13897452654366017820655445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9264968436244011880436963 13897452654366017820655445)
              ·
                refine ⟨81430386646675885667903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13897452654366017820655445 81430386646675885667903)
                ·
                  rfl

theorem cell22_2140899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 9].length) (baseStart_2140899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140899 prefixEnd_2140899 := by exact prefixLift 2140899
  have htrace : WordTrace (prefixWord ++ tailWord_2140899) baseStart_2140899 baseEnd_2140899 := by
    simpa [prefixWord, tailWord_2140899, baseEnd_2140899] using wordTrace_append hprefix tailTrace_2140899
  have hstable : (prefixWord ++ tailWord_2140899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140899).length < 2 ^ (prefixWord ++ tailWord_2140899).sum := by decide
  have hdescent : baseEnd_2140899 < baseStart_2140899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2140959 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_2140959 : Nat := 118140960795 + 2140959 * 2 ^ 59
def prefixEnd_2140959 : Nat := 4983230072969 + 3 ^ 40 * 2140959 * 2
def baseEnd_2140959 : Nat := 732894019046262814510943

theorem tailTrace_2140959 : CollatzResearch.WordTrace tailWord_2140959 prefixEnd_2140959 732894019046262814510943 := by
  unfold tailWord_2140959
  simp only [CollatzResearch.WordTrace]
  refine ⟨78087189850678664531689931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52058126567119109687793287 78087189850678664531689931)
  ·
    refine ⟨117130784776017996797534897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78087189850678664531689931 117130784776017996797534897)
    ·
      refine ⟨87848088582013497598151173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117130784776017996797534897 87848088582013497598151173)
      ·
        refine ⟨16471516609127530799653345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87848088582013497598151173 16471516609127530799653345)
        ·
          refine ⟨12353637456845648099740009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16471516609127530799653345 12353637456845648099740009)
          ·
            refine ⟨9265228092634236074805007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12353637456845648099740009 9265228092634236074805007)
            ·
              refine ⟨13897842138951354112207511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9265228092634236074805007 13897842138951354112207511)
              ·
                refine ⟨20846763208427031168311267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13897842138951354112207511 20846763208427031168311267)
                ·
                  refine ⟨31270144812640546752466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20846763208427031168311267 31270144812640546752466901)
                  ·
                    refine ⟨732894019046262814510943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31270144812640546752466901 732894019046262814510943)
                    ·
                      rfl

theorem cell22_2140959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_2140959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2140959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2140959 prefixEnd_2140959 := by exact prefixLift 2140959
  have htrace : WordTrace (prefixWord ++ tailWord_2140959) baseStart_2140959 baseEnd_2140959 := by
    simpa [prefixWord, tailWord_2140959, baseEnd_2140959] using wordTrace_append hprefix tailTrace_2140959
  have hstable : (prefixWord ++ tailWord_2140959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2140959).length < 2 ^ (prefixWord ++ tailWord_2140959).sum := by decide
  have hdescent : baseEnd_2140959 < baseStart_2140959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2140959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141036 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_2141036 : Nat := 118140960795 + 2141036 * 2 ^ 59
def prefixEnd_2141036 : Nat := 4983230072969 + 3 ^ 40 * 2141036 * 2
def baseEnd_2141036 : Nat := 732920377719860280335707

theorem tailTrace_2141036 : CollatzResearch.WordTrace tailWord_2141036 prefixEnd_2141036 732920377719860280335707 := by
  unfold tailWord_2141036
  simp only [CollatzResearch.WordTrace]
  refine ⟨39044999135699853341121481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52059998847599804454828641 39044999135699853341121481)
  ·
    refine ⟨29283749351774890005841111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39044999135699853341121481 29283749351774890005841111)
    ·
      refine ⟨43925624027662335008761667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29283749351774890005841111 43925624027662335008761667)
      ·
        refine ⟨65888436041493502513142501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43925624027662335008761667 65888436041493502513142501)
        ·
          refine ⟨12354081757780031721214219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65888436041493502513142501 12354081757780031721214219)
          ·
            refine ⟨18531122636670047581821329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354081757780031721214219 18531122636670047581821329)
            ·
              refine ⟨13898341977502535686365997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18531122636670047581821329 13898341977502535686365997)
              ·
                refine ⟨5211878241563450882387249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13898341977502535686365997 5211878241563450882387249)
                ·
                  refine ⟨3908908681172588161790437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5211878241563450882387249 3908908681172588161790437)
                  ·
                    refine ⟨732920377719860280335707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3908908681172588161790437 732920377719860280335707)
                    ·
                      rfl

theorem cell22_2141036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_2141036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141036 prefixEnd_2141036 := by exact prefixLift 2141036
  have htrace : WordTrace (prefixWord ++ tailWord_2141036) baseStart_2141036 baseEnd_2141036 := by
    simpa [prefixWord, tailWord_2141036, baseEnd_2141036] using wordTrace_append hprefix tailTrace_2141036
  have hstable : (prefixWord ++ tailWord_2141036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141036).length < 2 ^ (prefixWord ++ tailWord_2141036).sum := by decide
  have hdescent : baseEnd_2141036 < baseStart_2141036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141113 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 5]
def baseStart_2141113 : Nat := 118140960795 + 2141113 * 2 ^ 59
def prefixEnd_2141113 : Nat := 4983230072969 + 3 ^ 40 * 2141113 * 2
def baseEnd_2141113 : Nat := 244315578797819248720157

theorem tailTrace_2141113 : CollatzResearch.WordTrace tailWord_2141113 prefixEnd_2141113 244315578797819248720157 := by
  unfold tailWord_2141113
  simp only [CollatzResearch.WordTrace]
  refine ⟨78092806692120748832795993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52061871128080499221863995 78092806692120748832795993)
  ·
    refine ⟨58569605019090561624596995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78092806692120748832795993 58569605019090561624596995)
    ·
      refine ⟨87854407528635842436895493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58569605019090561624596995 87854407528635842436895493)
      ·
        refine ⟨16472701411619220456917905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87854407528635842436895493 16472701411619220456917905)
        ·
          refine ⟨12354526058714415342688429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16472701411619220456917905 12354526058714415342688429)
          ·
            refine ⟨4632947272017905753508161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12354526058714415342688429 4632947272017905753508161)
            ·
              refine ⟨3474710454013429315131121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4632947272017905753508161 3474710454013429315131121)
              ·
                refine ⟨2606032840510071986348341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474710454013429315131121 2606032840510071986348341)
                ·
                  refine ⟨244315578797819248720157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606032840510071986348341 244315578797819248720157)
                  ·
                    rfl

theorem cell22_2141113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_2141113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141113 prefixEnd_2141113 := by exact prefixLift 2141113
  have htrace : WordTrace (prefixWord ++ tailWord_2141113) baseStart_2141113 baseEnd_2141113 := by
    simpa [prefixWord, tailWord_2141113, baseEnd_2141113] using wordTrace_append hprefix tailTrace_2141113
  have hstable : (prefixWord ++ tailWord_2141113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141113).length < 2 ^ (prefixWord ++ tailWord_2141113).sum := by decide
  have hdescent : baseEnd_2141113 < baseStart_2141113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141117 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_2141117 : Nat := 118140960795 + 2141117 * 2 ^ 59
def prefixEnd_2141117 : Nat := 4983230072969 + 3 ^ 40 * 2141117 * 2
def baseEnd_2141117 : Nat := 732948105675203069060459

theorem tailTrace_2141117 : CollatzResearch.WordTrace tailWord_2141117 prefixEnd_2141117 732948105675203069060459 := by
  unfold tailWord_2141117
  simp only [CollatzResearch.WordTrace]
  refine ⟨78092952584106257515941605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52061968389404171677294403 78092952584106257515941605)
  ·
    refine ⟨14642428609519923284239051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78092952584106257515941605 14642428609519923284239051)
    ·
      refine ⟨21963642914279884926358577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14642428609519923284239051 21963642914279884926358577)
      ·
        refine ⟨16472732185709913694768933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21963642914279884926358577 16472732185709913694768933)
        ·
          refine ⟨3088637284820608817769175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16472732185709913694768933 3088637284820608817769175)
          ·
            refine ⟨4632955927230913226653763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088637284820608817769175 4632955927230913226653763)
            ·
              refine ⟨6949433890846369839980645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632955927230913226653763 6949433890846369839980645)
              ·
                refine ⟨1303018854533694344996371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6949433890846369839980645 1303018854533694344996371)
                ·
                  refine ⟨1954528281800541517494557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303018854533694344996371 1954528281800541517494557)
                  ·
                    refine ⟨732948105675203069060459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954528281800541517494557 732948105675203069060459)
                    ·
                      rfl

theorem cell22_2141117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_2141117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141117 prefixEnd_2141117 := by exact prefixLift 2141117
  have htrace : WordTrace (prefixWord ++ tailWord_2141117) baseStart_2141117 baseEnd_2141117 := by
    simpa [prefixWord, tailWord_2141117, baseEnd_2141117] using wordTrace_append hprefix tailTrace_2141117
  have hstable : (prefixWord ++ tailWord_2141117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141117).length < 2 ^ (prefixWord ++ tailWord_2141117).sum := by decide
  have hdescent : baseEnd_2141117 < baseStart_2141117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141128 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_2141128 : Nat := 118140960795 + 2141128 * 2 ^ 59
def prefixEnd_2141128 : Nat := 4983230072969 + 3 ^ 40 * 2141128 * 2
def baseEnd_2141128 : Nat := 732951871200002707035425

theorem tailTrace_2141128 : CollatzResearch.WordTrace tailWord_2141128 prefixEnd_2141128 732951871200002707035425 := by
  unfold tailWord_2141128
  simp only [CollatzResearch.WordTrace]
  refine ⟨39046676893533203197296019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52062235858044270929728025 39046676893533203197296019)
  ·
    refine ⟨58570015340299804795944029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39046676893533203197296019 58570015340299804795944029)
    ·
      refine ⟨21963755752612426798479011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58570015340299804795944029 21963755752612426798479011)
      ·
        refine ⟨32945633628918640197718517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21963755752612426798479011 32945633628918640197718517)
        ·
          refine ⟨3088653152711122518536111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32945633628918640197718517 3088653152711122518536111)
          ·
            refine ⟨4632979729066683777804167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088653152711122518536111 4632979729066683777804167)
            ·
              refine ⟨6949469593600025666706251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632979729066683777804167 6949469593600025666706251)
              ·
                refine ⟨10424204390400038500059377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949469593600025666706251 10424204390400038500059377)
                ·
                  refine ⟨7818153292800028875044533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10424204390400038500059377 7818153292800028875044533)
                  ·
                    refine ⟨732951871200002707035425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7818153292800028875044533 732951871200002707035425)
                    ·
                      rfl

theorem cell22_2141128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_2141128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141128 prefixEnd_2141128 := by exact prefixLift 2141128
  have htrace : WordTrace (prefixWord ++ tailWord_2141128) baseStart_2141128 baseEnd_2141128 := by
    simpa [prefixWord, tailWord_2141128, baseEnd_2141128] using wordTrace_append hprefix tailTrace_2141128
  have hstable : (prefixWord ++ tailWord_2141128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141128).length < 2 ^ (prefixWord ++ tailWord_2141128).sum := by decide
  have hdescent : baseEnd_2141128 < baseStart_2141128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141156 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_2141156 : Nat := 118140960795 + 2141156 * 2 ^ 59
def prefixEnd_2141156 : Nat := 4983230072969 + 3 ^ 40 * 2141156 * 2
def baseEnd_2141156 : Nat := 732961456172219967335339

theorem tailTrace_2141156 : CollatzResearch.WordTrace tailWord_2141156 prefixEnd_2141156 732961456172219967335339 := by
  unfold tailWord_2141156
  simp only [CollatzResearch.WordTrace]
  refine ⟨39047187515482483588305661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52062916687309978117740881 39047187515482483588305661)
  ·
    refine ⟨14642695318305931345614623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39047187515482483588305661 14642695318305931345614623)
    ·
      refine ⟨21964042977458897018421935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14642695318305931345614623 21964042977458897018421935)
      ·
        refine ⟨32946064466188345527632903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21964042977458897018421935 32946064466188345527632903)
        ·
          refine ⟨49419096699282518291449355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32946064466188345527632903 49419096699282518291449355)
          ·
            refine ⟨74128645048923777437174033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49419096699282518291449355 74128645048923777437174033)
            ·
              refine ⟨55596483786692833077880525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74128645048923777437174033 55596483786692833077880525)
              ·
                refine ⟨20848681420009812404205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55596483786692833077880525 20848681420009812404205197)
                ·
                  refine ⟨7818255532503679651576949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20848681420009812404205197 7818255532503679651576949)
                  ·
                    refine ⟨732961456172219967335339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7818255532503679651576949 732961456172219967335339)
                    ·
                      rfl

theorem cell22_2141156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_2141156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141156 prefixEnd_2141156 := by exact prefixLift 2141156
  have htrace : WordTrace (prefixWord ++ tailWord_2141156) baseStart_2141156 baseEnd_2141156 := by
    simpa [prefixWord, tailWord_2141156, baseEnd_2141156] using wordTrace_append hprefix tailTrace_2141156
  have hstable : (prefixWord ++ tailWord_2141156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141156).length < 2 ^ (prefixWord ++ tailWord_2141156).sum := by decide
  have hdescent : baseEnd_2141156 < baseStart_2141156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141160 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2141160 : Nat := 118140960795 + 2141160 * 2 ^ 59
def prefixEnd_2141160 : Nat := 4983230072969 + 3 ^ 40 * 2141160 * 2
def baseEnd_2141160 : Nat := 732962825453965290235327

theorem tailTrace_2141160 : CollatzResearch.WordTrace tailWord_2141160 prefixEnd_2141160 732962825453965290235327 := by
  unfold tailWord_2141160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39047260461475237929878467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52063013948633650573171289 39047260461475237929878467)
  ·
    refine ⟨58570890692212856894817701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39047260461475237929878467 58570890692212856894817701)
    ·
      refine ⟨10982042004789910667778319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58570890692212856894817701 10982042004789910667778319)
      ·
        refine ⟨16473063007184866001667479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982042004789910667778319 16473063007184866001667479)
        ·
          refine ⟨24709594510777299002501219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16473063007184866001667479 24709594510777299002501219)
          ·
            refine ⟨37064391766165948503751829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24709594510777299002501219 37064391766165948503751829)
            ·
              refine ⟨1737393364039028836113367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37064391766165948503751829 1737393364039028836113367)
              ·
                refine ⟨2606090046058543254170051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737393364039028836113367 2606090046058543254170051)
                ·
                  refine ⟨3909135069087814881255077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606090046058543254170051 3909135069087814881255077)
                  ·
                    refine ⟨732962825453965290235327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3909135069087814881255077 732962825453965290235327)
                    ·
                      rfl

theorem cell22_2141160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2141160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141160 prefixEnd_2141160 := by exact prefixLift 2141160
  have htrace : WordTrace (prefixWord ++ tailWord_2141160) baseStart_2141160 baseEnd_2141160 := by
    simpa [prefixWord, tailWord_2141160, baseEnd_2141160] using wordTrace_append hprefix tailTrace_2141160
  have hstable : (prefixWord ++ tailWord_2141160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141160).length < 2 ^ (prefixWord ++ tailWord_2141160).sum := by decide
  have hdescent : baseEnd_2141160 < baseStart_2141160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141248 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_2141248 : Nat := 118140960795 + 2141248 * 2 ^ 59
def prefixEnd_2141248 : Nat := 4983230072969 + 3 ^ 40 * 2141248 * 2
def baseEnd_2141248 : Nat := 244330983217454131345019

theorem tailTrace_2141248 : CollatzResearch.WordTrace tailWord_2141248 prefixEnd_2141248 244330983217454131345019 := by
  unfold tailWord_2141248
  simp only [CollatzResearch.WordTrace]
  refine ⟨39048865273315833444480199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52065153697754444592640265 39048865273315833444480199)
  ·
    refine ⟨58573297909973750166720299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39048865273315833444480199 58573297909973750166720299)
    ·
      refine ⟨87859946864960625250080449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58573297909973750166720299 87859946864960625250080449)
      ·
        refine ⟨65894960148720468937560337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87859946864960625250080449 65894960148720468937560337)
        ·
          refine ⟨49421220111540351703170253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65894960148720468937560337 49421220111540351703170253)
          ·
            refine ⟨18532957541827631888688845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49421220111540351703170253 18532957541827631888688845)
            ·
              refine ⟨6949859078185361958258317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18532957541827631888688845 6949859078185361958258317)
              ·
                refine ⟨2606197154319510734346869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6949859078185361958258317 2606197154319510734346869)
                ·
                  refine ⟨244330983217454131345019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606197154319510734346869 244330983217454131345019)
                  ·
                    rfl

theorem cell22_2141248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_2141248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141248 prefixEnd_2141248 := by exact prefixLift 2141248
  have htrace : WordTrace (prefixWord ++ tailWord_2141248) baseStart_2141248 baseEnd_2141248 := by
    simpa [prefixWord, tailWord_2141248, baseEnd_2141248] using wordTrace_append hprefix tailTrace_2141248
  have hstable : (prefixWord ++ tailWord_2141248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141248).length < 2 ^ (prefixWord ++ tailWord_2141248).sum := by decide
  have hdescent : baseEnd_2141248 < baseStart_2141248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141282 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2141282 : Nat := 118140960795 + 2141282 * 2 ^ 59
def prefixEnd_2141282 : Nat := 4983230072969 + 3 ^ 40 * 2141282 * 2
def baseEnd_2141282 : Nat := 244334862849065879561651

theorem tailTrace_2141282 : CollatzResearch.WordTrace tailWord_2141282 prefixEnd_2141282 244334862849065879561651 := by
  unfold tailWord_2141282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19524742657127122673924525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52065980419005660463798733 19524742657127122673924525)
  ·
    refine ⟨7321778496422671002721697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19524742657127122673924525 7321778496422671002721697)
    ·
      refine ⟨5491333872317003252041273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7321778496422671002721697 5491333872317003252041273)
      ·
        refine ⟨4118500404237752439030955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491333872317003252041273 4118500404237752439030955)
        ·
          refine ⟨6177750606356628658546433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118500404237752439030955 6177750606356628658546433)
          ·
            refine ⟨4633312954767471493909825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6177750606356628658546433 4633312954767471493909825)
            ·
              refine ⟨3474984716075603620432369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633312954767471493909825 3474984716075603620432369)
              ·
                refine ⟨2606238537056702715324277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3474984716075603620432369 2606238537056702715324277)
                ·
                  refine ⟨244334862849065879561651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606238537056702715324277 244334862849065879561651)
                  ·
                    rfl

theorem cell22_2141282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2141282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141282 prefixEnd_2141282 := by exact prefixLift 2141282
  have htrace : WordTrace (prefixWord ++ tailWord_2141282) baseStart_2141282 baseEnd_2141282 := by
    simpa [prefixWord, tailWord_2141282, baseEnd_2141282] using wordTrace_append hprefix tailTrace_2141282
  have hstable : (prefixWord ++ tailWord_2141282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141282).length < 2 ^ (prefixWord ++ tailWord_2141282).sum := by decide
  have hdescent : baseEnd_2141282 < baseStart_2141282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141372 : List Nat := [2, 2, 2, 3, 2, 3, 2, 6]
def baseStart_2141372 : Nat := 118140960795 + 2141372 * 2 ^ 59
def prefixEnd_2141372 : Nat := 4983230072969 + 3 ^ 40 * 2141372 * 2
def baseEnd_2141372 : Nat := 81448377487385267103853

theorem tailTrace_2141372 : CollatzResearch.WordTrace tailWord_2141372 prefixEnd_2141372 81448377487385267103853 := by
  unfold tailWord_2141372
  simp only [CollatzResearch.WordTrace]
  refine ⟨39051126599091218033237185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52068168798788290710982913 39051126599091218033237185)
  ·
    refine ⟨29288344949318413524927889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39051126599091218033237185 29288344949318413524927889)
    ·
      refine ⟨21966258711988810143695917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29288344949318413524927889 21966258711988810143695917)
      ·
        refine ⟨8237347016995803803885969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21966258711988810143695917 8237347016995803803885969)
        ·
          refine ⟨6178010262746852852914477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8237347016995803803885969 6178010262746852852914477)
          ·
            refine ⟨2316753848530069819842929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6178010262746852852914477 2316753848530069819842929)
            ·
              refine ⟨1737565386397552364882197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2316753848530069819842929 1737565386397552364882197)
              ·
                refine ⟨81448377487385267103853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1737565386397552364882197 81448377487385267103853)
                ·
                  rfl

theorem cell22_2141372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_2141372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141372 prefixEnd_2141372 := by exact prefixLift 2141372
  have htrace : WordTrace (prefixWord ++ tailWord_2141372) baseStart_2141372 baseEnd_2141372 := by
    simpa [prefixWord, tailWord_2141372, baseEnd_2141372] using wordTrace_append hprefix tailTrace_2141372
  have hstable : (prefixWord ++ tailWord_2141372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141372).length < 2 ^ (prefixWord ++ tailWord_2141372).sum := by decide
  have hdescent : baseEnd_2141372 < baseStart_2141372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141378 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2141378 : Nat := 118140960795 + 2141378 * 2 ^ 59
def prefixEnd_2141378 : Nat := 4983230072969 + 3 ^ 40 * 2141378 * 2
def baseEnd_2141378 : Nat := 244345817103028462761553

theorem tailTrace_2141378 : CollatzResearch.WordTrace tailWord_2141378 prefixEnd_2141378 244345817103028462761553 := by
  unfold tailWord_2141378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19525618009040174772798197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52068314690773799394128525 19525618009040174772798197)
  ·
    refine ⟨1830526688347516384949831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19525618009040174772798197 1830526688347516384949831)
    ·
      refine ⟨2745790032521274577424747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830526688347516384949831 2745790032521274577424747)
      ·
        refine ⟨4118685048781911866137121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745790032521274577424747 4118685048781911866137121)
        ·
          refine ⟨3089013786586433899602841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118685048781911866137121 3089013786586433899602841)
          ·
            refine ⟨2316760339939825424702131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3089013786586433899602841 2316760339939825424702131)
            ·
              refine ⟨3475140509909738137053197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316760339939825424702131 3475140509909738137053197)
              ·
                refine ⟨1303177691216151801394949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475140509909738137053197 1303177691216151801394949)
                ·
                  refine ⟨244345817103028462761553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303177691216151801394949 244345817103028462761553)
                  ·
                    rfl

theorem cell22_2141378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2141378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141378 prefixEnd_2141378 := by exact prefixLift 2141378
  have htrace : WordTrace (prefixWord ++ tailWord_2141378) baseStart_2141378 baseEnd_2141378 := by
    simpa [prefixWord, tailWord_2141378, baseEnd_2141378] using wordTrace_append hprefix tailTrace_2141378
  have hstable : (prefixWord ++ tailWord_2141378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141378).length < 2 ^ (prefixWord ++ tailWord_2141378).sum := by decide
  have hdescent : baseEnd_2141378 < baseStart_2141378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141387 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 1, 3]
def baseStart_2141387 : Nat := 118140960795 + 2141387 * 2 ^ 59
def prefixEnd_2141387 : Nat := 4983230072969 + 3 ^ 40 * 2141387 * 2
def baseEnd_2141387 : Nat := 733040532193012364809631

theorem tailTrace_2141387 : CollatzResearch.WordTrace tailWord_2141387 prefixEnd_2141387 733040532193012364809631 := by
  unfold tailWord_2141387
  simp only [CollatzResearch.WordTrace]
  refine ⟨78102800293128093628270415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52068533528752062418846943 78102800293128093628270415)
  ·
    refine ⟨117154200439692140442405623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78102800293128093628270415 117154200439692140442405623)
    ·
      refine ⟨175731300659538210663608435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117154200439692140442405623 175731300659538210663608435)
      ·
        refine ⟨263596950989307315995412653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175731300659538210663608435 263596950989307315995412653)
        ·
          refine ⟨98848856620990243498279745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263596950989307315995412653 98848856620990243498279745)
          ·
            refine ⟨74136642465742682623709809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98848856620990243498279745 74136642465742682623709809)
            ·
              refine ⟨55602481849307011967782357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74136642465742682623709809 55602481849307011967782357)
              ·
                refine ⟨1303183168343133092994899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55602481849307011967782357 1303183168343133092994899)
                ·
                  refine ⟨1954774752514699639492349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303183168343133092994899 1954774752514699639492349)
                  ·
                    refine ⟨733040532193012364809631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954774752514699639492349 733040532193012364809631)
                    ·
                      rfl

theorem cell22_2141387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 1, 3].length) (baseStart_2141387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141387 prefixEnd_2141387 := by exact prefixLift 2141387
  have htrace : WordTrace (prefixWord ++ tailWord_2141387) baseStart_2141387 baseEnd_2141387 := by
    simpa [prefixWord, tailWord_2141387, baseEnd_2141387] using wordTrace_append hprefix tailTrace_2141387
  have hstable : (prefixWord ++ tailWord_2141387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141387).length < 2 ^ (prefixWord ++ tailWord_2141387).sum := by decide
  have hdescent : baseEnd_2141387 < baseStart_2141387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141389 : List Nat := [1, 6, 2, 2, 1, 2, 8]
def baseStart_2141389 : Nat := 118140960795 + 2141389 * 2 ^ 59
def prefixEnd_2141389 : Nat := 4983230072969 + 3 ^ 40 * 2141389 * 2
def baseEnd_2141389 : Nat := 27149674697551297268875

theorem tailTrace_2141389 : CollatzResearch.WordTrace tailWord_2141389 prefixEnd_2141389 27149674697551297268875 := by
  unfold tailWord_2141389
  simp only [CollatzResearch.WordTrace]
  refine ⟨78102873239120847969843221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52068582159413898646562147 78102873239120847969843221)
  ·
    refine ⟨3661072183083789748586401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78102873239120847969843221 3661072183083789748586401)
    ·
      refine ⟨2745804137312842311439801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661072183083789748586401 2745804137312842311439801)
      ·
        refine ⟨2059353102984631733579851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2745804137312842311439801 2059353102984631733579851)
        ·
          refine ⟨3089029654476947600369777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059353102984631733579851 3089029654476947600369777)
          ·
            refine ⟨2316772240857710700277333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3089029654476947600369777 2316772240857710700277333)
            ·
              refine ⟨27149674697551297268875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2316772240857710700277333 27149674697551297268875)
              ·
                rfl

theorem cell22_2141389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 8].length) (baseStart_2141389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141389 prefixEnd_2141389 := by exact prefixLift 2141389
  have htrace : WordTrace (prefixWord ++ tailWord_2141389) baseStart_2141389 baseEnd_2141389 := by
    simpa [prefixWord, tailWord_2141389, baseEnd_2141389] using wordTrace_append hprefix tailTrace_2141389
  have hstable : (prefixWord ++ tailWord_2141389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141389).length < 2 ^ (prefixWord ++ tailWord_2141389).sum := by decide
  have hdescent : baseEnd_2141389 < baseStart_2141389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141477 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_2141477 : Nat := 118140960795 + 2141477 * 2 ^ 59
def prefixEnd_2141477 : Nat := 4983230072969 + 3 ^ 40 * 2141477 * 2
def baseEnd_2141477 : Nat := 733071341032282130059355

theorem tailTrace_2141477 : CollatzResearch.WordTrace tailWord_2141477 prefixEnd_2141477 733071341032282130059355 := by
  unfold tailWord_2141477
  simp only [CollatzResearch.WordTrace]
  refine ⟨78106082862802038999046685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52070721908534692666031123 78106082862802038999046685)
  ·
    refine ⟨29289781073550764624642507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78106082862802038999046685 29289781073550764624642507)
    ·
      refine ⟨43934671610326146936963761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29289781073550764624642507 43934671610326146936963761)
      ·
        refine ⟨32951003707744610202722821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43934671610326146936963761 32951003707744610202722821)
        ·
          refine ⟨6178313195202114413010529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32951003707744610202722821 6178313195202114413010529)
          ·
            refine ⟨4633734896401585809757897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178313195202114413010529 4633734896401585809757897)
            ·
              refine ⟨3475301172301189357318423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633734896401585809757897 3475301172301189357318423)
              ·
                refine ⟨5212951758451784035977635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475301172301189357318423 5212951758451784035977635)
                ·
                  refine ⟨7819427637677676053966453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212951758451784035977635 7819427637677676053966453)
                  ·
                    refine ⟨733071341032282130059355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7819427637677676053966453 733071341032282130059355)
                    ·
                      rfl

theorem cell22_2141477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_2141477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141477 prefixEnd_2141477 := by exact prefixLift 2141477
  have htrace : WordTrace (prefixWord ++ tailWord_2141477) baseStart_2141477 baseEnd_2141477 := by
    simpa [prefixWord, tailWord_2141477, baseEnd_2141477] using wordTrace_append hprefix tailTrace_2141477
  have hstable : (prefixWord ++ tailWord_2141477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141477).length < 2 ^ (prefixWord ++ tailWord_2141477).sum := by decide
  have hdescent : baseEnd_2141477 < baseStart_2141477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141492 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2141492 : Nat := 118140960795 + 2141492 * 2 ^ 59
def prefixEnd_2141492 : Nat := 4983230072969 + 3 ^ 40 * 2141492 * 2
def baseEnd_2141492 : Nat := 733076475838827090934309

theorem tailTrace_2141492 : CollatzResearch.WordTrace tailWord_2141492 prefixEnd_2141492 733076475838827090934309 := by
  unfold tailWord_2141492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39053314978873848280421365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52071086638498464373895153 39053314978873848280421365)
  ·
    refine ⟨3661248279269423276289503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39053314978873848280421365 3661248279269423276289503)
    ·
      refine ⟨5491872418904134914434255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661248279269423276289503 5491872418904134914434255)
      ·
        refine ⟨8237808628356202371651383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491872418904134914434255 8237808628356202371651383)
        ·
          refine ⟨12356712942534303557477075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237808628356202371651383 12356712942534303557477075)
          ·
            refine ⟨18535069413801455336215613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12356712942534303557477075 18535069413801455336215613)
            ·
              refine ⟨6950651030175545751080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18535069413801455336215613 6950651030175545751080855)
              ·
                refine ⟨10425976545263318626621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6950651030175545751080855 10425976545263318626621283)
                ·
                  refine ⟨15638964817894977939931925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10425976545263318626621283 15638964817894977939931925)
                  ·
                    refine ⟨733076475838827090934309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15638964817894977939931925 733076475838827090934309)
                    ·
                      rfl

theorem cell22_2141492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2141492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141492 prefixEnd_2141492 := by exact prefixLift 2141492
  have htrace : WordTrace (prefixWord ++ tailWord_2141492) baseStart_2141492 baseEnd_2141492 := by
    simpa [prefixWord, tailWord_2141492, baseEnd_2141492] using wordTrace_append hprefix tailTrace_2141492
  have hstable : (prefixWord ++ tailWord_2141492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141492).length < 2 ^ (prefixWord ++ tailWord_2141492).sum := by decide
  have hdescent : baseEnd_2141492 < baseStart_2141492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141586 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2141586 : Nat := 118140960795 + 2141586 * 2 ^ 59
def prefixEnd_2141586 : Nat := 4983230072969 + 3 ^ 40 * 2141586 * 2
def baseEnd_2141586 : Nat := 244369551319947393028007

theorem tailTrace_2141586 : CollatzResearch.WordTrace tailWord_2141586 prefixEnd_2141586 244369551319947393028007 := by
  unfold tailWord_2141586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527514604851787653691153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52073372279604767076509741 19527514604851787653691153)
  ·
    refine ⟨14645635953638840740268365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19527514604851787653691153 14645635953638840740268365)
    ·
      refine ⟨5492113482614565277600637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14645635953638840740268365 5492113482614565277600637)
      ·
        refine ⟨2059542555980461979100239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5492113482614565277600637 2059542555980461979100239)
        ·
          refine ⟨3089313833970692968650359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059542555980461979100239 3089313833970692968650359)
          ·
            refine ⟨4633970750956039452975539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089313833970692968650359 4633970750956039452975539)
            ·
              refine ⟨6950956126434059179463309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4633970750956039452975539 6950956126434059179463309)
              ·
                refine ⟨2606608547412772192298741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6950956126434059179463309 2606608547412772192298741)
                ·
                  refine ⟨244369551319947393028007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606608547412772192298741 244369551319947393028007)
                  ·
                    rfl

theorem cell22_2141586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2141586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141586 prefixEnd_2141586 := by exact prefixLift 2141586
  have htrace : WordTrace (prefixWord ++ tailWord_2141586) baseStart_2141586 baseEnd_2141586 := by
    simpa [prefixWord, tailWord_2141586, baseEnd_2141586] using wordTrace_append hprefix tailTrace_2141586
  have hstable : (prefixWord ++ tailWord_2141586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141586).length < 2 ^ (prefixWord ++ tailWord_2141586).sum := by decide
  have hdescent : baseEnd_2141586 < baseStart_2141586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141599 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 1, 4]
def baseStart_2141599 : Nat := 118140960795 + 2141599 * 2 ^ 59
def prefixEnd_2141599 : Nat := 4983230072969 + 3 ^ 40 * 2141599 * 2
def baseEnd_2141599 : Nat := 733113104125514478508981

theorem tailTrace_2141599 : CollatzResearch.WordTrace tailWord_2141599 prefixEnd_2141599 733113104125514478508981 := by
  unfold tailWord_2141599
  simp only [CollatzResearch.WordTrace]
  refine ⟨78110532568360053834987851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52073688378906702556658567 78110532568360053834987851)
  ·
    refine ⟨117165798852540080752481777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78110532568360053834987851 117165798852540080752481777)
    ·
      refine ⟨87874349139405060564361333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117165798852540080752481777 87874349139405060564361333)
      ·
        refine ⟨8238220231819224427908875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87874349139405060564361333 8238220231819224427908875)
        ·
          refine ⟨12357330347728836641863313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238220231819224427908875 12357330347728836641863313)
          ·
            refine ⟨9267997760796627481397485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12357330347728836641863313 9267997760796627481397485)
            ·
              refine ⟨3475499160298735305524057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9267997760796627481397485 3475499160298735305524057)
              ·
                refine ⟨2606624370224051479143043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475499160298735305524057 2606624370224051479143043)
                ·
                  refine ⟨3909936555336077218714565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606624370224051479143043 3909936555336077218714565)
                  ·
                    refine ⟨733113104125514478508981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3909936555336077218714565 733113104125514478508981)
                    ·
                      rfl

theorem cell22_2141599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_2141599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141599 prefixEnd_2141599 := by exact prefixLift 2141599
  have htrace : WordTrace (prefixWord ++ tailWord_2141599) baseStart_2141599 baseEnd_2141599 := by
    simpa [prefixWord, tailWord_2141599, baseEnd_2141599] using wordTrace_append hprefix tailTrace_2141599
  have hstable : (prefixWord ++ tailWord_2141599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141599).length < 2 ^ (prefixWord ++ tailWord_2141599).sum := by decide
  have hdescent : baseEnd_2141599 < baseStart_2141599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141612 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_2141612 : Nat := 118140960795 + 2141612 * 2 ^ 59
def prefixEnd_2141612 : Nat := 4983230072969 + 3 ^ 40 * 2141612 * 2
def baseEnd_2141612 : Nat := 733117554291186777933941

theorem tailTrace_2141612 : CollatzResearch.WordTrace tailWord_2141612 prefixEnd_2141612 733117554291186777933941 := by
  unfold tailWord_2141612
  simp only [CollatzResearch.WordTrace]
  refine ⟨39055503358656478527605545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52074004478208638036807393 39055503358656478527605545)
  ·
    refine ⟨29291627518992358895704159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39055503358656478527605545 29291627518992358895704159)
    ·
      refine ⟨43937441278488538343556239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29291627518992358895704159 43937441278488538343556239)
      ·
        refine ⟨65906161917732807515334359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43937441278488538343556239 65906161917732807515334359)
        ·
          refine ⟨98859242876599211273001539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65906161917732807515334359 98859242876599211273001539)
          ·
            refine ⟨148288864314898816909502309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98859242876599211273001539 148288864314898816909502309)
            ·
              refine ⟨27804162059043528170531683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148288864314898816909502309 27804162059043528170531683)
              ·
                refine ⟨41706243088565292255797525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27804162059043528170531683 41706243088565292255797525)
                ·
                  refine ⟨1954980144776498074490509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41706243088565292255797525 1954980144776498074490509)
                  ·
                    refine ⟨733117554291186777933941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1954980144776498074490509 733117554291186777933941)
                    ·
                      rfl

theorem cell22_2141612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_2141612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141612 prefixEnd_2141612 := by exact prefixLift 2141612
  have htrace : WordTrace (prefixWord ++ tailWord_2141612) baseStart_2141612 baseEnd_2141612 := by
    simpa [prefixWord, tailWord_2141612, baseEnd_2141612] using wordTrace_append hprefix tailTrace_2141612
  have hstable : (prefixWord ++ tailWord_2141612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141612).length < 2 ^ (prefixWord ++ tailWord_2141612).sum := by decide
  have hdescent : baseEnd_2141612 < baseStart_2141612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141625 : List Nat := [1, 2, 1, 4, 14]
def baseStart_2141625 : Nat := 118140960795 + 2141625 * 2 ^ 59
def prefixEnd_2141625 : Nat := 4983230072969 + 3 ^ 40 * 2141625 * 2
def baseEnd_2141625 : Nat := 3016962981303946820407

theorem tailTrace_2141625 : CollatzResearch.WordTrace tailWord_2141625 prefixEnd_2141625 3016962981303946820407 := by
  unfold tailWord_2141625
  simp only [CollatzResearch.WordTrace]
  refine ⟨78111480866265860275434329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52074320577510573516956219 78111480866265860275434329)
  ·
    refine ⟨58583610649699395206575747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78111480866265860275434329 58583610649699395206575747)
    ·
      refine ⟨87875415974549092809863621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58583610649699395206575747 87875415974549092809863621)
      ·
        refine ⟨16476640495227954901849429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87875415974549092809863621 16476640495227954901849429)
        ·
          refine ⟨3016962981303946820407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 16476640495227954901849429 3016962981303946820407)
          ·
            rfl

theorem cell22_2141625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 14].length) (baseStart_2141625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141625 prefixEnd_2141625 := by exact prefixLift 2141625
  have htrace : WordTrace (prefixWord ++ tailWord_2141625) baseStart_2141625 baseEnd_2141625 := by
    simpa [prefixWord, tailWord_2141625, baseEnd_2141625] using wordTrace_append hprefix tailTrace_2141625
  have hstable : (prefixWord ++ tailWord_2141625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141625).length < 2 ^ (prefixWord ++ tailWord_2141625).sum := by decide
  have hdescent : baseEnd_2141625 < baseStart_2141625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141642 : List Nat := [3, 1, 2, 1, 2, 3, 3, 7]
def baseStart_2141642 : Nat := 118140960795 + 2141642 * 2 ^ 59
def prefixEnd_2141642 : Nat := 4983230072969 + 3 ^ 40 * 2141642 * 2
def baseEnd_2141642 : Nat := 81458647100475188853761

theorem tailTrace_2141642 : CollatzResearch.WordTrace tailWord_2141642 prefixEnd_2141642 81458647100475188853761 := by
  unfold tailWord_2141642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528025226801068044700795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52074733938136181452535453 19528025226801068044700795)
  ·
    refine ⟨29292037840201602067051193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19528025226801068044700795 29292037840201602067051193)
    ·
      refine ⟨21969028380151201550288395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29292037840201602067051193 21969028380151201550288395)
      ·
        refine ⟨32953542570226802325432593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21969028380151201550288395 32953542570226802325432593)
        ·
          refine ⟨24715156927670101744074445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32953542570226802325432593 24715156927670101744074445)
          ·
            refine ⟨9268183847876288154027917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24715156927670101744074445 9268183847876288154027917)
            ·
              refine ⟨3475568942953608057760469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9268183847876288154027917 3475568942953608057760469)
              ·
                refine ⟨81458647100475188853761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3475568942953608057760469 81458647100475188853761)
                ·
                  rfl

theorem cell22_2141642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_2141642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141642 prefixEnd_2141642 := by exact prefixLift 2141642
  have htrace : WordTrace (prefixWord ++ tailWord_2141642) baseStart_2141642 baseEnd_2141642 := by
    simpa [prefixWord, tailWord_2141642, baseEnd_2141642] using wordTrace_append hprefix tailTrace_2141642
  have hstable : (prefixWord ++ tailWord_2141642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141642).length < 2 ^ (prefixWord ++ tailWord_2141642).sum := by decide
  have hdescent : baseEnd_2141642 < baseStart_2141642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141661 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2141661 : Nat := 118140960795 + 2141661 * 2 ^ 59
def prefixEnd_2141661 : Nat := 4983230072969 + 3 ^ 40 * 2141661 * 2
def baseEnd_2141661 : Nat := 733134327992566983458791

theorem tailTrace_2141661 : CollatzResearch.WordTrace tailWord_2141661 prefixEnd_2141661 733134327992566983458791 := by
  unfold tailWord_2141661
  simp only [CollatzResearch.WordTrace]
  refine ⟨78112793894135438423744837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52075195929423625615829891 78112793894135438423744837)
  ·
    refine ⟨14646148855150394704452157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78112793894135438423744837 14646148855150394704452157)
    ·
      refine ⟨5492305820681398014169559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14646148855150394704452157 5492305820681398014169559)
      ·
        refine ⟨8238458731022097021254339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5492305820681398014169559 8238458731022097021254339)
        ·
          refine ⟨12357688096533145531881509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238458731022097021254339 12357688096533145531881509)
          ·
            refine ⟨2317066518099964787227783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12357688096533145531881509 2317066518099964787227783)
            ·
              refine ⟨3475599777149947180841675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317066518099964787227783 3475599777149947180841675)
              ·
                refine ⟨5213399665724920771262513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475599777149947180841675 5213399665724920771262513)
                ·
                  refine ⟨3910049749293690578446885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213399665724920771262513 3910049749293690578446885)
                  ·
                    refine ⟨733134327992566983458791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910049749293690578446885 733134327992566983458791)
                    ·
                      rfl

theorem cell22_2141661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2141661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141661 prefixEnd_2141661 := by exact prefixLift 2141661
  have htrace : WordTrace (prefixWord ++ tailWord_2141661) baseStart_2141661 baseEnd_2141661 := by
    simpa [prefixWord, tailWord_2141661, baseEnd_2141661] using wordTrace_append hprefix tailTrace_2141661
  have hstable : (prefixWord ++ tailWord_2141661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141661).length < 2 ^ (prefixWord ++ tailWord_2141661).sum := by decide
  have hdescent : baseEnd_2141661 < baseStart_2141661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141687 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 5]
def baseStart_2141687 : Nat := 118140960795 + 2141687 * 2 ^ 59
def prefixEnd_2141687 : Nat := 4983230072969 + 3 ^ 40 * 2141687 * 2
def baseEnd_2141687 : Nat := 244381076107970527436237

theorem tailTrace_2141687 : CollatzResearch.WordTrace tailWord_2141687 prefixEnd_2141687 244381076107970527436237 := by
  unfold tailWord_2141687
  simp only [CollatzResearch.WordTrace]
  refine ⟨78113742192041244864191315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52075828128027496576127543 78113742192041244864191315)
  ·
    refine ⟨117170613288061867296286973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78113742192041244864191315 117170613288061867296286973)
    ·
      refine ⟨43938979983023200236107615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117170613288061867296286973 43938979983023200236107615)
      ·
        refine ⟨65908469974534800354161423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43938979983023200236107615 65908469974534800354161423)
        ·
          refine ⟨98862704961802200531242135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65908469974534800354161423 98862704961802200531242135)
          ·
            refine ⟨148294057442703300796863203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98862704961802200531242135 148294057442703300796863203)
            ·
              refine ⟨222441086164054951195294805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148294057442703300796863203 222441086164054951195294805)
              ·
                refine ⟨2606731478485018959319861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 222441086164054951195294805 2606731478485018959319861)
                ·
                  refine ⟨244381076107970527436237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606731478485018959319861 244381076107970527436237)
                  ·
                    rfl

theorem cell22_2141687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 5].length) (baseStart_2141687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141687 prefixEnd_2141687 := by exact prefixLift 2141687
  have htrace : WordTrace (prefixWord ++ tailWord_2141687) baseStart_2141687 baseEnd_2141687 := by
    simpa [prefixWord, tailWord_2141687, baseEnd_2141687] using wordTrace_append hprefix tailTrace_2141687
  have hstable : (prefixWord ++ tailWord_2141687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141687).length < 2 ^ (prefixWord ++ tailWord_2141687).sum := by decide
  have hdescent : baseEnd_2141687 < baseStart_2141687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141749 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 6]
def baseStart_2141749 : Nat := 118140960795 + 2141749 * 2 ^ 59
def prefixEnd_2141749 : Nat := 4983230072969 + 3 ^ 40 * 2141749 * 2
def baseEnd_2141749 : Nat := 244388150730321362419507

theorem tailTrace_2141749 : CollatzResearch.WordTrace tailWord_2141749 prefixEnd_2141749 244388150730321362419507 := by
  unfold tailWord_2141749
  simp only [CollatzResearch.WordTrace]
  refine ⟨78116003517816629452948301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52077335678544419635298867 78116003517816629452948301)
  ·
    refine ⟨29293501319181236044855613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78116003517816629452948301 29293501319181236044855613)
    ·
      refine ⟨10985062994692963516820855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29293501319181236044855613 10985062994692963516820855)
      ·
        refine ⟨16477594492039445275231283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10985062994692963516820855 16477594492039445275231283)
        ·
          refine ⟨24716391738059167912846925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16477594492039445275231283 24716391738059167912846925)
          ·
            refine ⟨9268646901772187967317597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24716391738059167912846925 9268646901772187967317597)
            ·
              refine ⟨3475742588164570487744099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9268646901772187967317597 3475742588164570487744099)
              ·
                refine ⟨5213613882246855731616149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475742588164570487744099 5213613882246855731616149)
                ·
                  refine ⟨244388150730321362419507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5213613882246855731616149 244388150730321362419507)
                  ·
                    rfl

theorem cell22_2141749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_2141749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141749 prefixEnd_2141749 := by exact prefixLift 2141749
  have htrace : WordTrace (prefixWord ++ tailWord_2141749) baseStart_2141749 baseEnd_2141749 := by
    simpa [prefixWord, tailWord_2141749, baseEnd_2141749] using wordTrace_append hprefix tailTrace_2141749
  have hstable : (prefixWord ++ tailWord_2141749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141749).length < 2 ^ (prefixWord ++ tailWord_2141749).sum := by decide
  have hdescent : baseEnd_2141749 < baseStart_2141749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141777 : List Nat := [1, 2, 2, 1, 3, 2, 1, 10]
def baseStart_2141777 : Nat := 118140960795 + 2141777 * 2 ^ 59
def prefixEnd_2141777 : Nat := 4983230072969 + 3 ^ 40 * 2141777 * 2
def baseEnd_2141777 : Nat := 81463781907020149728715

theorem tailTrace_2141777 : CollatzResearch.WordTrace tailWord_2141777 prefixEnd_2141777 81463781907020149728715 := by
  unfold tailWord_2141777
  simp only [CollatzResearch.WordTrace]
  refine ⟨78117024761715190234967585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52078016507810126823311723 78117024761715190234967585)
  ·
    refine ⟨58587768571286392676225689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78117024761715190234967585 58587768571286392676225689)
    ·
      refine ⟨43940826428464794507169267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58587768571286392676225689 43940826428464794507169267)
      ·
        refine ⟨65911239642697191760753901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43940826428464794507169267 65911239642697191760753901)
        ·
          refine ⟨24716714866011446910282713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65911239642697191760753901 24716714866011446910282713)
          ·
            refine ⟨18537536149508585182712035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24716714866011446910282713 18537536149508585182712035)
            ·
              refine ⟨27806304224262877774068053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18537536149508585182712035 27806304224262877774068053)
              ·
                refine ⟨81463781907020149728715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27806304224262877774068053 81463781907020149728715)
                ·
                  rfl

theorem cell22_2141777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 10].length) (baseStart_2141777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141777 prefixEnd_2141777 := by exact prefixLift 2141777
  have htrace : WordTrace (prefixWord ++ tailWord_2141777) baseStart_2141777 baseEnd_2141777 := by
    simpa [prefixWord, tailWord_2141777, baseEnd_2141777] using wordTrace_append hprefix tailTrace_2141777
  have hstable : (prefixWord ++ tailWord_2141777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141777).length < 2 ^ (prefixWord ++ tailWord_2141777).sum := by decide
  have hdescent : baseEnd_2141777 < baseStart_2141777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141800 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_2141800 : Nat := 118140960795 + 2141800 * 2 ^ 59
def prefixEnd_2141800 : Nat := 4983230072969 + 3 ^ 40 * 2141800 * 2
def baseEnd_2141800 : Nat := 244393970177738984744455

theorem tailTrace_2141800 : CollatzResearch.WordTrace tailWord_2141800 prefixEnd_2141800 244393970177738984744455 := by
  unfold tailWord_2141800
  simp only [CollatzResearch.WordTrace]
  refine ⟨39058931820315932581527427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52078575760421243442036569 39058931820315932581527427)
  ·
    refine ⟨58588397730473898872291141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39058931820315932581527427 58588397730473898872291141)
    ·
      refine ⟨10985324574463856038554589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58588397730473898872291141 10985324574463856038554589)
      ·
        refine ⟨4119496715423946014457971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10985324574463856038554589 4119496715423946014457971)
        ·
          refine ⟨6179245073135919021686957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119496715423946014457971 6179245073135919021686957)
          ·
            refine ⟨2317216902425969633132609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6179245073135919021686957 2317216902425969633132609)
            ·
              refine ⟨1737912676819477224849457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317216902425969633132609 1737912676819477224849457)
              ·
                refine ⟨1303434507614607918637093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737912676819477224849457 1303434507614607918637093)
                ·
                  refine ⟨244393970177738984744455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303434507614607918637093 244393970177738984744455)
                  ·
                    rfl

theorem cell22_2141800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_2141800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141800 prefixEnd_2141800 := by exact prefixLift 2141800
  have htrace : WordTrace (prefixWord ++ tailWord_2141800) baseStart_2141800 baseEnd_2141800 := by
    simpa [prefixWord, tailWord_2141800, baseEnd_2141800] using wordTrace_append hprefix tailTrace_2141800
  have hstable : (prefixWord ++ tailWord_2141800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141800).length < 2 ^ (prefixWord ++ tailWord_2141800).sum := by decide
  have hdescent : baseEnd_2141800 < baseStart_2141800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141809 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 7, 3]
def baseStart_2141809 : Nat := 118140960795 + 2141809 * 2 ^ 59
def prefixEnd_2141809 : Nat := 4983230072969 + 3 ^ 40 * 2141809 * 2
def baseEnd_2141809 : Nat := 733184991417143930758337

theorem tailTrace_2141809 : CollatzResearch.WordTrace tailWord_2141809 prefixEnd_2141809 733184991417143930758337 := by
  unfold tailWord_2141809
  simp only [CollatzResearch.WordTrace]
  refine ⟨78118191897599259700132481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52078794598399506466754987 78118191897599259700132481)
  ·
    refine ⟨58588643923199444775099361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78118191897599259700132481 58588643923199444775099361)
    ·
      refine ⟨43941482942399583581324521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58588643923199444775099361 43941482942399583581324521)
      ·
        refine ⟨32956112206799687685993391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43941482942399583581324521 32956112206799687685993391)
        ·
          refine ⟨49434168310199531528990087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32956112206799687685993391 49434168310199531528990087)
          ·
            refine ⟨74151252465299297293485131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49434168310199531528990087 74151252465299297293485131)
            ·
              refine ⟨111226878697948945940227697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74151252465299297293485131 111226878697948945940227697)
              ·
                refine ⟨83420159023461709455170773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111226878697948945940227697 83420159023461709455170773)
                ·
                  refine ⟨1955159977112383815355565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 83420159023461709455170773 1955159977112383815355565)
                  ·
                    refine ⟨733184991417143930758337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955159977112383815355565 733184991417143930758337)
                    ·
                      rfl

theorem cell22_2141809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_2141809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141809 prefixEnd_2141809 := by exact prefixLift 2141809
  have htrace : WordTrace (prefixWord ++ tailWord_2141809) baseStart_2141809 baseEnd_2141809 := by
    simpa [prefixWord, tailWord_2141809, baseEnd_2141809] using wordTrace_append hprefix tailTrace_2141809
  have hstable : (prefixWord ++ tailWord_2141809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141809).length < 2 ^ (prefixWord ++ tailWord_2141809).sum := by decide
  have hdescent : baseEnd_2141809 < baseStart_2141809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141856 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_2141856 : Nat := 118140960795 + 2141856 * 2 ^ 59
def prefixEnd_2141856 : Nat := 4983230072969 + 3 ^ 40 * 2141856 * 2
def baseEnd_2141856 : Nat := 244400360159217158277731

theorem tailTrace_2141856 : CollatzResearch.WordTrace tailWord_2141856 prefixEnd_2141856 244400360159217158277731 := by
  unfold tailWord_2141856
  simp only [CollatzResearch.WordTrace]
  refine ⟨39059953064214493363546711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52079937418952657818062281 39059953064214493363546711)
  ·
    refine ⟨58589929596321740045320067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39059953064214493363546711 58589929596321740045320067)
    ·
      refine ⟨87884894394482610067980101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58589929596321740045320067 87884894394482610067980101)
      ·
        refine ⟨16478417698965489387746269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87884894394482610067980101 16478417698965489387746269)
        ·
          refine ⟨6179406637112058520404851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16478417698965489387746269 6179406637112058520404851)
          ·
            refine ⟨9269109955668087780607277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179406637112058520404851 9269109955668087780607277)
            ·
              refine ⟨3475916233375532917727729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9269109955668087780607277 3475916233375532917727729)
              ·
                refine ⟨2606937175031649688295797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475916233375532917727729 2606937175031649688295797)
                ·
                  refine ⟨244400360159217158277731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2606937175031649688295797 244400360159217158277731)
                  ·
                    rfl

theorem cell22_2141856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_2141856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141856 prefixEnd_2141856 := by exact prefixLift 2141856
  have htrace : WordTrace (prefixWord ++ tailWord_2141856) baseStart_2141856 baseEnd_2141856 := by
    simpa [prefixWord, tailWord_2141856, baseEnd_2141856] using wordTrace_append hprefix tailTrace_2141856
  have hstable : (prefixWord ++ tailWord_2141856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141856).length < 2 ^ (prefixWord ++ tailWord_2141856).sum := by decide
  have hdescent : baseEnd_2141856 < baseStart_2141856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141894 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2141894 : Nat := 118140960795 + 2141894 * 2 ^ 59
def prefixEnd_2141894 : Nat := 4983230072969 + 3 ^ 40 * 2141894 * 2
def baseEnd_2141894 : Nat := 733214088654232042383077

theorem tailTrace_2141894 : CollatzResearch.WordTrace tailWord_2141894 prefixEnd_2141894 733214088654232042383077 := by
  unfold tailWord_2141894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441290378196603725530523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52080861401527546144651157 2441290378196603725530523)
  ·
    refine ⟨3661935567294905588295785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2441290378196603725530523 3661935567294905588295785)
    ·
      refine ⟨2746451675471179191221839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661935567294905588295785 2746451675471179191221839)
      ·
        refine ⟨4119677513206768786832759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746451675471179191221839 4119677513206768786832759)
        ·
          refine ⟨6179516269810153180249139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119677513206768786832759 6179516269810153180249139)
          ·
            refine ⟨9269274404715229770373709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179516269810153180249139 9269274404715229770373709)
            ·
              refine ⟨3475977901768211163890141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9269274404715229770373709 3475977901768211163890141)
              ·
                refine ⟨1303491713163079186458803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475977901768211163890141 1303491713163079186458803)
                ·
                  refine ⟨1955237569744618779688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303491713163079186458803 1955237569744618779688205)
                  ·
                    refine ⟨733214088654232042383077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955237569744618779688205 733214088654232042383077)
                    ·
                      rfl

theorem cell22_2141894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2141894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141894 prefixEnd_2141894 := by exact prefixLift 2141894
  have htrace : WordTrace (prefixWord ++ tailWord_2141894) baseStart_2141894 baseEnd_2141894 := by
    simpa [prefixWord, tailWord_2141894, baseEnd_2141894] using wordTrace_append hprefix tailTrace_2141894
  have hstable : (prefixWord ++ tailWord_2141894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141894).length < 2 ^ (prefixWord ++ tailWord_2141894).sum := by decide
  have hdescent : baseEnd_2141894 < baseStart_2141894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141899 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_2141899 : Nat := 118140960795 + 2141899 * 2 ^ 59
def prefixEnd_2141899 : Nat := 4983230072969 + 3 ^ 40 * 2141899 * 2
def baseEnd_2141899 : Nat := 733215800256413696008061

theorem tailTrace_2141899 : CollatzResearch.WordTrace tailWord_2141899 prefixEnd_2141899 733215800256413696008061 := by
  unfold tailWord_2141899
  simp only [CollatzResearch.WordTrace]
  refine ⟨78121474467273205070908751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52080982978182136713939167 78121474467273205070908751)
  ·
    refine ⟨117182211700909807606363127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78121474467273205070908751 117182211700909807606363127)
    ·
      refine ⟨175773317551364711409544691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117182211700909807606363127 175773317551364711409544691)
      ·
        refine ⟨263659976327047067114317037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175773317551364711409544691 263659976327047067114317037)
        ·
          refine ⟨98872491122642650167868889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263659976327047067114317037 98872491122642650167868889)
          ·
            refine ⟨74154368341981987625901667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98872491122642650167868889 74154368341981987625901667)
            ·
              refine ⟨111231552512972981438852501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74154368341981987625901667 111231552512972981438852501)
              ·
                refine ⟨5213979024045608504946211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111231552512972981438852501 5213979024045608504946211)
                ·
                  refine ⟨7820968536068412757419317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5213979024045608504946211 7820968536068412757419317)
                  ·
                    refine ⟨733215800256413696008061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7820968536068412757419317 733215800256413696008061)
                    ·
                      rfl

theorem cell22_2141899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_2141899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2141899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2141899 prefixEnd_2141899 := by exact prefixLift 2141899
  have htrace : WordTrace (prefixWord ++ tailWord_2141899) baseStart_2141899 baseEnd_2141899 := by
    simpa [prefixWord, tailWord_2141899, baseEnd_2141899] using wordTrace_append hprefix tailTrace_2141899
  have hstable : (prefixWord ++ tailWord_2141899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141899).length < 2 ^ (prefixWord ++ tailWord_2141899).sum := by decide
  have hdescent : baseEnd_2141899 < baseStart_2141899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142083 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_2142083 : Nat := 118140960795 + 2142083 * 2 ^ 59
def prefixEnd_2142083 : Nat := 4983230072969 + 3 ^ 40 * 2142083 * 2
def baseEnd_2142083 : Nat := 733278787216698549407497

theorem tailTrace_2142083 : CollatzResearch.WordTrace tailWord_2142083 prefixEnd_2142083 733278787216698549407497 := by
  unfold tailWord_2142083
  simp only [CollatzResearch.WordTrace]
  refine ⟨78128185498606604495606903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52085456999071069663737935 78128185498606604495606903)
  ·
    refine ⟨117192278247909906743410355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78128185498606604495606903 117192278247909906743410355)
    ·
      refine ⟨175788417371864860115115533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117192278247909906743410355 175788417371864860115115533)
      ·
        refine ⟨65920656514449322543168325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175788417371864860115115533 65920656514449322543168325)
        ·
          refine ⟨12360123096459247976844061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65920656514449322543168325 12360123096459247976844061)
          ·
            refine ⟨4635046161172217991316523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12360123096459247976844061 4635046161172217991316523)
            ·
              refine ⟨6952569241758326986974785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635046161172217991316523 6952569241758326986974785)
              ·
                refine ⟨5214426931318745240231089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6952569241758326986974785 5214426931318745240231089)
                ·
                  refine ⟨3910820198489058930173317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5214426931318745240231089 3910820198489058930173317)
                  ·
                    refine ⟨733278787216698549407497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3910820198489058930173317 733278787216698549407497)
                    ·
                      rfl

theorem cell22_2142083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_2142083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142083 prefixEnd_2142083 := by exact prefixLift 2142083
  have htrace : WordTrace (prefixWord ++ tailWord_2142083) baseStart_2142083 baseEnd_2142083 := by
    simpa [prefixWord, tailWord_2142083, baseEnd_2142083] using wordTrace_append hprefix tailTrace_2142083
  have hstable : (prefixWord ++ tailWord_2142083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142083).length < 2 ^ (prefixWord ++ tailWord_2142083).sum := by decide
  have hdescent : baseEnd_2142083 < baseStart_2142083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142087 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 4]
def baseStart_2142087 : Nat := 118140960795 + 2142087 * 2 ^ 59
def prefixEnd_2142087 : Nat := 4983230072969 + 3 ^ 40 * 2142087 * 2
def baseEnd_2142087 : Nat := 244426718832814624102495

theorem tailTrace_2142087 : CollatzResearch.WordTrace tailWord_2142087 prefixEnd_2142087 244426718832814624102495 := by
  unfold tailWord_2142087
  simp only [CollatzResearch.WordTrace]
  refine ⟨78128331390592113178752515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52085554260394742119168343 78128331390592113178752515)
  ·
    refine ⟨117192497085888169768128773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78128331390592113178752515 117192497085888169768128773)
    ·
      refine ⟨21973593203604031831524145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117192497085888169768128773 21973593203604031831524145)
      ·
        refine ⟨16480194902703023873643109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21973593203604031831524145 16480194902703023873643109)
        ·
          refine ⟨3090036544256816976308083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16480194902703023873643109 3090036544256816976308083)
          ·
            refine ⟨4635054816385225464462125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090036544256816976308083 4635054816385225464462125)
            ·
              refine ⟨1738145556144459549173297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4635054816385225464462125 1738145556144459549173297)
              ·
                refine ⟨1303609167108344661879973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738145556144459549173297 1303609167108344661879973)
                ·
                  refine ⟨244426718832814624102495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303609167108344661879973 244426718832814624102495)
                  ·
                    rfl

theorem cell22_2142087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 4].length) (baseStart_2142087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142087 prefixEnd_2142087 := by exact prefixLift 2142087
  have htrace : WordTrace (prefixWord ++ tailWord_2142087) baseStart_2142087 baseEnd_2142087 := by
    simpa [prefixWord, tailWord_2142087, baseEnd_2142087] using wordTrace_append hprefix tailTrace_2142087
  have hstable : (prefixWord ++ tailWord_2142087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142087).length < 2 ^ (prefixWord ++ tailWord_2142087).sum := by decide
  have hdescent : baseEnd_2142087 < baseStart_2142087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142098 : List Nat := [3, 2, 3, 2, 1, 1, 1, 9]
def baseStart_2142098 : Nat := 118140960795 + 2142098 * 2 ^ 59
def prefixEnd_2142098 : Nat := 4983230072969 + 3 ^ 40 * 2142098 * 2
def baseEnd_2142098 : Nat := 81475991335915945586939

theorem tailTrace_2142098 : CollatzResearch.WordTrace tailWord_2142098 prefixEnd_2142098 81475991335915945586939 := by
  unfold tailWord_2142098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532183148388065514350737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52085821729034841371601965 19532183148388065514350737)
  ·
    refine ⟨14649137361291049135763053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19532183148388065514350737 14649137361291049135763053)
    ·
      refine ⟨5493426510484143425911145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14649137361291049135763053 5493426510484143425911145)
      ·
        refine ⟨4120069882863107569433359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493426510484143425911145 4120069882863107569433359)
        ·
          refine ⟨6180104824294661354150039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120069882863107569433359 6180104824294661354150039)
          ·
            refine ⟨9270157236441992031225059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180104824294661354150039 9270157236441992031225059)
            ·
              refine ⟨13905235854662988046837589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9270157236441992031225059 13905235854662988046837589)
              ·
                refine ⟨81475991335915945586939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13905235854662988046837589 81475991335915945586939)
                ·
                  rfl

theorem cell22_2142098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_2142098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142098 prefixEnd_2142098 := by exact prefixLift 2142098
  have htrace : WordTrace (prefixWord ++ tailWord_2142098) baseStart_2142098 baseEnd_2142098 := by
    simpa [prefixWord, tailWord_2142098, baseEnd_2142098] using wordTrace_append hprefix tailTrace_2142098
  have hstable : (prefixWord ++ tailWord_2142098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142098).length < 2 ^ (prefixWord ++ tailWord_2142098).sum := by decide
  have hdescent : baseEnd_2142098 < baseStart_2142098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142143 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 5]
def baseStart_2142143 : Nat := 118140960795 + 2142143 * 2 ^ 59
def prefixEnd_2142143 : Nat := 4983230072969 + 3 ^ 40 * 2142143 * 2
def baseEnd_2142143 : Nat := 244433108814292797635771

theorem tailTrace_2142143 : CollatzResearch.WordTrace tailWord_2142143 prefixEnd_2142143 244433108814292797635771 := by
  unfold tailWord_2142143
  simp only [CollatzResearch.WordTrace]
  refine ⟨78130373878389234742791083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52086915918926156495194055 78130373878389234742791083)
  ·
    refine ⟨117195560817583852114186625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78130373878389234742791083 117195560817583852114186625)
    ·
      refine ⟨87896670613187889085639969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117195560817583852114186625 87896670613187889085639969)
      ·
        refine ⟨65922502959890916814229977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87896670613187889085639969 65922502959890916814229977)
        ·
          refine ⟨49441877219918187610672483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65922502959890916814229977 49441877219918187610672483)
          ·
            refine ⟨74162815829877281416008725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49441877219918187610672483 74162815829877281416008725)
            ·
              refine ⟨3476381992025497566375409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74162815829877281416008725 3476381992025497566375409)
              ·
                refine ⟨2607286494019123174781557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3476381992025497566375409 2607286494019123174781557)
                ·
                  refine ⟨244433108814292797635771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607286494019123174781557 244433108814292797635771)
                  ·
                    rfl

theorem cell22_2142143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].length) (baseStart_2142143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142143 prefixEnd_2142143 := by exact prefixLift 2142143
  have htrace : WordTrace (prefixWord ++ tailWord_2142143) baseStart_2142143 baseEnd_2142143 := by
    simpa [prefixWord, tailWord_2142143, baseEnd_2142143] using wordTrace_append hprefix tailTrace_2142143
  have hstable : (prefixWord ++ tailWord_2142143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142143).length < 2 ^ (prefixWord ++ tailWord_2142143).sum := by decide
  have hdescent : baseEnd_2142143 < baseStart_2142143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142158 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2142158 : Nat := 118140960795 + 2142158 * 2 ^ 59
def prefixEnd_2142158 : Nat := 4983230072969 + 3 ^ 40 * 2142158 * 2
def baseEnd_2142158 : Nat := 733304461249423353782267

theorem tailTrace_2142158 : CollatzResearch.WordTrace tailWord_2142158 prefixEnd_2142158 733304461249423353782267 := by
  unfold tailWord_2142158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9766365121666861538073391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52087280648889928203058085 9766365121666861538073391)
  ·
    refine ⟨14649547682500292307110087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9766365121666861538073391 14649547682500292307110087)
    ·
      refine ⟨21974321523750438460665131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14649547682500292307110087 21974321523750438460665131)
      ·
        refine ⟨32961482285625657690997697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21974321523750438460665131 32961482285625657690997697)
        ·
          refine ⟨24721111714219243268248273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32961482285625657690997697 24721111714219243268248273)
          ·
            refine ⟨18540833785664432451186205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24721111714219243268248273 18540833785664432451186205)
            ·
              refine ⟨6952812669624162169194827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18540833785664432451186205 6952812669624162169194827)
              ·
                refine ⟨10429219004436243253792241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6952812669624162169194827 10429219004436243253792241)
                ·
                  refine ⟨7821914253327182440344181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10429219004436243253792241 7821914253327182440344181)
                  ·
                    refine ⟨733304461249423353782267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7821914253327182440344181 733304461249423353782267)
                    ·
                      rfl

theorem cell22_2142158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2142158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142158 prefixEnd_2142158 := by exact prefixLift 2142158
  have htrace : WordTrace (prefixWord ++ tailWord_2142158) baseStart_2142158 baseEnd_2142158 := by
    simpa [prefixWord, tailWord_2142158, baseEnd_2142158] using wordTrace_append hprefix tailTrace_2142158
  have hstable : (prefixWord ++ tailWord_2142158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142158).length < 2 ^ (prefixWord ++ tailWord_2142158).sum := by decide
  have hdescent : baseEnd_2142158 < baseStart_2142158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142205 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 4]
def baseStart_2142205 : Nat := 118140960795 + 2142205 * 2 ^ 59
def prefixEnd_2142205 : Nat := 4983230072969 + 3 ^ 40 * 2142205 * 2
def baseEnd_2142205 : Nat := 244440183436643632619041

theorem tailTrace_2142205 : CollatzResearch.WordTrace tailWord_2142205 prefixEnd_2142205 244440183436643632619041 := by
  unfold tailWord_2142205
  simp only [CollatzResearch.WordTrace]
  refine ⟨78132635204164619331548069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52088423469443079554365379 78132635204164619331548069)
  ·
    refine ⟨14649869100780866124665263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78132635204164619331548069 14649869100780866124665263)
    ·
      refine ⟨21974803651171299186997895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14649869100780866124665263 21974803651171299186997895)
      ·
        refine ⟨32962205476756948780496843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21974803651171299186997895 32962205476756948780496843)
        ·
          refine ⟨49443308215135423170745265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32962205476756948780496843 49443308215135423170745265)
          ·
            refine ⟨37082481161351567378058949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49443308215135423170745265 37082481161351567378058949)
            ·
              refine ⟨6952965217753418883386053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37082481161351567378058949 6952965217753418883386053)
              ·
                refine ⟨1303680978328766040634885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6952965217753418883386053 1303680978328766040634885)
                ·
                  refine ⟨244440183436643632619041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303680978328766040634885 244440183436643632619041)
                  ·
                    rfl

theorem cell22_2142205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_2142205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142205 prefixEnd_2142205 := by exact prefixLift 2142205
  have htrace : WordTrace (prefixWord ++ tailWord_2142205) baseStart_2142205 baseEnd_2142205 := by
    simpa [prefixWord, tailWord_2142205, baseEnd_2142205] using wordTrace_append hprefix tailTrace_2142205
  have hstable : (prefixWord ++ tailWord_2142205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142205).length < 2 ^ (prefixWord ++ tailWord_2142205).sum := by decide
  have hdescent : baseEnd_2142205 < baseStart_2142205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142250 : List Nat := [3, 1, 4, 1, 2, 3, 8]
def baseStart_2142250 : Nat := 118140960795 + 2142250 * 2 ^ 59
def prefixEnd_2142250 : Nat := 4983230072969 + 3 ^ 40 * 2142250 * 2
def baseEnd_2142250 : Nat := 27160590915909843721555

theorem tailTrace_2142250 : CollatzResearch.WordTrace tailWord_2142250 prefixEnd_2142250 27160590915909843721555 := by
  unfold tailWord_2142250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19533569122250398004234051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52089517659334394677957469 19533569122250398004234051)
  ·
    refine ⟨29300353683375597006351077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19533569122250398004234051 29300353683375597006351077)
    ·
      refine ⟨5493816315632924438690827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29300353683375597006351077 5493816315632924438690827)
      ·
        refine ⟨8240724473449386658036241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5493816315632924438690827 8240724473449386658036241)
        ·
          refine ⟨6180543355087039993527181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8240724473449386658036241 6180543355087039993527181)
          ·
            refine ⟨2317703758157639997572693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6180543355087039993527181 2317703758157639997572693)
            ·
              refine ⟨27160590915909843721555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2317703758157639997572693 27160590915909843721555)
              ·
                rfl

theorem cell22_2142250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 8].length) (baseStart_2142250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142250 prefixEnd_2142250 := by exact prefixLift 2142250
  have htrace : WordTrace (prefixWord ++ tailWord_2142250) baseStart_2142250 baseEnd_2142250 := by
    simpa [prefixWord, tailWord_2142250, baseEnd_2142250] using wordTrace_append hprefix tailTrace_2142250
  have hstable : (prefixWord ++ tailWord_2142250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142250).length < 2 ^ (prefixWord ++ tailWord_2142250).sum := by decide
  have hdescent : baseEnd_2142250 < baseStart_2142250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142316 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_2142316 : Nat := 118140960795 + 2142316 * 2 ^ 59
def prefixEnd_2142316 : Nat := 4983230072969 + 3 ^ 40 * 2142316 * 2
def baseEnd_2142316 : Nat := 733358547878363608331783

theorem tailTrace_2142316 : CollatzResearch.WordTrace tailWord_2142316 prefixEnd_2142316 733358547878363608331783 := by
  unfold tailWord_2142316
  simp only [CollatzResearch.WordTrace]
  refine ⟨39068341853381242644419401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52091122471174990192559201 39068341853381242644419401)
  ·
    refine ⟨29301256390035931983314551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39068341853381242644419401 29301256390035931983314551)
    ·
      refine ⟨43951884585053897974971827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29301256390035931983314551 43951884585053897974971827)
      ·
        refine ⟨65927826877580846962457741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43951884585053897974971827 65927826877580846962457741)
        ·
          refine ⟨24722935079092817610921653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65927826877580846962457741 24722935079092817610921653)
          ·
            refine ⟨2317775163664951651023905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24722935079092817610921653 2317775163664951651023905)
            ·
              refine ⟨1738331372748713738267929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317775163664951651023905 1738331372748713738267929)
              ·
                refine ⟨1303748529561535303700947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738331372748713738267929 1303748529561535303700947)
                ·
                  refine ⟨1955622794342302955551421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303748529561535303700947 1955622794342302955551421)
                  ·
                    refine ⟨733358547878363608331783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955622794342302955551421 733358547878363608331783)
                    ·
                      rfl

theorem cell22_2142316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_2142316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142316 prefixEnd_2142316 := by exact prefixLift 2142316
  have htrace : WordTrace (prefixWord ++ tailWord_2142316) baseStart_2142316 baseEnd_2142316 := by
    simpa [prefixWord, tailWord_2142316, baseEnd_2142316] using wordTrace_append hprefix tailTrace_2142316
  have hstable : (prefixWord ++ tailWord_2142316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142316).length < 2 ^ (prefixWord ++ tailWord_2142316).sum := by decide
  have hdescent : baseEnd_2142316 < baseStart_2142316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142340 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_2142340 : Nat := 118140960795 + 2142340 * 2 ^ 59
def prefixEnd_2142340 : Nat := 4983230072969 + 3 ^ 40 * 2142340 * 2
def baseEnd_2142340 : Nat := 244455587856278515243903

theorem tailTrace_2142340 : CollatzResearch.WordTrace tailWord_2142340 prefixEnd_2142340 244455587856278515243903 := by
  unfold tailWord_2142340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39068779529337768693856237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52091706039117024925141649 39068779529337768693856237)
  ·
    refine ⟨14650792323501663260196089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39068779529337768693856237 14650792323501663260196089)
    ·
      refine ⟨10988094242626247445147067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14650792323501663260196089 10988094242626247445147067)
      ·
        refine ⟨16482141363939371167720601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10988094242626247445147067 16482141363939371167720601)
        ·
          refine ⟨12361606022954528375790451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16482141363939371167720601 12361606022954528375790451)
          ·
            refine ⟨18542409034431792563685677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12361606022954528375790451 18542409034431792563685677)
            ·
              refine ⟨6953403387911922211382129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18542409034431792563685677 6953403387911922211382129)
              ·
                refine ⟨5215052540933941658536597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6953403387911922211382129 5215052540933941658536597)
                ·
                  refine ⟨244455587856278515243903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5215052540933941658536597 244455587856278515243903)
                  ·
                    rfl

theorem cell22_2142340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_2142340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142340 prefixEnd_2142340 := by exact prefixLift 2142340
  have htrace : WordTrace (prefixWord ++ tailWord_2142340) baseStart_2142340 baseEnd_2142340 := by
    simpa [prefixWord, tailWord_2142340, baseEnd_2142340] using wordTrace_append hprefix tailTrace_2142340
  have hstable : (prefixWord ++ tailWord_2142340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142340).length < 2 ^ (prefixWord ++ tailWord_2142340).sum := by decide
  have hdescent : baseEnd_2142340 < baseStart_2142340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142355 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 4, 3]
def baseStart_2142355 : Nat := 118140960795 + 2142355 * 2 ^ 59
def prefixEnd_2142355 : Nat := 4983230072969 + 3 ^ 40 * 2142355 * 2
def baseEnd_2142355 : Nat := 733371898375380506606663

theorem tailTrace_2142355 : CollatzResearch.WordTrace tailWord_2142355 prefixEnd_2142355 733371898375380506606663 := by
  unfold tailWord_2142355
  simp only [CollatzResearch.WordTrace]
  refine ⟨78138106153621194949508519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52092070769080796633005679 78138106153621194949508519)
  ·
    refine ⟨117207159230431792424262779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78138106153621194949508519 117207159230431792424262779)
    ·
      refine ⟨175810738845647688636394169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117207159230431792424262779 175810738845647688636394169)
      ·
        refine ⟨131858054134235766477295627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175810738845647688636394169 131858054134235766477295627)
        ·
          refine ⟨197787081201353649715943441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131858054134235766477295627 197787081201353649715943441)
          ·
            refine ⟨148340310901015237286957581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197787081201353649715943441 148340310901015237286957581)
            ·
              refine ⟨55627616587880713982609093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148340310901015237286957581 55627616587880713982609093)
              ·
                refine ⟨10430178110227633871739205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55627616587880713982609093 10430178110227633871739205)
                ·
                  refine ⟨1955658395667681350951101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10430178110227633871739205 1955658395667681350951101)
                  ·
                    refine ⟨733371898375380506606663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955658395667681350951101 733371898375380506606663)
                    ·
                      rfl

theorem cell22_2142355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].length) (baseStart_2142355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142355 prefixEnd_2142355 := by exact prefixLift 2142355
  have htrace : WordTrace (prefixWord ++ tailWord_2142355) baseStart_2142355 baseEnd_2142355 := by
    simpa [prefixWord, tailWord_2142355, baseEnd_2142355] using wordTrace_append hprefix tailTrace_2142355
  have hstable : (prefixWord ++ tailWord_2142355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142355).length < 2 ^ (prefixWord ++ tailWord_2142355).sum := by decide
  have hdescent : baseEnd_2142355 < baseStart_2142355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142357 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 4]
def baseStart_2142357 : Nat := 118140960795 + 2142357 * 2 ^ 59
def prefixEnd_2142357 : Nat := 4983230072969 + 3 ^ 40 * 2142357 * 2
def baseEnd_2142357 : Nat := 244457527672084389352219

theorem tailTrace_2142357 : CollatzResearch.WordTrace tailWord_2142357 prefixEnd_2142357 244457527672084389352219 := by
  unfold tailWord_2142357
  simp only [CollatzResearch.WordTrace]
  refine ⟨78138179099613949291081325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52092119399742632860720883 78138179099613949291081325)
  ·
    refine ⟨29301817162355230984155497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78138179099613949291081325 29301817162355230984155497)
    ·
      refine ⟨21976362871766423238116623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29301817162355230984155497 21976362871766423238116623)
      ·
        refine ⟨32964544307649634857174935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21976362871766423238116623 32964544307649634857174935)
        ·
          refine ⟨49446816461474452285762403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32964544307649634857174935 49446816461474452285762403)
          ·
            refine ⟨74170224692211678428643605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49446816461474452285762403 74170224692211678428643605)
            ·
              refine ⟨3476729282447422426342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74170224692211678428643605 3476729282447422426342669)
              ·
                refine ⟨1303773480917783409878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3476729282447422426342669 1303773480917783409878501)
                ·
                  refine ⟨244457527672084389352219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303773480917783409878501 244457527672084389352219)
                  ·
                    rfl

theorem cell22_2142357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_2142357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142357 prefixEnd_2142357 := by exact prefixLift 2142357
  have htrace : WordTrace (prefixWord ++ tailWord_2142357) baseStart_2142357 baseEnd_2142357 := by
    simpa [prefixWord, tailWord_2142357, baseEnd_2142357] using wordTrace_append hprefix tailTrace_2142357
  have hstable : (prefixWord ++ tailWord_2142357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142357).length < 2 ^ (prefixWord ++ tailWord_2142357).sum := by decide
  have hdescent : baseEnd_2142357 < baseStart_2142357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142447 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 5]
def baseStart_2142447 : Nat := 118140960795 + 2142447 * 2 ^ 59
def prefixEnd_2142447 : Nat := 4983230072969 + 3 ^ 40 * 2142447 * 2
def baseEnd_2142447 : Nat := 244467797285174311102127

theorem tailTrace_2142447 : CollatzResearch.WordTrace tailWord_2142447 prefixEnd_2142447 244467797285174311102127 := by
  unfold tailWord_2142447
  simp only [CollatzResearch.WordTrace]
  refine ⟨78141461669287894661857595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52094307779525263107905063 78141461669287894661857595)
  ·
    refine ⟨117212192503931841992786393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78141461669287894661857595 117212192503931841992786393)
    ·
      refine ⟨87909144377948881494589795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117212192503931841992786393 87909144377948881494589795)
      ·
        refine ⟨131863716566923322241884693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87909144377948881494589795 131863716566923322241884693)
        ·
          refine ⟨6181111714074530730088345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 131863716566923322241884693 6181111714074530730088345)
          ·
            refine ⟨4635833785555898047566259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181111714074530730088345 4635833785555898047566259)
            ·
              refine ⟨6953750678333847071349389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635833785555898047566259 6953750678333847071349389)
              ·
                refine ⟨2607656504375192651756021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6953750678333847071349389 2607656504375192651756021)
                ·
                  refine ⟨244467797285174311102127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607656504375192651756021 244467797285174311102127)
                  ·
                    rfl

theorem cell22_2142447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].length) (baseStart_2142447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142447 prefixEnd_2142447 := by exact prefixLift 2142447
  have htrace : WordTrace (prefixWord ++ tailWord_2142447) baseStart_2142447 baseEnd_2142447 := by
    simpa [prefixWord, tailWord_2142447, baseEnd_2142447] using wordTrace_append hprefix tailTrace_2142447
  have hstable : (prefixWord ++ tailWord_2142447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142447).length < 2 ^ (prefixWord ++ tailWord_2142447).sum := by decide
  have hdescent : baseEnd_2142447 < baseStart_2142447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142520 : List Nat := [2, 1, 2, 1, 3, 1, 2, 10]
def baseStart_2142520 : Nat := 118140960795 + 2142520 * 2 ^ 59
def prefixEnd_2142520 : Nat := 4983230072969 + 3 ^ 40 * 2142520 * 2
def baseEnd_2142520 : Nat := 81492042360819452914573

theorem tailTrace_2142520 : CollatzResearch.WordTrace tailWord_2142520 prefixEnd_2142520 81492042360819452914573 := by
  unfold tailWord_2142520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072062099011714064632507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52096082798682285419510009 39072062099011714064632507)
  ·
    refine ⟨58608093148517571096948761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39072062099011714064632507 58608093148517571096948761)
    ·
      refine ⟨43956069861388178322711571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58608093148517571096948761 43956069861388178322711571)
      ·
        refine ⟨65934104792082267484067357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43956069861388178322711571 65934104792082267484067357)
        ·
          refine ⟨24725289297030850306525259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65934104792082267484067357 24725289297030850306525259)
          ·
            refine ⟨37087933945546275459787889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24725289297030850306525259 37087933945546275459787889)
            ·
              refine ⟨27815950459159706594840917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37087933945546275459787889 27815950459159706594840917)
              ·
                refine ⟨81492042360819452914573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27815950459159706594840917 81492042360819452914573)
                ·
                  rfl

theorem cell22_2142520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_2142520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142520 prefixEnd_2142520 := by exact prefixLift 2142520
  have htrace : WordTrace (prefixWord ++ tailWord_2142520) baseStart_2142520 baseEnd_2142520 := by
    simpa [prefixWord, tailWord_2142520, baseEnd_2142520] using wordTrace_append hprefix tailTrace_2142520
  have hstable : (prefixWord ++ tailWord_2142520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142520).length < 2 ^ (prefixWord ++ tailWord_2142520).sum := by decide
  have hdescent : baseEnd_2142520 < baseStart_2142520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142522 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_2142522 : Nat := 118140960795 + 2142522 * 2 ^ 59
def prefixEnd_2142522 : Nat := 4983230072969 + 3 ^ 40 * 2142522 * 2
def baseEnd_2142522 : Nat := 733429065888247737681151

theorem tailTrace_2142522 : CollatzResearch.WordTrace tailWord_2142522 prefixEnd_2142522 733429065888247737681151 := by
  unfold tailWord_2142522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536049286004045617709455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52096131429344121647225213 19536049286004045617709455)
  ·
    refine ⟨29304073929006068426564183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19536049286004045617709455 29304073929006068426564183)
    ·
      refine ⟨43956110893509102639846275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29304073929006068426564183 43956110893509102639846275)
      ·
        refine ⟨65934166340263653959769413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43956110893509102639846275 65934166340263653959769413)
        ·
          refine ⟨12362656188799435117456765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65934166340263653959769413 12362656188799435117456765)
          ·
            refine ⟨4635996070799788169046287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12362656188799435117456765 4635996070799788169046287)
            ·
              refine ⟨6953994106199682253569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635996070799788169046287 6953994106199682253569431)
              ·
                refine ⟨10430991159299523380354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953994106199682253569431 10430991159299523380354147)
                ·
                  refine ⟨15646486738949285070531221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10430991159299523380354147 15646486738949285070531221)
                  ·
                    refine ⟨733429065888247737681151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15646486738949285070531221 733429065888247737681151)
                    ·
                      rfl

theorem cell22_2142522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_2142522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142522 prefixEnd_2142522 := by exact prefixLift 2142522
  have htrace : WordTrace (prefixWord ++ tailWord_2142522) baseStart_2142522 baseEnd_2142522 := by
    simpa [prefixWord, tailWord_2142522, baseEnd_2142522] using wordTrace_append hprefix tailTrace_2142522
  have hstable : (prefixWord ++ tailWord_2142522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142522).length < 2 ^ (prefixWord ++ tailWord_2142522).sum := by decide
  have hdescent : baseEnd_2142522 < baseStart_2142522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142526 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2142526 : Nat := 118140960795 + 2142526 * 2 ^ 59
def prefixEnd_2142526 : Nat := 4983230072969 + 3 ^ 40 * 2142526 * 2
def baseEnd_2142526 : Nat := 244476811723331020193713

theorem tailTrace_2142526 : CollatzResearch.WordTrace tailWord_2142526 prefixEnd_2142526 244476811723331020193713 := by
  unfold tailWord_2142526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768042879500211394247929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52096228690667794102655621 9768042879500211394247929)
  ·
    refine ⟨7326032159625158545685947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9768042879500211394247929 7326032159625158545685947)
    ·
      refine ⟨10989048239437737818528921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326032159625158545685947 10989048239437737818528921)
      ·
        refine ⟨8241786179578303363896691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10989048239437737818528921 8241786179578303363896691)
        ·
          refine ⟨12362679269367455045845037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241786179578303363896691 12362679269367455045845037)
          ·
            refine ⟨4636004726012795642191889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12362679269367455045845037 4636004726012795642191889)
            ·
              refine ⟨3477003544509596731643917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636004726012795642191889 3477003544509596731643917)
              ·
                refine ⟨1303876329191098774366469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3477003544509596731643917 1303876329191098774366469)
                ·
                  refine ⟨244476811723331020193713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303876329191098774366469 244476811723331020193713)
                  ·
                    rfl

theorem cell22_2142526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2142526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142526 prefixEnd_2142526 := by exact prefixLift 2142526
  have htrace : WordTrace (prefixWord ++ tailWord_2142526) baseStart_2142526 baseEnd_2142526 := by
    simpa [prefixWord, tailWord_2142526, baseEnd_2142526] using wordTrace_append hprefix tailTrace_2142526
  have hstable : (prefixWord ++ tailWord_2142526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142526).length < 2 ^ (prefixWord ++ tailWord_2142526).sum := by decide
  have hdescent : baseEnd_2142526 < baseStart_2142526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142603 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 1, 3]
def baseStart_2142603 : Nat := 118140960795 + 2142603 * 2 ^ 59
def prefixEnd_2142603 : Nat := 4983230072969 + 3 ^ 40 * 2142603 * 2
def baseEnd_2142603 : Nat := 733456793843590526405903

theorem tailTrace_2142603 : CollatzResearch.WordTrace tailWord_2142603 prefixEnd_2142603 733456793843590526405903 := by
  unfold tailWord_2142603
  simp only [CollatzResearch.WordTrace]
  refine ⟨78147151456722733304536463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52098100971148488869690975 78147151456722733304536463)
  ·
    refine ⟨117220727185084099956804695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78147151456722733304536463 117220727185084099956804695)
    ·
      refine ⟨175831090777626149935207043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117220727185084099956804695 175831090777626149935207043)
      ·
        refine ⟨263746636166439224902810565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175831090777626149935207043 263746636166439224902810565)
        ·
          refine ⟨49452494281207354669276981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 263746636166439224902810565 49452494281207354669276981)
          ·
            refine ⟨4636171338863189500244717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49452494281207354669276981 4636171338863189500244717)
            ·
              refine ⟨1738564252073696062591769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4636171338863189500244717 1738564252073696062591769)
              ·
                refine ⟨1303923189055272046943827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738564252073696062591769 1303923189055272046943827)
                ·
                  refine ⟨1955884783582908070415741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303923189055272046943827 1955884783582908070415741)
                  ·
                    refine ⟨733456793843590526405903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955884783582908070415741 733456793843590526405903)
                    ·
                      rfl

theorem cell22_2142603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 3].length) (baseStart_2142603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142603 prefixEnd_2142603 := by exact prefixLift 2142603
  have htrace : WordTrace (prefixWord ++ tailWord_2142603) baseStart_2142603 baseEnd_2142603 := by
    simpa [prefixWord, tailWord_2142603, baseEnd_2142603] using wordTrace_append hprefix tailTrace_2142603
  have hstable : (prefixWord ++ tailWord_2142603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142603).length < 2 ^ (prefixWord ++ tailWord_2142603).sum := by decide
  have hdescent : baseEnd_2142603 < baseStart_2142603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142616 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_2142616 : Nat := 118140960795 + 2142616 * 2 ^ 59
def prefixEnd_2142616 : Nat := 4983230072969 + 3 ^ 40 * 2142616 * 2
def baseEnd_2142616 : Nat := 244487081336420941943621

theorem tailTrace_2142616 : CollatzResearch.WordTrace tailWord_2142616 prefixEnd_2142616 244487081336420941943621 := by
  unfold tailWord_2142616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39073812802837818262379851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52098417070450424349839801 39073812802837818262379851)
  ·
    refine ⟨58610719204256727393569777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39073812802837818262379851 58610719204256727393569777)
    ·
      refine ⟨43958039403192545545177333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58610719204256727393569777 43958039403192545545177333)
      ·
        refine ⟨4121066194049301144860375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43958039403192545545177333 4121066194049301144860375)
        ·
          refine ⟨6181599291073951717290563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121066194049301144860375 6181599291073951717290563)
          ·
            refine ⟨9272398936610927575935845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181599291073951717290563 9272398936610927575935845)
            ·
              refine ⟨1738574800614548920487971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9272398936610927575935845 1738574800614548920487971)
              ·
                refine ⟨2607862200921823380731957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738574800614548920487971 2607862200921823380731957)
                ·
                  refine ⟨244487081336420941943621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607862200921823380731957 244487081336420941943621)
                  ·
                    rfl

theorem cell22_2142616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_2142616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142616 prefixEnd_2142616 := by exact prefixLift 2142616
  have htrace : WordTrace (prefixWord ++ tailWord_2142616) baseStart_2142616 baseEnd_2142616 := by
    simpa [prefixWord, tailWord_2142616, baseEnd_2142616] using wordTrace_append hprefix tailTrace_2142616
  have hstable : (prefixWord ++ tailWord_2142616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142616).length < 2 ^ (prefixWord ++ tailWord_2142616).sum := by decide
  have hdescent : baseEnd_2142616 < baseStart_2142616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142676 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2142676 : Nat := 118140960795 + 2142676 * 2 ^ 59
def prefixEnd_2142676 : Nat := 4983230072969 + 3 ^ 40 * 2142676 * 2
def baseEnd_2142676 : Nat := 733481783235442669330679

theorem tailTrace_2142676 : CollatzResearch.WordTrace tailWord_2142676 prefixEnd_2142676 733481783235442669330679 := by
  unfold tailWord_2142676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39074906992729133385971941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52099875990305511181295921 39074906992729133385971941)
  ·
    refine ⟨7326545061136712509869739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39074906992729133385971941 7326545061136712509869739)
    ·
      refine ⟨10989817591705068764804609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326545061136712509869739 10989817591705068764804609)
      ·
        refine ⟨8242363193778801573603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10989817591705068764804609 8242363193778801573603457)
        ·
          refine ⟨6181772395334101180202593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242363193778801573603457 6181772395334101180202593)
          ·
            refine ⟨4636329296500575885151945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181772395334101180202593 4636329296500575885151945)
            ·
              refine ⟨3477246972375431913863959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636329296500575885151945 3477246972375431913863959)
              ·
                refine ⟨5215870458563147870795939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477246972375431913863959 5215870458563147870795939)
                ·
                  refine ⟨7823805687844721806193909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215870458563147870795939 7823805687844721806193909)
                  ·
                    refine ⟨733481783235442669330679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7823805687844721806193909 733481783235442669330679)
                    ·
                      rfl

theorem cell22_2142676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2142676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142676 prefixEnd_2142676 := by exact prefixLift 2142676
  have htrace : WordTrace (prefixWord ++ tailWord_2142676) baseStart_2142676 baseEnd_2142676 := by
    simpa [prefixWord, tailWord_2142676, baseEnd_2142676] using wordTrace_append hprefix tailTrace_2142676
  have hstable : (prefixWord ++ tailWord_2142676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142676).length < 2 ^ (prefixWord ++ tailWord_2142676).sum := by decide
  have hdescent : baseEnd_2142676 < baseStart_2142676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142689 : List Nat := [1, 2, 3, 1, 2, 2, 5, 6]
def baseStart_2142689 : Nat := 118140960795 + 2142689 * 2 ^ 59
def prefixEnd_2142689 : Nat := 4983230072969 + 3 ^ 40 * 2142689 * 2
def baseEnd_2142689 : Nat := 81498470377901663195071

theorem tailTrace_2142689 : CollatzResearch.WordTrace tailWord_2142689 prefixEnd_2142689 81498470377901663195071 := by
  unfold tailWord_2142689
  simp only [CollatzResearch.WordTrace]
  refine ⟨78150288134411169992167121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52100192089607446661444747 78150288134411169992167121)
  ·
    refine ⟨58612716100808377494125341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78150288134411169992167121 58612716100808377494125341)
    ·
      refine ⟨21979768537803141560297003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58612716100808377494125341 21979768537803141560297003)
      ·
        refine ⟨32969652806704712340445505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21979768537803141560297003 32969652806704712340445505)
        ·
          refine ⟨24727239605028534255334129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32969652806704712340445505 24727239605028534255334129)
          ·
            refine ⟨18545429703771400691500597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24727239605028534255334129 18545429703771400691500597)
            ·
              refine ⟨1738634034728568814828181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18545429703771400691500597 1738634034728568814828181)
              ·
                refine ⟨81498470377901663195071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1738634034728568814828181 81498470377901663195071)
                ·
                  rfl

theorem cell22_2142689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 6].length) (baseStart_2142689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142689 prefixEnd_2142689 := by exact prefixLift 2142689
  have htrace : WordTrace (prefixWord ++ tailWord_2142689) baseStart_2142689 baseEnd_2142689 := by
    simpa [prefixWord, tailWord_2142689, baseEnd_2142689] using wordTrace_append hprefix tailTrace_2142689
  have hstable : (prefixWord ++ tailWord_2142689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142689).length < 2 ^ (prefixWord ++ tailWord_2142689).sum := by decide
  have hdescent : baseEnd_2142689 < baseStart_2142689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142704 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_2142704 : Nat := 118140960795 + 2142704 * 2 ^ 59
def prefixEnd_2142704 : Nat := 4983230072969 + 3 ^ 40 * 2142704 * 2
def baseEnd_2142704 : Nat := 733491368207659929630593

theorem tailTrace_2142704 : CollatzResearch.WordTrace tailWord_2142704 prefixEnd_2142704 733491368207659929630593 := by
  unfold tailWord_2142704
  simp only [CollatzResearch.WordTrace]
  refine ⟨39075417614678413776981583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52100556819571218369308777 39075417614678413776981583)
  ·
    refine ⟨58613126422017620665472375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39075417614678413776981583 58613126422017620665472375)
    ·
      refine ⟨87919689633026430998208563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58613126422017620665472375 87919689633026430998208563)
      ·
        refine ⟨131879534449539646497312845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87919689633026430998208563 131879534449539646497312845)
        ·
          refine ⟨49454825418577367436492317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131879534449539646497312845 49454825418577367436492317)
          ·
            refine ⟨18545559531966512788684619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49454825418577367436492317 18545559531966512788684619)
            ·
              refine ⟨27818339297949769183026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18545559531966512788684619 27818339297949769183026929)
              ·
                refine ⟨20863754473462326887270197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27818339297949769183026929 20863754473462326887270197)
                ·
                  refine ⟨1955976981887093145681581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20863754473462326887270197 1955976981887093145681581)
                  ·
                    refine ⟨733491368207659929630593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955976981887093145681581 733491368207659929630593)
                    ·
                      rfl

theorem cell22_2142704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_2142704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142704 prefixEnd_2142704 := by exact prefixLift 2142704
  have htrace : WordTrace (prefixWord ++ tailWord_2142704) baseStart_2142704 baseEnd_2142704 := by
    simpa [prefixWord, tailWord_2142704, baseEnd_2142704] using wordTrace_append hprefix tailTrace_2142704
  have hstable : (prefixWord ++ tailWord_2142704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142704).length < 2 ^ (prefixWord ++ tailWord_2142704).sum := by decide
  have hdescent : baseEnd_2142704 < baseStart_2142704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142721 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2142721 : Nat := 118140960795 + 2142721 * 2 ^ 59
def prefixEnd_2142721 : Nat := 4983230072969 + 3 ^ 40 * 2142721 * 2
def baseEnd_2142721 : Nat := 733497187655077551955541

theorem tailTrace_2142721 : CollatzResearch.WordTrace tailWord_2142721 prefixEnd_2142721 733497187655077551955541 := by
  unfold tailWord_2142721
  simp only [CollatzResearch.WordTrace]
  refine ⟨78151455270295239457332017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52100970180196826304888011 78151455270295239457332017)
  ·
    refine ⟨58613591452721429592999013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78151455270295239457332017 58613591452721429592999013)
    ·
      refine ⟨10990048397385268048687315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58613591452721429592999013 10990048397385268048687315)
      ·
        refine ⟨16485072596077902073030973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10990048397385268048687315 16485072596077902073030973)
        ·
          refine ⟨6181902223529213277386615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16485072596077902073030973 6181902223529213277386615)
          ·
            refine ⟨9272853335293819916079923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181902223529213277386615 9272853335293819916079923)
            ·
              refine ⟨13909280002940729874119885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9272853335293819916079923 13909280002940729874119885)
              ·
                refine ⟨5215980001102773702794957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13909280002940729874119885 5215980001102773702794957)
                ·
                  refine ⟨1955992500413540138548109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215980001102773702794957 1955992500413540138548109)
                  ·
                    refine ⟨733497187655077551955541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1955992500413540138548109 733497187655077551955541)
                    ·
                      rfl

theorem cell22_2142721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2142721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142721 prefixEnd_2142721 := by exact prefixLift 2142721
  have htrace : WordTrace (prefixWord ++ tailWord_2142721) baseStart_2142721 baseEnd_2142721 := by
    simpa [prefixWord, tailWord_2142721, baseEnd_2142721] using wordTrace_append hprefix tailTrace_2142721
  have hstable : (prefixWord ++ tailWord_2142721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142721).length < 2 ^ (prefixWord ++ tailWord_2142721).sum := by decide
  have hdescent : baseEnd_2142721 < baseStart_2142721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142747 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_2142747 : Nat := 118140960795 + 2142747 * 2 ^ 59
def prefixEnd_2142747 : Nat := 4983230072969 + 3 ^ 40 * 2142747 * 2
def baseEnd_2142747 : Nat := 733506087986422150805461

theorem tailTrace_2142747 : CollatzResearch.WordTrace tailWord_2142747 prefixEnd_2142747 733506087986422150805461 := by
  unfold tailWord_2142747
  simp only [CollatzResearch.WordTrace]
  refine ⟨78152403568201045897778495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52101602378800697265185663 78152403568201045897778495)
  ·
    refine ⟨117228605352301568846667743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78152403568201045897778495 117228605352301568846667743)
    ·
      refine ⟨175842908028452353270001615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117228605352301568846667743 175842908028452353270001615)
      ·
        refine ⟨263764362042678529905002423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175842908028452353270001615 263764362042678529905002423)
        ·
          refine ⟨395646543064017794857503635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263764362042678529905002423 395646543064017794857503635)
          ·
            refine ⟨593469814596026692286255453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395646543064017794857503635 593469814596026692286255453)
            ·
              refine ⟨222551180473510009607345795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593469814596026692286255453 222551180473510009607345795)
              ·
                refine ⟨333826770710265014411018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222551180473510009607345795 333826770710265014411018693)
                ·
                  refine ⟨62592519508174690202066005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333826770710265014411018693 62592519508174690202066005)
                  ·
                    refine ⟨733506087986422150805461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62592519508174690202066005 733506087986422150805461)
                    ·
                      rfl

theorem cell22_2142747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_2142747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142747 prefixEnd_2142747 := by exact prefixLift 2142747
  have htrace : WordTrace (prefixWord ++ tailWord_2142747) baseStart_2142747 baseEnd_2142747 := by
    simpa [prefixWord, tailWord_2142747, baseEnd_2142747] using wordTrace_append hprefix tailTrace_2142747
  have hstable : (prefixWord ++ tailWord_2142747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142747).length < 2 ^ (prefixWord ++ tailWord_2142747).sum := by decide
  have hdescent : baseEnd_2142747 < baseStart_2142747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142755 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 1, 3]
def baseStart_2142755 : Nat := 118140960795 + 2142755 * 2 ^ 59
def prefixEnd_2142755 : Nat := 4983230072969 + 3 ^ 40 * 2142755 * 2
def baseEnd_2142755 : Nat := 733508826549912796605437

theorem tailTrace_2142755 : CollatzResearch.WordTrace tailWord_2142755 prefixEnd_2142755 733508826549912796605437 := by
  unfold tailWord_2142755
  simp only [CollatzResearch.WordTrace]
  refine ⟨78152695352172063264069719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52101796901448042176046479 78152695352172063264069719)
  ·
    refine ⟨117229043028258094896104579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78152695352172063264069719 117229043028258094896104579)
    ·
      refine ⟨175843564542387142344156869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117229043028258094896104579 175843564542387142344156869)
      ·
        refine ⟨32970668351697589189529413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175843564542387142344156869 32970668351697589189529413)
        ·
          refine ⟨6182000315943297973036765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32970668351697589189529413 6182000315943297973036765)
          ·
            refine ⟨2318250118478736739888787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182000315943297973036765 2318250118478736739888787)
            ·
              refine ⟨3477375177718105109833181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318250118478736739888787 3477375177718105109833181)
              ·
                refine ⟨1304015691644289416187443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3477375177718105109833181 1304015691644289416187443)
                ·
                  refine ⟨1956023537466434124281165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304015691644289416187443 1956023537466434124281165)
                  ·
                    refine ⟨733508826549912796605437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956023537466434124281165 733508826549912796605437)
                    ·
                      rfl

theorem cell22_2142755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 3].length) (baseStart_2142755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142755 prefixEnd_2142755 := by exact prefixLift 2142755
  have htrace : WordTrace (prefixWord ++ tailWord_2142755) baseStart_2142755 baseEnd_2142755 := by
    simpa [prefixWord, tailWord_2142755, baseEnd_2142755] using wordTrace_append hprefix tailTrace_2142755
  have hstable : (prefixWord ++ tailWord_2142755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142755).length < 2 ^ (prefixWord ++ tailWord_2142755).sum := by decide
  have hdescent : baseEnd_2142755 < baseStart_2142755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142772 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2142772 : Nat := 118140960795 + 2142772 * 2 ^ 59
def prefixEnd_2142772 : Nat := 4983230072969 + 3 ^ 40 * 2142772 * 2
def baseEnd_2142772 : Nat := 733514645997330418930385

theorem tailTrace_2142772 : CollatzResearch.WordTrace tailWord_2142772 prefixEnd_2142772 733514645997330418930385 := by
  unfold tailWord_2142772
  simp only [CollatzResearch.WordTrace]
  refine ⟨39076657696555237583719285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52102210262073650111625713 39076657696555237583719285)
  ·
    refine ⟨3663436659052053523473683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39076657696555237583719285 3663436659052053523473683)
    ·
      refine ⟨5495154988578080285210525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663436659052053523473683 5495154988578080285210525)
      ·
        refine ⟨2060683120716780106953947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5495154988578080285210525 2060683120716780106953947)
        ·
          refine ⟨3091024681075170160430921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060683120716780106953947 3091024681075170160430921)
          ·
            refine ⟨2318268510806377620323191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3091024681075170160430921 2318268510806377620323191)
            ·
              refine ⟨3477402766209566430484787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318268510806377620323191 3477402766209566430484787)
              ·
                refine ⟨5216104149314349645727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477402766209566430484787 5216104149314349645727181)
                ·
                  refine ⟨1956039055992881117147693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5216104149314349645727181 1956039055992881117147693)
                  ·
                    refine ⟨733514645997330418930385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956039055992881117147693 733514645997330418930385)
                    ·
                      rfl

theorem cell22_2142772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2142772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142772 prefixEnd_2142772 := by exact prefixLift 2142772
  have htrace : WordTrace (prefixWord ++ tailWord_2142772) baseStart_2142772 baseEnd_2142772 := by
    simpa [prefixWord, tailWord_2142772, baseEnd_2142772] using wordTrace_append hprefix tailTrace_2142772
  have hstable : (prefixWord ++ tailWord_2142772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142772).length < 2 ^ (prefixWord ++ tailWord_2142772).sum := by decide
  have hdescent : baseEnd_2142772 < baseStart_2142772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142824 : List Nat := [2, 1, 4, 3, 12]
def baseStart_2142824 : Nat := 118140960795 + 2142824 * 2 ^ 59
def prefixEnd_2142824 : Nat := 4983230072969 + 3 ^ 40 * 2142824 * 2
def baseEnd_2142824 : Nat := 3018652043868393484075

theorem tailTrace_2142824 : CollatzResearch.WordTrace tailWord_2142824 prefixEnd_2142824 3018652043868393484075 := by
  unfold tailWord_2142824
  simp only [CollatzResearch.WordTrace]
  refine ⟨39077605994461044024165763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52103474659281392032221017 39077605994461044024165763)
  ·
    refine ⟨58616408991691566036248645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39077605994461044024165763 58616408991691566036248645)
    ·
      refine ⟨10990576685942168631796621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58616408991691566036248645 10990576685942168631796621)
      ·
        refine ⟨4121466257228313236923733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10990576685942168631796621 4121466257228313236923733)
        ·
          refine ⟨3018652043868393484075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4121466257228313236923733 3018652043868393484075)
          ·
            rfl

theorem cell22_2142824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 12].length) (baseStart_2142824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142824 prefixEnd_2142824 := by exact prefixLift 2142824
  have htrace : WordTrace (prefixWord ++ tailWord_2142824) baseStart_2142824 baseEnd_2142824 := by
    simpa [prefixWord, tailWord_2142824, baseEnd_2142824] using wordTrace_append hprefix tailTrace_2142824
  have hstable : (prefixWord ++ tailWord_2142824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142824).length < 2 ^ (prefixWord ++ tailWord_2142824).sum := by decide
  have hdescent : baseEnd_2142824 < baseStart_2142824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142826 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2142826 : Nat := 118140960795 + 2142826 * 2 ^ 59
def prefixEnd_2142826 : Nat := 4983230072969 + 3 ^ 40 * 2142826 * 2
def baseEnd_2142826 : Nat := 733533131300892278080219

theorem tailTrace_2142826 : CollatzResearch.WordTrace tailWord_2142826 prefixEnd_2142826 733533131300892278080219 := by
  unfold tailWord_2142826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538821233728710597476083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52103523289943228259936221 19538821233728710597476083)
  ·
    refine ⟨29308231850593065896214125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19538821233728710597476083 29308231850593065896214125)
    ·
      refine ⟨10990586943972399711080297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29308231850593065896214125 10990586943972399711080297)
      ·
        refine ⟨8242940207979299783310223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10990586943972399711080297 8242940207979299783310223)
        ·
          refine ⟨12364410311968949674965335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242940207979299783310223 12364410311968949674965335)
          ·
            refine ⟨18546615467953424512448003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12364410311968949674965335 18546615467953424512448003)
            ·
              refine ⟨27819923201930136768672005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18546615467953424512448003 27819923201930136768672005)
              ·
                refine ⟨5216235600361900644126001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27819923201930136768672005 5216235600361900644126001)
                ·
                  refine ⟨3912176700271425483094501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5216235600361900644126001 3912176700271425483094501)
                  ·
                    refine ⟨733533131300892278080219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3912176700271425483094501 733533131300892278080219)
                    ·
                      rfl

theorem cell22_2142826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2142826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142826 prefixEnd_2142826 := by exact prefixLift 2142826
  have htrace : WordTrace (prefixWord ++ tailWord_2142826) baseStart_2142826 baseEnd_2142826 := by
    simpa [prefixWord, tailWord_2142826, baseEnd_2142826] using wordTrace_append hprefix tailTrace_2142826
  have hstable : (prefixWord ++ tailWord_2142826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142826).length < 2 ^ (prefixWord ++ tailWord_2142826).sum := by decide
  have hdescent : baseEnd_2142826 < baseStart_2142826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142830 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_2142830 : Nat := 118140960795 + 2142830 * 2 ^ 59
def prefixEnd_2142830 : Nat := 4983230072969 + 3 ^ 40 * 2142830 * 2
def baseEnd_2142830 : Nat := 244511500194212533660069

theorem tailTrace_2142830 : CollatzResearch.WordTrace tailWord_2142830 prefixEnd_2142830 244511500194212533660069 := by
  unfold tailWord_2142830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9769428853362543884131243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52103620551266900715366629 9769428853362543884131243)
  ·
    refine ⟨14654143280043815826196865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9769428853362543884131243 14654143280043815826196865)
    ·
      refine ⟨10990607460032861869647649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14654143280043815826196865 10990607460032861869647649)
      ·
        refine ⟨8242955595024646402235737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10990607460032861869647649 8242955595024646402235737)
        ·
          refine ⟨6182216696268484801676803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242955595024646402235737 6182216696268484801676803)
          ·
            refine ⟨9273325044402727202515205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182216696268484801676803 9273325044402727202515205)
            ·
              refine ⟨1738748445825511350471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9273325044402727202515205 1738748445825511350471601)
              ·
                refine ⟨1304061334369133512853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738748445825511350471601 1304061334369133512853701)
                ·
                  refine ⟨244511500194212533660069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304061334369133512853701 244511500194212533660069)
                  ·
                    rfl

theorem cell22_2142830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_2142830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142830 prefixEnd_2142830 := by exact prefixLift 2142830
  have htrace : WordTrace (prefixWord ++ tailWord_2142830) baseStart_2142830 baseEnd_2142830 := by
    simpa [prefixWord, tailWord_2142830, baseEnd_2142830] using wordTrace_append hprefix tailTrace_2142830
  have hstable : (prefixWord ++ tailWord_2142830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142830).length < 2 ^ (prefixWord ++ tailWord_2142830).sum := by decide
  have hdescent : baseEnd_2142830 < baseStart_2142830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142841 : List Nat := [1, 2, 1, 3, 3, 4, 1, 7]
def baseStart_2142841 : Nat := 118140960795 + 2142841 * 2 ^ 59
def prefixEnd_2142841 : Nat := 4983230072969 + 3 ^ 40 * 2142841 * 2
def baseEnd_2142841 : Nat := 81504251789715248772797

theorem tailTrace_2142841 : CollatzResearch.WordTrace tailWord_2142841 prefixEnd_2142841 81504251789715248772797 := by
  unfold tailWord_2142841
  simp only [CollatzResearch.WordTrace]
  refine ⟨78155832029860499951700377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52103888019906999967800251 78155832029860499951700377)
  ·
    refine ⟨58616874022395374963775283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78155832029860499951700377 58616874022395374963775283)
    ·
      refine ⟨87925311033593062445662925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58616874022395374963775283 87925311033593062445662925)
      ·
        refine ⟨32971991637597398417123597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87925311033593062445662925 32971991637597398417123597)
        ·
          refine ⟨12364496864099024406421349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32971991637597398417123597 12364496864099024406421349)
          ·
            refine ⟨2318343162018567076204003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12364496864099024406421349 2318343162018567076204003)
            ·
              refine ⟨3477514743027850614306005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318343162018567076204003 3477514743027850614306005)
              ·
                refine ⟨81504251789715248772797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3477514743027850614306005 81504251789715248772797)
                ·
                  rfl

theorem cell22_2142841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 7].length) (baseStart_2142841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142841 prefixEnd_2142841 := by exact prefixLift 2142841
  have htrace : WordTrace (prefixWord ++ tailWord_2142841) baseStart_2142841 baseEnd_2142841 := by
    simpa [prefixWord, tailWord_2142841, baseEnd_2142841] using wordTrace_append hprefix tailTrace_2142841
  have hstable : (prefixWord ++ tailWord_2142841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142841).length < 2 ^ (prefixWord ++ tailWord_2142841).sum := by decide
  have hdescent : baseEnd_2142841 < baseStart_2142841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142858 : List Nat := [3, 1, 2, 3, 3, 1, 3, 6]
def baseStart_2142858 : Nat := 118140960795 + 2142858 * 2 ^ 59
def prefixEnd_2142858 : Nat := 4983230072969 + 3 ^ 40 * 2142858 * 2
def baseEnd_2142858 : Nat := 81504898394983873475569

theorem tailTrace_2142858 : CollatzResearch.WordTrace tailWord_2142858 prefixEnd_2142858 81504898394983873475569 := by
  unfold tailWord_2142858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539113017699727963767307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52104301380532607903379485 19539113017699727963767307)
  ·
    refine ⟨29308669526549591945650961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19539113017699727963767307 29308669526549591945650961)
    ·
      refine ⟨21981502144912193959238221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29308669526549591945650961 21981502144912193959238221)
      ·
        refine ⟨8243063304342072734714333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21981502144912193959238221 8243063304342072734714333)
        ·
          refine ⟨3091148739128277275517875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8243063304342072734714333 3091148739128277275517875)
          ·
            refine ⟨4636723108692415913276813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091148739128277275517875 4636723108692415913276813)
            ·
              refine ⟨1738771165759655967478805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4636723108692415913276813 1738771165759655967478805)
              ·
                refine ⟨81504898394983873475569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1738771165759655967478805 81504898394983873475569)
                ·
                  rfl

theorem cell22_2142858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_2142858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142858 prefixEnd_2142858 := by exact prefixLift 2142858
  have htrace : WordTrace (prefixWord ++ tailWord_2142858) baseStart_2142858 baseEnd_2142858 := by
    simpa [prefixWord, tailWord_2142858, baseEnd_2142858] using wordTrace_append hprefix tailTrace_2142858
  have hstable : (prefixWord ++ tailWord_2142858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142858).length < 2 ^ (prefixWord ++ tailWord_2142858).sum := by decide
  have hdescent : baseEnd_2142858 < baseStart_2142858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142948 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_2142948 : Nat := 118140960795 + 2142948 * 2 ^ 59
def prefixEnd_2142948 : Nat := 4983230072969 + 3 ^ 40 * 2142948 * 2
def baseEnd_2142948 : Nat := 244524964798041542176615

theorem tailTrace_2142948 : CollatzResearch.WordTrace tailWord_2142948 prefixEnd_2142948 244524964798041542176615 := by
  unfold tailWord_2142948
  simp only [CollatzResearch.WordTrace]
  refine ⟨39079867320236428612922749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52106489760315238150563665 39079867320236428612922749)
  ·
    refine ⟨14654950245088660729846031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39079867320236428612922749 14654950245088660729846031)
    ·
      refine ⟨21982425367632991094769047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14654950245088660729846031 21982425367632991094769047)
      ·
        refine ⟨32973638051449486642153571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21982425367632991094769047 32973638051449486642153571)
        ·
          refine ⟨49460457077174229963230357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32973638051449486642153571 49460457077174229963230357)
          ·
            refine ⟨2318458925492542029526423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49460457077174229963230357 2318458925492542029526423)
            ·
              refine ⟨3477688388238813044289635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318458925492542029526423 3477688388238813044289635)
              ·
                refine ⟨5216532582358219566434453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477688388238813044289635 5216532582358219566434453)
                ·
                  refine ⟨244524964798041542176615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5216532582358219566434453 244524964798041542176615)
                  ·
                    rfl

theorem cell22_2142948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_2142948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142948 prefixEnd_2142948 := by exact prefixLift 2142948
  have htrace : WordTrace (prefixWord ++ tailWord_2142948) baseStart_2142948 baseEnd_2142948 := by
    simpa [prefixWord, tailWord_2142948, baseEnd_2142948] using wordTrace_append hprefix tailTrace_2142948
  have hstable : (prefixWord ++ tailWord_2142948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142948).length < 2 ^ (prefixWord ++ tailWord_2142948).sum := by decide
  have hdescent : baseEnd_2142948 < baseStart_2142948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142961 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2142961 : Nat := 118140960795 + 2142961 * 2 ^ 59
def prefixEnd_2142961 : Nat := 4983230072969 + 3 ^ 40 * 2142961 * 2
def baseEnd_2142961 : Nat := 733579344559796925954805

theorem tailTrace_2142961 : CollatzResearch.WordTrace tailWord_2142961 prefixEnd_2142961 733579344559796925954805 := by
  unfold tailWord_2142961
  simp only [CollatzResearch.WordTrace]
  refine ⟨78160208789425760446068737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52106805859617173630712491 78160208789425760446068737)
  ·
    refine ⟨58620156592069320334551553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78160208789425760446068737 58620156592069320334551553)
    ·
      refine ⟨43965117444051990250913665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58620156592069320334551553 43965117444051990250913665)
      ·
        refine ⟨32973838083038992688185249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43965117444051990250913665 32973838083038992688185249)
        ·
          refine ⟨24730378562279244516138937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32973838083038992688185249 24730378562279244516138937)
          ·
            refine ⟨18547783921709433387104203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24730378562279244516138937 18547783921709433387104203)
            ·
              refine ⟨27821675882564150080656305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18547783921709433387104203 27821675882564150080656305)
              ·
                refine ⟨20866256911923112560492229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27821675882564150080656305 20866256911923112560492229)
                ·
                  refine ⟨3912423170985583605092293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20866256911923112560492229 3912423170985583605092293)
                  ·
                    refine ⟨733579344559796925954805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3912423170985583605092293 733579344559796925954805)
                    ·
                      rfl

theorem cell22_2142961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2142961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142961 prefixEnd_2142961 := by exact prefixLift 2142961
  have htrace : WordTrace (prefixWord ++ tailWord_2142961) baseStart_2142961 baseEnd_2142961 := by
    simpa [prefixWord, tailWord_2142961, baseEnd_2142961] using wordTrace_append hprefix tailTrace_2142961
  have hstable : (prefixWord ++ tailWord_2142961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142961).length < 2 ^ (prefixWord ++ tailWord_2142961).sum := by decide
  have hdescent : baseEnd_2142961 < baseStart_2142961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142999 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 4]
def baseStart_2142999 : Nat := 118140960795 + 2142999 * 2 ^ 59
def prefixEnd_2142999 : Nat := 4983230072969 + 3 ^ 40 * 2142999 * 2
def baseEnd_2142999 : Nat := 244530784245459164501563

theorem tailTrace_2142999 : CollatzResearch.WordTrace tailWord_2142999 prefixEnd_2142999 244530784245459164501563 := by
  unfold tailWord_2142999
  simp only [CollatzResearch.WordTrace]
  refine ⟨78161594763288092935952051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52107729842192061957301367 78161594763288092935952051)
  ·
    refine ⟨117242392144932139403928077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78161594763288092935952051 117242392144932139403928077)
    ·
      refine ⟨43965897054349552276473029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117242392144932139403928077 43965897054349552276473029)
      ·
        refine ⟨8243605697690541051838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43965897054349552276473029 8243605697690541051838693)
        ·
          refine ⟨1545676068316976447219755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8243605697690541051838693 1545676068316976447219755)
          ·
            refine ⟨2318514102475464670829633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545676068316976447219755 2318514102475464670829633)
            ·
              refine ⟨1738885576856598503122225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318514102475464670829633 1738885576856598503122225)
              ·
                refine ⟨1304164182642448877341669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738885576856598503122225 1304164182642448877341669)
                ·
                  refine ⟨244530784245459164501563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304164182642448877341669 244530784245459164501563)
                  ·
                    rfl

theorem cell22_2142999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 4].length) (baseStart_2142999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2142999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2142999 prefixEnd_2142999 := by exact prefixLift 2142999
  have htrace : WordTrace (prefixWord ++ tailWord_2142999) baseStart_2142999 baseEnd_2142999 := by
    simpa [prefixWord, tailWord_2142999, baseEnd_2142999] using wordTrace_append hprefix tailTrace_2142999
  have hstable : (prefixWord ++ tailWord_2142999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142999).length < 2 ^ (prefixWord ++ tailWord_2142999).sum := by decide
  have hdescent : baseEnd_2142999 < baseStart_2142999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143036 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2143036 : Nat := 118140960795 + 2143036 * 2 ^ 59
def prefixEnd_2143036 : Nat := 4983230072969 + 3 ^ 40 * 2143036 * 2
def baseEnd_2143036 : Nat := 733605018592521730329575

theorem tailTrace_2143036 : CollatzResearch.WordTrace tailWord_2143036 prefixEnd_2143036 733605018592521730329575 := by
  unfold tailWord_2143036
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081472132077024127524481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52108629509436032170032641 39081472132077024127524481)
  ·
    refine ⟨29311104099057768095643361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39081472132077024127524481 29311104099057768095643361)
    ·
      refine ⟨21983328074293326071732521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29311104099057768095643361 21983328074293326071732521)
      ·
        refine ⟨16487496055719994553799391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21983328074293326071732521 16487496055719994553799391)
        ·
          refine ⟨24731244083579991830699087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16487496055719994553799391 24731244083579991830699087)
          ·
            refine ⟨37096866125369987746048631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24731244083579991830699087 37096866125369987746048631)
            ·
              refine ⟨55645299188054981619072947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37096866125369987746048631 55645299188054981619072947)
              ·
                refine ⟨83467948782082472428609421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55645299188054981619072947 83467948782082472428609421)
                ·
                  refine ⟨31300480793280927160728533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83467948782082472428609421 31300480793280927160728533)
                  ·
                    refine ⟨733605018592521730329575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31300480793280927160728533 733605018592521730329575)
                    ·
                      rfl

theorem cell22_2143036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2143036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143036 prefixEnd_2143036 := by exact prefixLift 2143036
  have htrace : WordTrace (prefixWord ++ tailWord_2143036) baseStart_2143036 baseEnd_2143036 := by
    simpa [prefixWord, tailWord_2143036, baseEnd_2143036] using wordTrace_append hprefix tailTrace_2143036
  have hstable : (prefixWord ++ tailWord_2143036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143036).length < 2 ^ (prefixWord ++ tailWord_2143036).sum := by decide
  have hdescent : baseEnd_2143036 < baseStart_2143036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143113 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_2143113 : Nat := 118140960795 + 2143113 * 2 ^ 59
def prefixEnd_2143113 : Nat := 4983230072969 + 3 ^ 40 * 2143113 * 2
def baseEnd_2143113 : Nat := 733631377266119196154339

theorem tailTrace_2143113 : CollatzResearch.WordTrace tailWord_2143113 prefixEnd_2143113 733631377266119196154339 := by
  unfold tailWord_2143113
  simp only [CollatzResearch.WordTrace]
  refine ⟨78165752684875090405601993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52110501789916726937067995 78165752684875090405601993)
  ·
    refine ⟨58624314513656317804201495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78165752684875090405601993 58624314513656317804201495)
    ·
      refine ⟨87936471770484476706302243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58624314513656317804201495 87936471770484476706302243)
      ·
        refine ⟨131904707655726715059453365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87936471770484476706302243 131904707655726715059453365)
        ·
          refine ⟨12366066342724379536823753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131904707655726715059453365 12366066342724379536823753)
          ·
            refine ⟨9274549757043284652617815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12366066342724379536823753 9274549757043284652617815)
            ·
              refine ⟨13911824635564926978926723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274549757043284652617815 13911824635564926978926723)
              ·
                refine ⟨20867736953347390468390085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13911824635564926978926723 20867736953347390468390085)
                ·
                  refine ⟨3912700678752635712823141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20867736953347390468390085 3912700678752635712823141)
                  ·
                    refine ⟨733631377266119196154339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3912700678752635712823141 733631377266119196154339)
                    ·
                      rfl

theorem cell22_2143113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_2143113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143113 prefixEnd_2143113 := by exact prefixLift 2143113
  have htrace : WordTrace (prefixWord ++ tailWord_2143113) baseStart_2143113 baseEnd_2143113 := by
    simpa [prefixWord, tailWord_2143113, baseEnd_2143113] using wordTrace_append hprefix tailTrace_2143113
  have hstable : (prefixWord ++ tailWord_2143113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143113).length < 2 ^ (prefixWord ++ tailWord_2143113).sum := by decide
  have hdescent : baseEnd_2143113 < baseStart_2143113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143265 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2143265 : Nat := 118140960795 + 2143265 * 2 ^ 59
def prefixEnd_2143265 : Nat := 4983230072969 + 3 ^ 40 * 2143265 * 2
def baseEnd_2143265 : Nat := 733683409972441466353873

theorem tailTrace_2143265 : CollatzResearch.WordTrace tailWord_2143265 prefixEnd_2143265 733683409972441466353873 := by
  unfold tailWord_2143265
  simp only [CollatzResearch.WordTrace]
  refine ⟨78171296580324420365135249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52114197720216280243423499 78171296580324420365135249)
  ·
    refine ⟨58628472435243315273851437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78171296580324420365135249 58628472435243315273851437)
    ·
      refine ⟨21985677163216243227694289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58628472435243315273851437 21985677163216243227694289)
      ·
        refine ⟨16489257872412182420770717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21985677163216243227694289 16489257872412182420770717)
        ·
          refine ⟨6183471702154568407789019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16489257872412182420770717 6183471702154568407789019)
          ·
            refine ⟨9275207553231852611683529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183471702154568407789019 9275207553231852611683529)
            ·
              refine ⟨6956405664923889458762647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9275207553231852611683529 6956405664923889458762647)
              ·
                refine ⟨10434608497385834188143971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956405664923889458762647 10434608497385834188143971)
                ·
                  refine ⟨15651912746078751282215957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10434608497385834188143971 15651912746078751282215957)
                  ·
                    refine ⟨733683409972441466353873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15651912746078751282215957 733683409972441466353873)
                    ·
                      rfl

theorem cell22_2143265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2143265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143265 prefixEnd_2143265 := by exact prefixLift 2143265
  have htrace : WordTrace (prefixWord ++ tailWord_2143265) baseStart_2143265 baseEnd_2143265 := by
    simpa [prefixWord, tailWord_2143265, baseEnd_2143265] using wordTrace_append hprefix tailTrace_2143265
  have hstable : (prefixWord ++ tailWord_2143265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143265).length < 2 ^ (prefixWord ++ tailWord_2143265).sum := by decide
  have hdescent : baseEnd_2143265 < baseStart_2143265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143284 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2143284 : Nat := 118140960795 + 2143284 * 2 ^ 59
def prefixEnd_2143284 : Nat := 4983230072969 + 3 ^ 40 * 2143284 * 2
def baseEnd_2143284 : Nat := 733689914060731750128815

theorem tailTrace_2143284 : CollatzResearch.WordTrace tailWord_2143284 prefixEnd_2143284 733689914060731750128815 := by
  unfold tailWord_2143284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39085994783627793305038453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52114659711503724406717937 39085994783627793305038453)
  ·
    refine ⟨3664312010965105622347355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39085994783627793305038453 3664312010965105622347355)
    ·
      refine ⟨5496468016447658433521033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664312010965105622347355 5496468016447658433521033)
      ·
        refine ⟨4122351012335743825140775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5496468016447658433521033 4122351012335743825140775)
        ·
          refine ⟨6183526518503615737711163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122351012335743825140775 6183526518503615737711163)
          ·
            refine ⟨9275289777755423606566745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183526518503615737711163 9275289777755423606566745)
            ·
              refine ⟨6956467333316567704925059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9275289777755423606566745 6956467333316567704925059)
              ·
                refine ⟨10434700999974851557387589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6956467333316567704925059 10434700999974851557387589)
                ·
                  refine ⟨1956506437495284667010173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10434700999974851557387589 1956506437495284667010173)
                  ·
                    refine ⟨733689914060731750128815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956506437495284667010173 733689914060731750128815)
                    ·
                      rfl

theorem cell22_2143284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2143284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143284 prefixEnd_2143284 := by exact prefixLift 2143284
  have htrace : WordTrace (prefixWord ++ tailWord_2143284) baseStart_2143284 baseEnd_2143284 := by
    simpa [prefixWord, tailWord_2143284, baseEnd_2143284] using wordTrace_append hprefix tailTrace_2143284
  have hstable : (prefixWord ++ tailWord_2143284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143284).length < 2 ^ (prefixWord ++ tailWord_2143284).sum := by decide
  have hdescent : baseEnd_2143284 < baseStart_2143284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143286 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2143286 : Nat := 118140960795 + 2143286 * 2 ^ 59
def prefixEnd_2143286 : Nat := 4983230072969 + 3 ^ 40 * 2143286 * 2
def baseEnd_2143286 : Nat := 244563532900534803859603

theorem tailTrace_2143286 : CollatzResearch.WordTrace tailWord_2143286 prefixEnd_2143286 244563532900534803859603 := by
  unfold tailWord_2143286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885753907078021309478107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52114708342165560634433141 4885753907078021309478107)
  ·
    refine ⟨7328630860617031964217161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885753907078021309478107 7328630860617031964217161)
    ·
      refine ⟨5496473145462773973162871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7328630860617031964217161 5496473145462773973162871)
      ·
        refine ⟨8244709718194160959744307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5496473145462773973162871 8244709718194160959744307)
        ·
          refine ⟨12367064577291241439616461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8244709718194160959744307 12367064577291241439616461)
          ·
            refine ⟨4637649216484215539856173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12367064577291241439616461 4637649216484215539856173)
            ·
              refine ⟨1739118456181580827446065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4637649216484215539856173 1739118456181580827446065)
              ·
                refine ⟨1304338842136185620584549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1739118456181580827446065 1304338842136185620584549)
                ·
                  refine ⟨244563532900534803859603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304338842136185620584549 244563532900534803859603)
                  ·
                    rfl

theorem cell22_2143286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2143286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143286 prefixEnd_2143286 := by exact prefixLift 2143286
  have htrace : WordTrace (prefixWord ++ tailWord_2143286) baseStart_2143286 baseEnd_2143286 := by
    simpa [prefixWord, tailWord_2143286, baseEnd_2143286] using wordTrace_append hprefix tailTrace_2143286
  have hstable : (prefixWord ++ tailWord_2143286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143286).length < 2 ^ (prefixWord ++ tailWord_2143286).sum := by decide
  have hdescent : baseEnd_2143286 < baseStart_2143286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143297 : List Nat := [1, 2, 5, 1, 3, 1, 2, 7]
def baseStart_2143297 : Nat := 118140960795 + 2143297 * 2 ^ 59
def prefixEnd_2143297 : Nat := 4983230072969 + 3 ^ 40 * 2143297 * 2
def baseEnd_2143297 : Nat := 81521596025156005505975

theorem tailTrace_2143297 : CollatzResearch.WordTrace tailWord_2143297 prefixEnd_2143297 81521596025156005505975 := by
  unfold tailWord_2143297
  simp only [CollatzResearch.WordTrace]
  refine ⟨78172463716208489830300145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52114975810805659886866763 78172463716208489830300145)
  ·
    refine ⟨58629347787156367372725109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78172463716208489830300145 58629347787156367372725109)
    ·
      refine ⟨5496501355045909441192979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58629347787156367372725109 5496501355045909441192979)
      ·
        refine ⟨8244752032568864161789469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5496501355045909441192979 8244752032568864161789469)
        ·
          refine ⟨3091782012213324060671051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8244752032568864161789469 3091782012213324060671051)
          ·
            refine ⟨4637673018319986091006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091782012213324060671051 4637673018319986091006577)
            ·
              refine ⟨3478254763739989568254933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637673018319986091006577 3478254763739989568254933)
              ·
                refine ⟨81521596025156005505975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3478254763739989568254933 81521596025156005505975)
                ·
                  rfl

theorem cell22_2143297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 7].length) (baseStart_2143297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143297 prefixEnd_2143297 := by exact prefixLift 2143297
  have htrace : WordTrace (prefixWord ++ tailWord_2143297) baseStart_2143297 baseEnd_2143297 := by
    simpa [prefixWord, tailWord_2143297, baseEnd_2143297] using wordTrace_append hprefix tailTrace_2143297
  have hstable : (prefixWord ++ tailWord_2143297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143297).length < 2 ^ (prefixWord ++ tailWord_2143297).sum := by decide
  have hdescent : baseEnd_2143297 < baseStart_2143297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143340 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_2143340 : Nat := 118140960795 + 2143340 * 2 ^ 59
def prefixEnd_2143340 : Nat := 4983230072969 + 3 ^ 40 * 2143340 * 2
def baseEnd_2143340 : Nat := 733709084005166270728643

theorem tailTrace_2143340 : CollatzResearch.WordTrace tailWord_2143340 prefixEnd_2143340 733709084005166270728643 := by
  unfold tailWord_2143340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39087016027526354087057737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52116021370035138782743649 39087016027526354087057737)
  ·
    refine ⟨29315262020644765565293303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39087016027526354087057737 29315262020644765565293303)
    ·
      refine ⟨43972893030967148347939955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29315262020644765565293303 43972893030967148347939955)
      ·
        refine ⟨65959339546450722521909933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43972893030967148347939955 65959339546450722521909933)
        ·
          refine ⟨24734752329919020945716225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65959339546450722521909933 24734752329919020945716225)
          ·
            refine ⟨18551064247439265709287169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24734752329919020945716225 18551064247439265709287169)
            ·
              refine ⟨13913298185579449281965377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18551064247439265709287169 13913298185579449281965377)
              ·
                refine ⟨10434973639184586961474033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13913298185579449281965377 10434973639184586961474033)
                ·
                  refine ⟨7826230229388440221105525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10434973639184586961474033 7826230229388440221105525)
                  ·
                    refine ⟨733709084005166270728643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7826230229388440221105525 733709084005166270728643)
                    ·
                      rfl

theorem cell22_2143340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_2143340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143340 prefixEnd_2143340 := by exact prefixLift 2143340
  have htrace : WordTrace (prefixWord ++ tailWord_2143340) baseStart_2143340 baseEnd_2143340 := by
    simpa [prefixWord, tailWord_2143340, baseEnd_2143340] using wordTrace_append hprefix tailTrace_2143340
  have hstable : (prefixWord ++ tailWord_2143340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143340).length < 2 ^ (prefixWord ++ tailWord_2143340).sum := by decide
  have hdescent : baseEnd_2143340 < baseStart_2143340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143342 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_2143342 : Nat := 118140960795 + 2143342 * 2 ^ 59
def prefixEnd_2143342 : Nat := 4983230072969 + 3 ^ 40 * 2143342 * 2
def baseEnd_2143342 : Nat := 244569922882012977392879

theorem tailTrace_2143342 : CollatzResearch.WordTrace tailWord_2143342 prefixEnd_2143342 244569922882012977392879 := by
  unfold tailWord_2143342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771763125130682814461035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52116070000696975010458853 9771763125130682814461035)
  ·
    refine ⟨14657644687696024221691553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9771763125130682814461035 14657644687696024221691553)
    ·
      refine ⟨10993233515772018166268665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14657644687696024221691553 10993233515772018166268665)
      ·
        refine ⟨8244925136829013624701499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10993233515772018166268665 8244925136829013624701499)
        ·
          refine ⟨12367387705243520437052249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8244925136829013624701499 12367387705243520437052249)
          ·
            refine ⟨9275540778932640327789187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12367387705243520437052249 9275540778932640327789187)
            ·
              refine ⟨13913311168398960491683781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9275540778932640327789187 13913311168398960491683781)
              ·
                refine ⟨2608745844074805092190709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13913311168398960491683781 2608745844074805092190709)
                ·
                  refine ⟨244569922882012977392879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2608745844074805092190709 244569922882012977392879)
                  ·
                    rfl

theorem cell22_2143342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_2143342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143342 prefixEnd_2143342 := by exact prefixLift 2143342
  have htrace : WordTrace (prefixWord ++ tailWord_2143342) baseStart_2143342 baseEnd_2143342 := by
    simpa [prefixWord, tailWord_2143342, baseEnd_2143342] using wordTrace_append hprefix tailTrace_2143342
  have hstable : (prefixWord ++ tailWord_2143342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143342).length < 2 ^ (prefixWord ++ tailWord_2143342).sum := by decide
  have hdescent : baseEnd_2143342 < baseStart_2143342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143415 : List Nat := [1, 1, 3, 1, 4, 1, 2, 9]
def baseStart_2143415 : Nat := 118140960795 + 2143415 * 2 ^ 59
def prefixEnd_2143415 : Nat := 4983230072969 + 3 ^ 40 * 2143415 * 2
def baseEnd_2143415 : Nat := 81526084226432341678157

theorem tailTrace_2143415 : CollatzResearch.WordTrace tailWord_2143415 prefixEnd_2143415 81526084226432341678157 := by
  unfold tailWord_2143415
  simp only [CollatzResearch.WordTrace]
  refine ⟨78176767529780995983095699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52117845019853997322063799 78176767529780995983095699)
  ·
    refine ⟨117265151294671493974643549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78176767529780995983095699 117265151294671493974643549)
    ·
      refine ⟨43974431735501810240491331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117265151294671493974643549 43974431735501810240491331)
      ·
        refine ⟨65961647603252715360736997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43974431735501810240491331 65961647603252715360736997)
        ·
          refine ⟨12367808925609884130138187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65961647603252715360736997 12367808925609884130138187)
          ·
            refine ⟨18551713388414826195207281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12367808925609884130138187 18551713388414826195207281)
            ·
              refine ⟨13913785041311119646405461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18551713388414826195207281 13913785041311119646405461)
              ·
                refine ⟨81526084226432341678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13913785041311119646405461 81526084226432341678157)
                ·
                  rfl

theorem cell22_2143415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 9].length) (baseStart_2143415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143415 prefixEnd_2143415 := by exact prefixLift 2143415
  have htrace : WordTrace (prefixWord ++ tailWord_2143415) baseStart_2143415 baseEnd_2143415 := by
    simpa [prefixWord, tailWord_2143415, baseEnd_2143415] using wordTrace_append hprefix tailTrace_2143415
  have hstable : (prefixWord ++ tailWord_2143415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143415).length < 2 ^ (prefixWord ++ tailWord_2143415).sum := by decide
  have hdescent : baseEnd_2143415 < baseStart_2143415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143432 : List Nat := [2, 1, 3, 1, 2, 1, 6, 6]
def baseStart_2143432 : Nat := 118140960795 + 2143432 * 2 ^ 59
def prefixEnd_2143432 : Nat := 4983230072969 + 3 ^ 40 * 2143432 * 2
def baseEnd_2143432 : Nat := 81526730831700966380929

theorem tailTrace_2143432 : CollatzResearch.WordTrace tailWord_2143432 prefixEnd_2143432 81526730831700966380929 := by
  unfold tailWord_2143432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39088693785359703943232275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52118258380479605257643033 39088693785359703943232275)
  ·
    refine ⟨58633040678039555914848413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39088693785359703943232275 58633040678039555914848413)
    ·
      refine ⟨21987390254264833468068155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58633040678039555914848413 21987390254264833468068155)
      ·
        refine ⟨32981085381397250202102233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21987390254264833468068155 32981085381397250202102233)
        ·
          refine ⟨24735814036047937651576675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32981085381397250202102233 24735814036047937651576675)
          ·
            refine ⟨37103721054071906477365013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24735814036047937651576675 37103721054071906477365013)
            ·
              refine ⟨1739236924409620616126485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37103721054071906477365013 1739236924409620616126485)
              ·
                refine ⟨81526730831700966380929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1739236924409620616126485 81526730831700966380929)
                ·
                  rfl

theorem cell22_2143432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_2143432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143432 prefixEnd_2143432 := by exact prefixLift 2143432
  have htrace : WordTrace (prefixWord ++ tailWord_2143432) baseStart_2143432 baseEnd_2143432 := by
    simpa [prefixWord, tailWord_2143432, baseEnd_2143432] using wordTrace_append hprefix tailTrace_2143432
  have hstable : (prefixWord ++ tailWord_2143432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143432).length < 2 ^ (prefixWord ++ tailWord_2143432).sum := by decide
  have hdescent : baseEnd_2143432 < baseStart_2143432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143438 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_2143438 : Nat := 118140960795 + 2143438 * 2 ^ 59
def prefixEnd_2143438 : Nat := 4983230072969 + 3 ^ 40 * 2143438 * 2
def baseEnd_2143438 : Nat := 244580877135975560592781

theorem tailTrace_2143438 : CollatzResearch.WordTrace tailWord_2143438 prefixEnd_2143438 244580877135975560592781 := by
  unfold tailWord_2143438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9772200801087208863897871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52118404272465113940788645 9772200801087208863897871)
  ·
    refine ⟨14658301201630813295846807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9772200801087208863897871 14658301201630813295846807)
    ·
      refine ⟨21987451802446219943770211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14658301201630813295846807 21987451802446219943770211)
      ·
        refine ⟨32981177703669329915655317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21987451802446219943770211 32981177703669329915655317)
        ·
          refine ⟨1545992704859499839796343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32981177703669329915655317 1545992704859499839796343)
          ·
            refine ⟨2318989057289249759694515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545992704859499839796343 2318989057289249759694515)
            ·
              refine ⟨3478483585933874639541773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318989057289249759694515 3478483585933874639541773)
              ·
                refine ⟨1304431344725202989828165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478483585933874639541773 1304431344725202989828165)
                ·
                  refine ⟨244580877135975560592781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304431344725202989828165 244580877135975560592781)
                  ·
                    rfl

theorem cell22_2143438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_2143438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143438 prefixEnd_2143438 := by exact prefixLift 2143438
  have htrace : WordTrace (prefixWord ++ tailWord_2143438) baseStart_2143438 baseEnd_2143438 := by
    simpa [prefixWord, tailWord_2143438, baseEnd_2143438] using wordTrace_append hprefix tailTrace_2143438
  have hstable : (prefixWord ++ tailWord_2143438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143438).length < 2 ^ (prefixWord ++ tailWord_2143438).sum := by decide
  have hdescent : baseEnd_2143438 < baseStart_2143438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143447 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2143447 : Nat := 118140960795 + 2143447 * 2 ^ 59
def prefixEnd_2143447 : Nat := 4983230072969 + 3 ^ 40 * 2143447 * 2
def baseEnd_2143447 : Nat := 733745712291853658303315

theorem tailTrace_2143447 : CollatzResearch.WordTrace tailWord_2143447 prefixEnd_2143447 733745712291853658303315 := by
  unfold tailWord_2143447
  simp only [CollatzResearch.WordTrace]
  refine ⟨78177934665665065448260595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52118623110443376965507063 78177934665665065448260595)
  ·
    refine ⟨117266901998497598172390893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78177934665665065448260595 117266901998497598172390893)
    ·
      refine ⟨43975088249436599314646585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117266901998497598172390893 43975088249436599314646585)
      ·
        refine ⟨32981316187077449485984939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43975088249436599314646585 32981316187077449485984939)
        ·
          refine ⟨49471974280616174228977409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32981316187077449485984939 49471974280616174228977409)
          ·
            refine ⟨37103980710462130671733057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49471974280616174228977409 37103980710462130671733057)
            ·
              refine ⟨27827985532846598003799793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37103980710462130671733057 27827985532846598003799793)
              ·
                refine ⟨20870989149634948502849845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27827985532846598003799793 20870989149634948502849845)
                ·
                  refine ⟨1956655232778276422142173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20870989149634948502849845 1956655232778276422142173)
                  ·
                    refine ⟨733745712291853658303315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956655232778276422142173 733745712291853658303315)
                    ·
                      rfl

theorem cell22_2143447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2143447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143447 prefixEnd_2143447 := by exact prefixLift 2143447
  have htrace : WordTrace (prefixWord ++ tailWord_2143447) baseStart_2143447 baseEnd_2143447 := by
    simpa [prefixWord, tailWord_2143447, baseEnd_2143447] using wordTrace_append hprefix tailTrace_2143447
  have hstable : (prefixWord ++ tailWord_2143447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143447).length < 2 ^ (prefixWord ++ tailWord_2143447).sum := by decide
  have hdescent : baseEnd_2143447 < baseStart_2143447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143552 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_2143552 : Nat := 118140960795 + 2143552 * 2 ^ 59
def prefixEnd_2143552 : Nat := 4983230072969 + 3 ^ 40 * 2143552 * 2
def baseEnd_2143552 : Nat := 733781655937668384427993

theorem tailTrace_2143552 : CollatzResearch.WordTrace tailWord_2143552 prefixEnd_2143552 733781655937668384427993 := by
  unfold tailWord_2143552
  simp only [CollatzResearch.WordTrace]
  refine ⟨39090882165142334190416455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52121176220189778920555273 39090882165142334190416455)
  ·
    refine ⟨58636323247713501285624683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39090882165142334190416455 58636323247713501285624683)
    ·
      refine ⟨87954484871570251928437025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58636323247713501285624683 87954484871570251928437025)
      ·
        refine ⟨65965863653677688946327769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87954484871570251928437025 65965863653677688946327769)
        ·
          refine ⟨49474397740258266709745827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65965863653677688946327769 49474397740258266709745827)
          ·
            refine ⟨74211596610387400064618741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49474397740258266709745827 74211596610387400064618741)
            ·
              refine ⟨6957337182223818756058007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74211596610387400064618741 6957337182223818756058007)
              ·
                refine ⟨10436005773335728134087011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957337182223818756058007 10436005773335728134087011)
                ·
                  refine ⟨15654008660003592201130517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10436005773335728134087011 15654008660003592201130517)
                  ·
                    refine ⟨733781655937668384427993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15654008660003592201130517 733781655937668384427993)
                    ·
                      rfl

theorem cell22_2143552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_2143552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143552 prefixEnd_2143552 := by exact prefixLift 2143552
  have htrace : WordTrace (prefixWord ++ tailWord_2143552) baseStart_2143552 baseEnd_2143552 := by
    simpa [prefixWord, tailWord_2143552, baseEnd_2143552] using wordTrace_append hprefix tailTrace_2143552
  have hstable : (prefixWord ++ tailWord_2143552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143552).length < 2 ^ (prefixWord ++ tailWord_2143552).sum := by decide
  have hdescent : baseEnd_2143552 < baseStart_2143552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143588 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2143588 : Nat := 118140960795 + 2143588 * 2 ^ 59
def prefixEnd_2143588 : Nat := 4983230072969 + 3 ^ 40 * 2143588 * 2
def baseEnd_2143588 : Nat := 733793979473376290527883

theorem tailTrace_2143588 : CollatzResearch.WordTrace tailWord_2143588 prefixEnd_2143588 733793979473376290527883 := by
  unfold tailWord_2143588
  simp only [CollatzResearch.WordTrace]
  refine ⟨39091538679077123264571709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52122051572102831019428945 39091538679077123264571709)
  ·
    refine ⟨14659327004653921224214391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39091538679077123264571709 14659327004653921224214391)
    ·
      refine ⟨21988990506980881836321587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14659327004653921224214391 21988990506980881836321587)
      ·
        refine ⟨32983485760471322754482381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21988990506980881836321587 32983485760471322754482381)
        ·
          refine ⟨12368807160176746032930893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32983485760471322754482381 12368807160176746032930893)
          ·
            refine ⟨4638302685066279762349085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12368807160176746032930893 4638302685066279762349085)
            ·
              refine ⟨1739363506899854910880907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4638302685066279762349085 1739363506899854910880907)
              ·
                refine ⟨2609045260349782366321361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739363506899854910880907 2609045260349782366321361)
                ·
                  refine ⟨1956783945262336774741021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609045260349782366321361 1956783945262336774741021)
                  ·
                    refine ⟨733793979473376290527883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956783945262336774741021 733793979473376290527883)
                    ·
                      rfl

theorem cell22_2143588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2143588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143588 prefixEnd_2143588 := by exact prefixLift 2143588
  have htrace : WordTrace (prefixWord ++ tailWord_2143588) baseStart_2143588 baseEnd_2143588 := by
    simpa [prefixWord, tailWord_2143588, baseEnd_2143588] using wordTrace_append hprefix tailTrace_2143588
  have hstable : (prefixWord ++ tailWord_2143588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143588).length < 2 ^ (prefixWord ++ tailWord_2143588).sum := by decide
  have hdescent : baseEnd_2143588 < baseStart_2143588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143599 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 3, 3]
def baseStart_2143599 : Nat := 118140960795 + 2143599 * 2 ^ 59
def prefixEnd_2143599 : Nat := 4983230072969 + 3 ^ 40 * 2143599 * 2
def baseEnd_2143599 : Nat := 733797744998175928502849

theorem tailTrace_2143599 : CollatzResearch.WordTrace tailWord_2143599 prefixEnd_2143599 733797744998175928502849 := by
  unfold tailWord_2143599
  simp only [CollatzResearch.WordTrace]
  refine ⟨78183478561114395407793851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52122319040742930271862567 78183478561114395407793851)
  ·
    refine ⟨117275217841671593111690777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78183478561114395407793851 117275217841671593111690777)
    ·
      refine ⟨87956413381253694833768083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117275217841671593111690777 87956413381253694833768083)
      ·
        refine ⟨131934620071880542250652125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87956413381253694833768083 131934620071880542250652125)
        ·
          refine ⟨49475482526955203343994547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131934620071880542250652125 49475482526955203343994547)
          ·
            refine ⟨74213223790432805015991821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49475482526955203343994547 74213223790432805015991821)
            ·
              refine ⟨27829958921412301880996933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74213223790432805015991821 27829958921412301880996933)
              ·
                refine ⟨5218117297764806602686925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27829958921412301880996933 5218117297764806602686925)
                ·
                  refine ⟨1956793986661802476007597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5218117297764806602686925 1956793986661802476007597)
                  ·
                    refine ⟨733797744998175928502849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1956793986661802476007597 733797744998175928502849)
                    ·
                      rfl

theorem cell22_2143599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_2143599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143599 prefixEnd_2143599 := by exact prefixLift 2143599
  have htrace : WordTrace (prefixWord ++ tailWord_2143599) baseStart_2143599 baseEnd_2143599 := by
    simpa [prefixWord, tailWord_2143599, baseEnd_2143599] using wordTrace_append hprefix tailTrace_2143599
  have hstable : (prefixWord ++ tailWord_2143599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143599).length < 2 ^ (prefixWord ++ tailWord_2143599).sum := by decide
  have hdescent : baseEnd_2143599 < baseStart_2143599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143612 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_2143612 : Nat := 118140960795 + 2143612 * 2 ^ 59
def prefixEnd_2143612 : Nat := 4983230072969 + 3 ^ 40 * 2143612 * 2
def baseEnd_2143612 : Nat := 244600731721282742642603

theorem tailTrace_2143612 : CollatzResearch.WordTrace tailWord_2143612 prefixEnd_2143612 244600731721282742642603 := by
  unfold tailWord_2143612
  simp only [CollatzResearch.WordTrace]
  refine ⟨39091976355033649314008545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52122635140044865752011393 39091976355033649314008545)
  ·
    refine ⟨29318982266275236985506409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39091976355033649314008545 29318982266275236985506409)
    ·
      refine ⟨21989236699706427739129807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29318982266275236985506409 21989236699706427739129807)
      ·
        refine ⟨32983855049559641608694711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21989236699706427739129807 32983855049559641608694711)
        ·
          refine ⟨49475782574339462413042067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32983855049559641608694711 49475782574339462413042067)
          ·
            refine ⟨74213673861509193619563101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49475782574339462413042067 74213673861509193619563101)
            ·
              refine ⟨27830127698065947607336163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74213673861509193619563101 27830127698065947607336163)
              ·
                refine ⟨41745191547098921411004245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27830127698065947607336163 41745191547098921411004245)
                ·
                  refine ⟨244600731721282742642603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41745191547098921411004245 244600731721282742642603)
                  ·
                    rfl

theorem cell22_2143612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_2143612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143612 prefixEnd_2143612 := by exact prefixLift 2143612
  have htrace : WordTrace (prefixWord ++ tailWord_2143612) baseStart_2143612 baseEnd_2143612 := by
    simpa [prefixWord, tailWord_2143612, baseEnd_2143612] using wordTrace_append hprefix tailTrace_2143612
  have hstable : (prefixWord ++ tailWord_2143612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143612).length < 2 ^ (prefixWord ++ tailWord_2143612).sum := by decide
  have hdescent : baseEnd_2143612 < baseStart_2143612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143704 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2143704 : Nat := 118140960795 + 2143704 * 2 ^ 59
def prefixEnd_2143704 : Nat := 4983230072969 + 3 ^ 40 * 2143704 * 2
def baseEnd_2143704 : Nat := 733833688643990654627527

theorem tailTrace_2143704 : CollatzResearch.WordTrace tailWord_2143704 prefixEnd_2143704 733833688643990654627527 := by
  unfold tailWord_2143704
  simp only [CollatzResearch.WordTrace]
  refine ⟨39093654112866999170183083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52124872150489332226910777 39093654112866999170183083)
  ·
    refine ⟨58640481169300498755274625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39093654112866999170183083 58640481169300498755274625)
    ·
      refine ⟨43980360876975374066455969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58640481169300498755274625 43980360876975374066455969)
      ·
        refine ⟨32985270657731530549841977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43980360876975374066455969 32985270657731530549841977)
        ·
          refine ⟨24738952993298647912381483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32985270657731530549841977 24738952993298647912381483)
          ·
            refine ⟨37108429489947971868572225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24738952993298647912381483 37108429489947971868572225)
            ·
              refine ⟨27831322117460978901429169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37108429489947971868572225 27831322117460978901429169)
              ·
                refine ⟨20873491588095734176071877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27831322117460978901429169 20873491588095734176071877)
                ·
                  refine ⟨3913779672767950158013477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20873491588095734176071877 3913779672767950158013477)
                  ·
                    refine ⟨733833688643990654627527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3913779672767950158013477 733833688643990654627527)
                    ·
                      rfl

theorem cell22_2143704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2143704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143704 prefixEnd_2143704 := by exact prefixLift 2143704
  have htrace : WordTrace (prefixWord ++ tailWord_2143704) baseStart_2143704 baseEnd_2143704 := by
    simpa [prefixWord, tailWord_2143704, baseEnd_2143704] using wordTrace_append hprefix tailTrace_2143704
  have hstable : (prefixWord ++ tailWord_2143704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143704).length < 2 ^ (prefixWord ++ tailWord_2143704).sum := by decide
  have hdescent : baseEnd_2143704 < baseStart_2143704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143706 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_2143706 : Nat := 118140960795 + 2143706 * 2 ^ 59
def prefixEnd_2143706 : Nat := 4983230072969 + 3 ^ 40 * 2143706 * 2
def baseEnd_2143706 : Nat := 733834373284863316077521

theorem tailTrace_2143706 : CollatzResearch.WordTrace tailWord_2143706 prefixEnd_2143706 733834373284863316077521 := by
  unfold tailWord_2143706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546845292931688170484743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52124920781151168454625981 19546845292931688170484743)
  ·
    refine ⟨29320267939397532255727115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19546845292931688170484743 29320267939397532255727115)
    ·
      refine ⟨43980401909096298383590673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29320267939397532255727115 43980401909096298383590673)
      ·
        refine ⟨32985301431822223787693005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43980401909096298383590673 32985301431822223787693005)
        ·
          refine ⟨12369488036933333920384877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32985301431822223787693005 12369488036933333920384877)
          ·
            refine ⟨4638558013850000220144329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12369488036933333920384877 4638558013850000220144329)
            ·
              refine ⟨3478918510387500165108247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638558013850000220144329 3478918510387500165108247)
              ·
                refine ⟨5218377765581250247662371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478918510387500165108247 5218377765581250247662371)
                ·
                  refine ⟨7827566648371875371493557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218377765581250247662371 7827566648371875371493557)
                  ·
                    refine ⟨733834373284863316077521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7827566648371875371493557 733834373284863316077521)
                    ·
                      rfl

theorem cell22_2143706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_2143706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143706 prefixEnd_2143706 := by exact prefixLift 2143706
  have htrace : WordTrace (prefixWord ++ tailWord_2143706) baseStart_2143706 baseEnd_2143706 := by
    simpa [prefixWord, tailWord_2143706, baseEnd_2143706] using wordTrace_append hprefix tailTrace_2143706
  have hstable : (prefixWord ++ tailWord_2143706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143706).length < 2 ^ (prefixWord ++ tailWord_2143706).sum := by decide
  have hdescent : baseEnd_2143706 < baseStart_2143706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143725 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2143725 : Nat := 118140960795 + 2143725 * 2 ^ 59
def prefixEnd_2143725 : Nat := 4983230072969 + 3 ^ 40 * 2143725 * 2
def baseEnd_2143725 : Nat := 244613625791051199950821

theorem tailTrace_2143725 : CollatzResearch.WordTrace tailWord_2143725 prefixEnd_2143725 244613625791051199950821 := by
  unfold tailWord_2143725
  simp only [CollatzResearch.WordTrace]
  refine ⟨78188074158657918926880629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52125382772438612617920419 78188074158657918926880629)
  ·
    refine ⟨7330131952374179899395059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78188074158657918926880629 7330131952374179899395059)
    ·
      refine ⟨10995197928561269849092589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330131952374179899395059 10995197928561269849092589)
      ·
        refine ⟨4123199223210476193409721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10995197928561269849092589 4123199223210476193409721)
        ·
          refine ⟨3092399417407857145057291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123199223210476193409721 3092399417407857145057291)
          ·
            refine ⟨4638599126111785717585937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092399417407857145057291 4638599126111785717585937)
            ·
              refine ⟨3478949344583839288189453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638599126111785717585937 3478949344583839288189453)
              ·
                refine ⟨1304606004218939733071045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478949344583839288189453 1304606004218939733071045)
                ·
                  refine ⟨244613625791051199950821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304606004218939733071045 244613625791051199950821)
                  ·
                    rfl

theorem cell22_2143725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2143725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143725 prefixEnd_2143725 := by exact prefixLift 2143725
  have htrace : WordTrace (prefixWord ++ tailWord_2143725) baseStart_2143725 baseEnd_2143725 := by
    simpa [prefixWord, tailWord_2143725, baseEnd_2143725] using wordTrace_append hprefix tailTrace_2143725
  have hstable : (prefixWord ++ tailWord_2143725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143725).length < 2 ^ (prefixWord ++ tailWord_2143725).sum := by decide
  have hdescent : baseEnd_2143725 < baseStart_2143725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143757 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2143757 : Nat := 118140960795 + 2143757 * 2 ^ 59
def prefixEnd_2143757 : Nat := 4983230072969 + 3 ^ 40 * 2143757 * 2
def baseEnd_2143757 : Nat := 733851831627116183052365

theorem tailTrace_2143757 : CollatzResearch.WordTrace tailWord_2143757 prefixEnd_2143757 733851831627116183052365 := by
  unfold tailWord_2143757
  simp only [CollatzResearch.WordTrace]
  refine ⟨78189241294541988392045525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52126160863027992261363683 78189241294541988392045525)
  ·
    refine ⟨1832560342840827852938567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 78189241294541988392045525 1832560342840827852938567)
    ·
      refine ⟨2748840514261241779407851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832560342840827852938567 2748840514261241779407851)
      ·
        refine ⟨4123260771391862669111777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748840514261241779407851 4123260771391862669111777)
        ·
          refine ⟨3092445578543897001833833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123260771391862669111777 3092445578543897001833833)
          ·
            refine ⟨2319334183907922751375375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3092445578543897001833833 2319334183907922751375375)
            ·
              refine ⟨3479001275861884127063063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319334183907922751375375 3479001275861884127063063)
              ·
                refine ⟨5218501913792826190594595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479001275861884127063063 5218501913792826190594595)
                ·
                  refine ⟨7827752870689239285891893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218501913792826190594595 7827752870689239285891893)
                  ·
                    refine ⟨733851831627116183052365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7827752870689239285891893 733851831627116183052365)
                    ·
                      rfl

theorem cell22_2143757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2143757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143757 prefixEnd_2143757 := by exact prefixLift 2143757
  have htrace : WordTrace (prefixWord ++ tailWord_2143757) baseStart_2143757 baseEnd_2143757 := by
    simpa [prefixWord, tailWord_2143757, baseEnd_2143757] using wordTrace_append hprefix tailTrace_2143757
  have hstable : (prefixWord ++ tailWord_2143757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143757).length < 2 ^ (prefixWord ++ tailWord_2143757).sum := by decide
  have hdescent : baseEnd_2143757 < baseStart_2143757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143815 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 5]
def baseStart_2143815 : Nat := 118140960795 + 2143815 * 2 ^ 59
def prefixEnd_2143815 : Nat := 4983230072969 + 3 ^ 40 * 2143815 * 2
def baseEnd_2143815 : Nat := 244623895404141121700729

theorem tailTrace_2143815 : CollatzResearch.WordTrace tailWord_2143815 prefixEnd_2143815 244623895404141121700729 := by
  unfold tailWord_2143815
  simp only [CollatzResearch.WordTrace]
  refine ⟨78191356728331864297656899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52127571152221242865104599 78191356728331864297656899)
  ·
    refine ⟨117287035092497796446485349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78191356728331864297656899 117287035092497796446485349)
    ·
      refine ⟨21991319079843336833716003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117287035092497796446485349 21991319079843336833716003)
      ·
        refine ⟨32986978619765005250574005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21991319079843336833716003 32986978619765005250574005)
        ·
          refine ⟨3092529245602969242241313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32986978619765005250574005 3092529245602969242241313)
          ·
            refine ⟨2319396934202226931680985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3092529245602969242241313 2319396934202226931680985)
            ·
              refine ⟨1739547700651670198760739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2319396934202226931680985 1739547700651670198760739)
              ·
                refine ⟨2609321550977505298141109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739547700651670198760739 2609321550977505298141109)
                ·
                  refine ⟨244623895404141121700729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609321550977505298141109 244623895404141121700729)
                  ·
                    rfl

theorem cell22_2143815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 5].length) (baseStart_2143815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143815 prefixEnd_2143815 := by exact prefixLift 2143815
  have htrace : WordTrace (prefixWord ++ tailWord_2143815) baseStart_2143815 baseEnd_2143815 := by
    simpa [prefixWord, tailWord_2143815, baseEnd_2143815] using wordTrace_append hprefix tailTrace_2143815
  have hstable : (prefixWord ++ tailWord_2143815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143815).length < 2 ^ (prefixWord ++ tailWord_2143815).sum := by decide
  have hdescent : baseEnd_2143815 < baseStart_2143815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143841 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2143841 : Nat := 118140960795 + 2143841 * 2 ^ 59
def prefixEnd_2143841 : Nat := 4983230072969 + 3 ^ 40 * 2143841 * 2
def baseEnd_2143841 : Nat := 733880586543767963952107

theorem tailTrace_2143841 : CollatzResearch.WordTrace tailWord_2143841 prefixEnd_2143841 733880586543767963952107 := by
  unfold tailWord_2143841
  simp only [CollatzResearch.WordTrace]
  refine ⟨78192305026237670738103377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52128203350825113825402251 78192305026237670738103377)
  ·
    refine ⟨58644228769678253053577533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78192305026237670738103377 58644228769678253053577533)
    ·
      refine ⟨21991585788629344895091575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58644228769678253053577533 21991585788629344895091575)
      ·
        refine ⟨32987378682944017342637363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21991585788629344895091575 32987378682944017342637363)
        ·
          refine ⟨49481068024416026013956045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32987378682944017342637363 49481068024416026013956045)
          ·
            refine ⟨18555400509156009755233517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49481068024416026013956045 18555400509156009755233517)
            ·
              refine ⟨6958275190933503658212569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18555400509156009755233517 6958275190933503658212569)
              ·
                refine ⟨5218706393200127743659427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6958275190933503658212569 5218706393200127743659427)
                ·
                  refine ⟨7828059589800191615489141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218706393200127743659427 7828059589800191615489141)
                  ·
                    refine ⟨733880586543767963952107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7828059589800191615489141 733880586543767963952107)
                    ·
                      rfl

theorem cell22_2143841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2143841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143841 prefixEnd_2143841 := by exact prefixLift 2143841
  have htrace : WordTrace (prefixWord ++ tailWord_2143841) baseStart_2143841 baseEnd_2143841 := by
    simpa [prefixWord, tailWord_2143841, baseEnd_2143841] using wordTrace_append hprefix tailTrace_2143841
  have hstable : (prefixWord ++ tailWord_2143841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143841).length < 2 ^ (prefixWord ++ tailWord_2143841).sum := by decide
  have hdescent : baseEnd_2143841 < baseStart_2143841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143845 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_2143845 : Nat := 118140960795 + 2143845 * 2 ^ 59
def prefixEnd_2143845 : Nat := 4983230072969 + 3 ^ 40 * 2143845 * 2
def baseEnd_2143845 : Nat := 733881955825513286852095

theorem tailTrace_2143845 : CollatzResearch.WordTrace tailWord_2143845 prefixEnd_2143845 733881955825513286852095 := by
  unfold tailWord_2143845
  simp only [CollatzResearch.WordTrace]
  refine ⟨78192450918223179421248989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52128300612148786280832659 78192450918223179421248989)
  ·
    refine ⟨29322169094333692282968371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78192450918223179421248989 29322169094333692282968371)
    ·
      refine ⟨43983253641500538424452557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29322169094333692282968371 43983253641500538424452557)
      ·
        refine ⟨16493720115562701909169709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43983253641500538424452557 16493720115562701909169709)
        ·
          refine ⟨6185145043336013215938641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16493720115562701909169709 6185145043336013215938641)
          ·
            refine ⟨4638858782502009911953981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185145043336013215938641 4638858782502009911953981)
            ·
              refine ⟨1739572043438253716982743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4638858782502009911953981 1739572043438253716982743)
              ·
                refine ⟨2609358065157380575474115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739572043438253716982743 2609358065157380575474115)
                ·
                  refine ⟨3914037097736070863211173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609358065157380575474115 3914037097736070863211173)
                  ·
                    refine ⟨733881955825513286852095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3914037097736070863211173 733881955825513286852095)
                    ·
                      rfl

theorem cell22_2143845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_2143845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143845 prefixEnd_2143845 := by exact prefixLift 2143845
  have htrace : WordTrace (prefixWord ++ tailWord_2143845) baseStart_2143845 baseEnd_2143845 := by
    simpa [prefixWord, tailWord_2143845, baseEnd_2143845] using wordTrace_append hprefix tailTrace_2143845
  have hstable : (prefixWord ++ tailWord_2143845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143845).length < 2 ^ (prefixWord ++ tailWord_2143845).sum := by decide
  have hdescent : baseEnd_2143845 < baseStart_2143845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143920 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_2143920 : Nat := 118140960795 + 2143920 * 2 ^ 59
def prefixEnd_2143920 : Nat := 4983230072969 + 3 ^ 40 * 2143920 * 2
def baseEnd_2143920 : Nat := 733907629858238091226865

theorem tailTrace_2143920 : CollatzResearch.WordTrace tailWord_2143920 prefixEnd_2143920 733907629858238091226865 := by
  unfold tailWord_2143920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39097593196475733615114607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52130124261967644820152809 39097593196475733615114607)
  ·
    refine ⟨58646389794713600422671911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39097593196475733615114607 58646389794713600422671911)
    ·
      refine ⟨87969584692070400634007867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58646389794713600422671911 87969584692070400634007867)
      ·
        refine ⟨131954377038105600951011801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87969584692070400634007867 131954377038105600951011801)
        ·
          refine ⟨98965782778579200713258851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131954377038105600951011801 98965782778579200713258851)
          ·
            refine ⟨148448674167868801069888277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98965782778579200713258851 148448674167868801069888277)
            ·
              refine ⟨6958531601618850050151013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148448674167868801069888277 6958531601618850050151013)
              ·
                refine ⟨1304724675303534384403315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6958531601618850050151013 1304724675303534384403315)
                ·
                  refine ⟨1957087012955301576604973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304724675303534384403315 1957087012955301576604973)
                  ·
                    refine ⟨733907629858238091226865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957087012955301576604973 733907629858238091226865)
                    ·
                      rfl

theorem cell22_2143920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_2143920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143920 prefixEnd_2143920 := by exact prefixLift 2143920
  have htrace : WordTrace (prefixWord ++ tailWord_2143920) baseStart_2143920 baseEnd_2143920 := by
    simpa [prefixWord, tailWord_2143920, baseEnd_2143920] using wordTrace_append hprefix tailTrace_2143920
  have hstable : (prefixWord ++ tailWord_2143920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143920).length < 2 ^ (prefixWord ++ tailWord_2143920).sum := by decide
  have hdescent : baseEnd_2143920 < baseStart_2143920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143954 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2143954 : Nat := 118140960795 + 2143954 * 2 ^ 59
def prefixEnd_2143954 : Nat := 4983230072969 + 3 ^ 40 * 2143954 * 2
def baseEnd_2143954 : Nat := 733919268753073335876761

theorem tailTrace_2143954 : CollatzResearch.WordTrace tailWord_2143954 prefixEnd_2143954 733919268753073335876761 := by
  unfold tailWord_2143954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549106618707072759241729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52130950983218860691311277 19549106618707072759241729)
  ·
    refine ⟨14661829964030304569431297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19549106618707072759241729 14661829964030304569431297)
    ·
      refine ⟨10996372473022728427073473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14661829964030304569431297 10996372473022728427073473)
      ·
        refine ⟨8247279354767046320305105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10996372473022728427073473 8247279354767046320305105)
        ·
          refine ⟨6185459516075284740228829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8247279354767046320305105 6185459516075284740228829)
          ·
            refine ⟨2319547318528231777585811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6185459516075284740228829 2319547318528231777585811)
            ·
              refine ⟨3479320977792347666378717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319547318528231777585811 3479320977792347666378717)
              ·
                refine ⟨1304745366672130374892019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3479320977792347666378717 1304745366672130374892019)
                ·
                  refine ⟨1957118050008195562338029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304745366672130374892019 1957118050008195562338029)
                  ·
                    refine ⟨733919268753073335876761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957118050008195562338029 733919268753073335876761)
                    ·
                      rfl

theorem cell22_2143954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2143954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143954 prefixEnd_2143954 := by exact prefixLift 2143954
  have htrace : WordTrace (prefixWord ++ tailWord_2143954) baseStart_2143954 baseEnd_2143954 := by
    simpa [prefixWord, tailWord_2143954, baseEnd_2143954] using wordTrace_append hprefix tailTrace_2143954
  have hstable : (prefixWord ++ tailWord_2143954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143954).length < 2 ^ (prefixWord ++ tailWord_2143954).sum := by decide
  have hdescent : baseEnd_2143954 < baseStart_2143954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143978 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_2143978 : Nat := 118140960795 + 2143978 * 2 ^ 59
def prefixEnd_2143978 : Nat := 4983230072969 + 3 ^ 40 * 2143978 * 2
def baseEnd_2143978 : Nat := 244642494814515091092229

theorem tailTrace_2143978 : CollatzResearch.WordTrace tailWord_2143978 prefixEnd_2143978 244642494814515091092229 := by
  unfold tailWord_2143978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549325456685335783960147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52131534551160895423893725 19549325456685335783960147)
  ·
    refine ⟨29323988185028003675940221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19549325456685335783960147 29323988185028003675940221)
    ·
      refine ⟨10996495569385501378477583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29323988185028003675940221 10996495569385501378477583)
      ·
        refine ⟨16494743354078252067716375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10996495569385501378477583 16494743354078252067716375)
        ·
          refine ⟨24742115031117378101574563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16494743354078252067716375 24742115031117378101574563)
          ·
            refine ⟨37113172546676067152361845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24742115031117378101574563 37113172546676067152361845)
            ·
              refine ⟨3479359926250881295533923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37113172546676067152361845 3479359926250881295533923)
              ·
                refine ⟨5219039889376321943300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479359926250881295533923 5219039889376321943300885)
                ·
                  refine ⟨244642494814515091092229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5219039889376321943300885 244642494814515091092229)
                  ·
                    rfl

theorem cell22_2143978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_2143978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143978 prefixEnd_2143978 := by exact prefixLift 2143978
  have htrace : WordTrace (prefixWord ++ tailWord_2143978) baseStart_2143978 baseEnd_2143978 := by
    simpa [prefixWord, tailWord_2143978, baseEnd_2143978] using wordTrace_append hprefix tailTrace_2143978
  have hstable : (prefixWord ++ tailWord_2143978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143978).length < 2 ^ (prefixWord ++ tailWord_2143978).sum := by decide
  have hdescent : baseEnd_2143978 < baseStart_2143978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143991 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_2143991 : Nat := 118140960795 + 2143991 * 2 ^ 59
def prefixEnd_2143991 : Nat := 4983230072969 + 3 ^ 40 * 2143991 * 2
def baseEnd_2143991 : Nat := 733931934609217572701647

theorem tailTrace_2143991 : CollatzResearch.WordTrace tailWord_2143991 prefixEnd_2143991 733931934609217572701647 := by
  unfold tailWord_2143991
  simp only [CollatzResearch.WordTrace]
  refine ⟨78197775975694246356063827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52131850650462830904042551 78197775975694246356063827)
  ·
    refine ⟨117296663963541369534095741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78197775975694246356063827 117296663963541369534095741)
    ·
      refine ⟨43986248986328013575285903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117296663963541369534095741 43986248986328013575285903)
      ·
        refine ⟨65979373479492020362928855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43986248986328013575285903 65979373479492020362928855)
        ·
          refine ⟨98969060219238030544393283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65979373479492020362928855 98969060219238030544393283)
          ·
            refine ⟨148453590328857045816589925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98969060219238030544393283 148453590328857045816589925)
            ·
              refine ⟨27835048186660696090610611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148453590328857045816589925 27835048186660696090610611)
              ·
                refine ⟨41752572279991044135915917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27835048186660696090610611 41752572279991044135915917)
                ·
                  refine ⟨15657214604996641550968469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41752572279991044135915917 15657214604996641550968469)
                  ·
                    refine ⟨733931934609217572701647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15657214604996641550968469 733931934609217572701647)
                    ·
                      rfl

theorem cell22_2143991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_2143991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2143991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2143991 prefixEnd_2143991 := by exact prefixLift 2143991
  have htrace : WordTrace (prefixWord ++ tailWord_2143991) baseStart_2143991 baseEnd_2143991 := by
    simpa [prefixWord, tailWord_2143991, baseEnd_2143991] using wordTrace_append hprefix tailTrace_2143991
  have hstable : (prefixWord ++ tailWord_2143991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143991).length < 2 ^ (prefixWord ++ tailWord_2143991).sum := by decide
  have hdescent : baseEnd_2143991 < baseStart_2143991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144040 : List Nat := [2, 1, 5, 1, 1, 4, 1, 7]
def baseStart_2144040 : Nat := 118140960795 + 2144040 * 2 ^ 59
def prefixEnd_2144040 : Nat := 4983230072969 + 3 ^ 40 * 2144040 * 2
def baseEnd_2144040 : Nat := 81549856478955308691833

theorem tailTrace_2144040 : CollatzResearch.WordTrace tailWord_2144040 prefixEnd_2144040 81549856478955308691833 := by
  unfold tailWord_2144040
  simp only [CollatzResearch.WordTrace]
  refine ⟨39099781576258363862298787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52133042101677818483065049 39099781576258363862298787)
  ·
    refine ⟨58649672364387545793448181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39099781576258363862298787 58649672364387545793448181)
    ·
      refine ⟨5498406784161332418135767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58649672364387545793448181 5498406784161332418135767)
      ·
        refine ⟨8247610176241998627203651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498406784161332418135767 8247610176241998627203651)
        ·
          refine ⟨12371415264362997940805477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247610176241998627203651 12371415264362997940805477)
          ·
            refine ⟨2319640362068062113901027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12371415264362997940805477 2319640362068062113901027)
            ·
              refine ⟨3479460543102093170851541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319640362068062113901027 3479460543102093170851541)
              ·
                refine ⟨81549856478955308691833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3479460543102093170851541 81549856478955308691833)
                ·
                  rfl

theorem cell22_2144040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_2144040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144040 prefixEnd_2144040 := by exact prefixLift 2144040
  have htrace : WordTrace (prefixWord ++ tailWord_2144040) baseStart_2144040 baseEnd_2144040 := by
    simpa [prefixWord, tailWord_2144040, baseEnd_2144040] using wordTrace_append hprefix tailTrace_2144040
  have hstable : (prefixWord ++ tailWord_2144040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144040).length < 2 ^ (prefixWord ++ tailWord_2144040).sum := by decide
  have hdescent : baseEnd_2144040 < baseStart_2144040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144057 : List Nat := [1, 2, 1, 7, 1, 1, 3, 6]
def baseStart_2144057 : Nat := 118140960795 + 2144057 * 2 ^ 59
def prefixEnd_2144057 : Nat := 4983230072969 + 3 ^ 40 * 2144057 * 2
def baseEnd_2144057 : Nat := 81550503084223933394605

theorem tailTrace_2144057 : CollatzResearch.WordTrace tailWord_2144057 prefixEnd_2144057 81550503084223933394605 := by
  unfold tailWord_2144057
  simp only [CollatzResearch.WordTrace]
  refine ⟨78200183193455139627966425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52133455462303426418644283 78200183193455139627966425)
  ·
    refine ⟨58650137395091354720974819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78200183193455139627966425 58650137395091354720974819)
    ·
      refine ⟨87975206092637032081462229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58650137395091354720974819 87975206092637032081462229)
      ·
        refine ⟨2061918892796180439409271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 87975206092637032081462229 2061918892796180439409271)
        ·
          refine ⟨3092878339194270659113907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061918892796180439409271 3092878339194270659113907)
          ·
            refine ⟨4639317508791405988670861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092878339194270659113907 4639317508791405988670861)
            ·
              refine ⟨1739744065796777245751573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4639317508791405988670861 1739744065796777245751573)
              ·
                refine ⟨81550503084223933394605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1739744065796777245751573 81550503084223933394605)
                ·
                  rfl

theorem cell22_2144057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 6].length) (baseStart_2144057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144057 prefixEnd_2144057 := by exact prefixLift 2144057
  have htrace : WordTrace (prefixWord ++ tailWord_2144057) baseStart_2144057 baseEnd_2144057 := by
    simpa [prefixWord, tailWord_2144057, baseEnd_2144057] using wordTrace_append hprefix tailTrace_2144057
  have hstable : (prefixWord ++ tailWord_2144057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144057).length < 2 ^ (prefixWord ++ tailWord_2144057).sum := by decide
  have hdescent : baseEnd_2144057 < baseStart_2144057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144072 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2144072 : Nat := 118140960795 + 2144072 * 2 ^ 59
def prefixEnd_2144072 : Nat := 4983230072969 + 3 ^ 40 * 2144072 * 2
def baseEnd_2144072 : Nat := 733959662564560361426399

theorem tailTrace_2144072 : CollatzResearch.WordTrace tailWord_2144072 prefixEnd_2144072 733959662564560361426399 := by
  unfold tailWord_2144072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39100365144200398594881235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52133820192267198126508313 39100365144200398594881235)
  ·
    refine ⟨58650547716300597892321853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39100365144200398594881235 58650547716300597892321853)
    ·
      refine ⟨21993955393612724209620695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58650547716300597892321853 21993955393612724209620695)
      ·
        refine ⟨32990933090419086314431043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21993955393612724209620695 32990933090419086314431043)
        ·
          refine ⟨49486399635628629471646565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32990933090419086314431043 49486399635628629471646565)
          ·
            refine ⟨9278699931680368025933731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49486399635628629471646565 9278699931680368025933731)
            ·
              refine ⟨13918049897520552038900597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9278699931680368025933731 13918049897520552038900597)
              ·
                refine ⟨1304817177892551753646931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13918049897520552038900597 1304817177892551753646931)
                ·
                  refine ⟨1957225766838827630470397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304817177892551753646931 1957225766838827630470397)
                  ·
                    refine ⟨733959662564560361426399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957225766838827630470397 733959662564560361426399)
                    ·
                      rfl

theorem cell22_2144072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2144072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144072 prefixEnd_2144072 := by exact prefixLift 2144072
  have htrace : WordTrace (prefixWord ++ tailWord_2144072) baseStart_2144072 baseEnd_2144072 := by
    simpa [prefixWord, tailWord_2144072, baseEnd_2144072] using wordTrace_append hprefix tailTrace_2144072
  have hstable : (prefixWord ++ tailWord_2144072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144072).length < 2 ^ (prefixWord ++ tailWord_2144072).sum := by decide
  have hdescent : baseEnd_2144072 < baseStart_2144072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144085 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 5]
def baseStart_2144085 : Nat := 118140960795 + 2144085 * 2 ^ 59
def prefixEnd_2144085 : Nat := 4983230072969 + 3 ^ 40 * 2144085 * 2
def baseEnd_2144085 : Nat := 244654704243410886950453

theorem tailTrace_2144085 : CollatzResearch.WordTrace tailWord_2144085 prefixEnd_2144085 244654704243410886950453 := by
  unfold tailWord_2144085
  simp only [CollatzResearch.WordTrace]
  refine ⟨78201204437353700409985709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52134136291569133606657139 78201204437353700409985709)
  ·
    refine ⟨29325451664007637653744641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78201204437353700409985709 29325451664007637653744641)
    ·
      refine ⟨21994088748005728240308481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29325451664007637653744641 21994088748005728240308481)
      ·
        refine ⟨16495566561004296180231361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21994088748005728240308481 16495566561004296180231361)
        ·
          refine ⟨12371674920753222135173521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16495566561004296180231361 12371674920753222135173521)
          ·
            refine ⟨9278756190564916601380141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12371674920753222135173521 9278756190564916601380141)
            ·
              refine ⟨3479533571461843725517553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9278756190564916601380141 3479533571461843725517553)
              ·
                refine ⟨2609650178596382794138165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479533571461843725517553 2609650178596382794138165)
                ·
                  refine ⟨244654704243410886950453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609650178596382794138165 244654704243410886950453)
                  ·
                    rfl

theorem cell22_2144085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_2144085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144085 prefixEnd_2144085 := by exact prefixLift 2144085
  have htrace : WordTrace (prefixWord ++ tailWord_2144085) baseStart_2144085 baseEnd_2144085 := by
    simpa [prefixWord, tailWord_2144085, baseEnd_2144085] using wordTrace_append hprefix tailTrace_2144085
  have hstable : (prefixWord ++ tailWord_2144085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144085).length < 2 ^ (prefixWord ++ tailWord_2144085).sum := by decide
  have hdescent : baseEnd_2144085 < baseStart_2144085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144113 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 6]
def baseStart_2144113 : Nat := 118140960795 + 2144113 * 2 ^ 59
def prefixEnd_2144113 : Nat := 4983230072969 + 3 ^ 40 * 2144113 * 2
def baseEnd_2144113 : Nat := 244657899234149973717091

theorem tailTrace_2144113 : CollatzResearch.WordTrace tailWord_2144113 prefixEnd_2144113 244657899234149973717091 := by
  unfold tailWord_2144113
  simp only [CollatzResearch.WordTrace]
  refine ⟨78202225681252261192004993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52134817120834840794669995 78202225681252261192004993)
  ·
    refine ⟨58651669260939195894003745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78202225681252261192004993 58651669260939195894003745)
    ·
      refine ⟨43988751945704396920502809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58651669260939195894003745 43988751945704396920502809)
      ·
        refine ⟨32991563959278297690377107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43988751945704396920502809 32991563959278297690377107)
        ·
          refine ⟨49487345938917446535565661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32991563959278297690377107 49487345938917446535565661)
          ·
            refine ⟨18557754727094042450837123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49487345938917446535565661 18557754727094042450837123)
            ·
              refine ⟨27836632090641063676255685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18557754727094042450837123 27836632090641063676255685)
              ·
                refine ⟨5219368516995199439297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27836632090641063676255685 5219368516995199439297941)
                ·
                  refine ⟨244657899234149973717091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5219368516995199439297941 244657899234149973717091)
                  ·
                    rfl

theorem cell22_2144113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_2144113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144113 prefixEnd_2144113 := by exact prefixLift 2144113
  have htrace : WordTrace (prefixWord ++ tailWord_2144113) baseStart_2144113 baseEnd_2144113 := by
    simpa [prefixWord, tailWord_2144113, baseEnd_2144113] using wordTrace_append hprefix tailTrace_2144113
  have hstable : (prefixWord ++ tailWord_2144113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144113).length < 2 ^ (prefixWord ++ tailWord_2144113).sum := by decide
  have hdescent : baseEnd_2144113 < baseStart_2144113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144128 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_2144128 : Nat := 118140960795 + 2144128 * 2 ^ 59
def prefixEnd_2144128 : Nat := 4983230072969 + 3 ^ 40 * 2144128 * 2
def baseEnd_2144128 : Nat := 733978832508994882026227

theorem tailTrace_2144128 : CollatzResearch.WordTrace tailWord_2144128 prefixEnd_2144128 733978832508994882026227 := by
  unfold tailWord_2144128
  simp only [CollatzResearch.WordTrace]
  refine ⟨39101386388098959376900519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52135181850798612502534025 39101386388098959376900519)
  ·
    refine ⟨58652079582148439065350779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39101386388098959376900519 58652079582148439065350779)
    ·
      refine ⟨87978119373222658598026169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58652079582148439065350779 87978119373222658598026169)
      ·
        refine ⟨65983589529916993948519627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87978119373222658598026169 65983589529916993948519627)
        ·
          refine ⟨98975384294875490922779441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65983589529916993948519627 98975384294875490922779441)
          ·
            refine ⟨74231538221156618192084581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98975384294875490922779441 74231538221156618192084581)
            ·
              refine ⟨13918413416466865911015859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74231538221156618192084581 13918413416466865911015859)
              ·
                refine ⟨20877620124700298866523789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13918413416466865911015859 20877620124700298866523789)
                ·
                  refine ⟨7829107546762612074946421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20877620124700298866523789 7829107546762612074946421)
                  ·
                    refine ⟨733978832508994882026227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7829107546762612074946421 733978832508994882026227)
                    ·
                      rfl

theorem cell22_2144128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_2144128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144128 prefixEnd_2144128 := by exact prefixLift 2144128
  have htrace : WordTrace (prefixWord ++ tailWord_2144128) baseStart_2144128 baseEnd_2144128 := by
    simpa [prefixWord, tailWord_2144128, baseEnd_2144128] using wordTrace_append hprefix tailTrace_2144128
  have hstable : (prefixWord ++ tailWord_2144128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144128).length < 2 ^ (prefixWord ++ tailWord_2144128).sum := by decide
  have hdescent : baseEnd_2144128 < baseStart_2144128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144145 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2144145 : Nat := 118140960795 + 2144145 * 2 ^ 59
def prefixEnd_2144145 : Nat := 4983230072969 + 3 ^ 40 * 2144145 * 2
def baseEnd_2144145 : Nat := 733984651956412504351175

theorem tailTrace_2144145 : CollatzResearch.WordTrace tailWord_2144145 prefixEnd_2144145 733984651956412504351175 := by
  unfold tailWord_2144145
  simp only [CollatzResearch.WordTrace]
  refine ⟨78203392817136330657169889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52135595211424220438113259 78203392817136330657169889)
  ·
    refine ⟨58652544612852247992877417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78203392817136330657169889 58652544612852247992877417)
    ·
      refine ⟨43989408459639185994658063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58652544612852247992877417 43989408459639185994658063)
      ·
        refine ⟨65984112689458778991987095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43989408459639185994658063 65984112689458778991987095)
        ·
          refine ⟨98976169034188168487980643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65984112689458778991987095 98976169034188168487980643)
          ·
            refine ⟨148464253551282252731970965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98976169034188168487980643 148464253551282252731970965)
            ·
              refine ⟨6959261885216355596811139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148464253551282252731970965 6959261885216355596811139)
              ·
                refine ⟨10438892827824533395216709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6959261885216355596811139 10438892827824533395216709)
                ·
                  refine ⟨1957292405217100011603133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10438892827824533395216709 1957292405217100011603133)
                  ·
                    refine ⟨733984651956412504351175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957292405217100011603133 733984651956412504351175)
                    ·
                      rfl

theorem cell22_2144145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2144145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144145 prefixEnd_2144145 := by exact prefixLift 2144145
  have htrace : WordTrace (prefixWord ++ tailWord_2144145) baseStart_2144145 baseEnd_2144145 := by
    simpa [prefixWord, tailWord_2144145, baseEnd_2144145] using wordTrace_append hprefix tailTrace_2144145
  have hstable : (prefixWord ++ tailWord_2144145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144145).length < 2 ^ (prefixWord ++ tailWord_2144145).sum := by decide
  have hdescent : baseEnd_2144145 < baseStart_2144145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144177 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2144177 : Nat := 118140960795 + 2144177 * 2 ^ 59
def prefixEnd_2144177 : Nat := 4983230072969 + 3 ^ 40 * 2144177 * 2
def baseEnd_2144177 : Nat := 733995606210375087551077

theorem tailTrace_2144177 : CollatzResearch.WordTrace tailWord_2144177 prefixEnd_2144177 733995606210375087551077 := by
  unfold tailWord_2144177
  simp only [CollatzResearch.WordTrace]
  refine ⟨78204559953020400122334785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52136373302013600081556523 78204559953020400122334785)
  ·
    refine ⟨58653419964765300091751089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78204559953020400122334785 58653419964765300091751089)
    ·
      refine ⟨43990064973573975068813317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58653419964765300091751089 43990064973573975068813317)
      ·
        refine ⟨8248137182545120325402497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43990064973573975068813317 8248137182545120325402497)
        ·
          refine ⟨6186102886908840244051873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8248137182545120325402497 6186102886908840244051873)
          ·
            refine ⟨4639577165181630183038905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6186102886908840244051873 4639577165181630183038905)
            ·
              refine ⟨3479682873886222637279179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4639577165181630183038905 3479682873886222637279179)
              ·
                refine ⟨5219524310829333955918769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479682873886222637279179 5219524310829333955918769)
                ·
                  refine ⟨3914643233122000466939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5219524310829333955918769 3914643233122000466939077)
                  ·
                    refine ⟨733995606210375087551077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3914643233122000466939077 733995606210375087551077)
                    ·
                      rfl

theorem cell22_2144177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2144177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144177 prefixEnd_2144177 := by exact prefixLift 2144177
  have htrace : WordTrace (prefixWord ++ tailWord_2144177) baseStart_2144177 baseEnd_2144177 := by
    simpa [prefixWord, tailWord_2144177, baseEnd_2144177] using wordTrace_append hprefix tailTrace_2144177
  have hstable : (prefixWord ++ tailWord_2144177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144177).length < 2 ^ (prefixWord ++ tailWord_2144177).sum := by decide
  have hdescent : baseEnd_2144177 < baseStart_2144177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144241 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2144241 : Nat := 118140960795 + 2144241 * 2 ^ 59
def prefixEnd_2144241 : Nat := 4983230072969 + 3 ^ 40 * 2144241 * 2
def baseEnd_2144241 : Nat := 734017514718300253950881

theorem tailTrace_2144241 : CollatzResearch.WordTrace tailWord_2144241 prefixEnd_2144241 734017514718300253950881 := by
  unfold tailWord_2144241
  simp only [CollatzResearch.WordTrace]
  refine ⟨78206894224788539052664577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52137929483192359368443051 78206894224788539052664577)
  ·
    refine ⟨58655170668591404289498433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78206894224788539052664577 58655170668591404289498433)
    ·
      refine ⟨43991378001443553217123825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58655170668591404289498433 43991378001443553217123825)
      ·
        refine ⟨32993533501082664912842869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43991378001443553217123825 32993533501082664912842869)
        ·
          refine ⟨3093143765726499835579019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32993533501082664912842869 3093143765726499835579019)
          ·
            refine ⟨4639715648589749753368529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093143765726499835579019 4639715648589749753368529)
            ·
              refine ⟨3479786736442312315026397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4639715648589749753368529 3479786736442312315026397)
              ·
                refine ⟨1304920026165867118134899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3479786736442312315026397 1304920026165867118134899)
                ·
                  refine ⟨1957380039248800677202349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304920026165867118134899 1957380039248800677202349)
                  ·
                    refine ⟨734017514718300253950881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957380039248800677202349 734017514718300253950881)
                    ·
                      rfl

theorem cell22_2144241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2144241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144241 prefixEnd_2144241 := by exact prefixLift 2144241
  have htrace : WordTrace (prefixWord ++ tailWord_2144241) baseStart_2144241 baseEnd_2144241 := by
    simpa [prefixWord, tailWord_2144241, baseEnd_2144241] using wordTrace_append hprefix tailTrace_2144241
  have hstable : (prefixWord ++ tailWord_2144241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144241).length < 2 ^ (prefixWord ++ tailWord_2144241).sum := by decide
  have hdescent : baseEnd_2144241 < baseStart_2144241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144254 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2144254 : Nat := 118140960795 + 2144254 * 2 ^ 59
def prefixEnd_2144254 : Nat := 4983230072969 + 3 ^ 40 * 2144254 * 2
def baseEnd_2144254 : Nat := 244673988294657517791947

theorem tailTrace_2144254 : CollatzResearch.WordTrace tailWord_2144254 prefixEnd_2144254 244673988294657517791947 := by
  unfold tailWord_2144254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775921046717680284110977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52138245582494294848591877 9775921046717680284110977)
  ·
    refine ⟨7331940785038260213083233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9775921046717680284110977 7331940785038260213083233)
    ·
      refine ⟨5498955588778695159812425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7331940785038260213083233 5498955588778695159812425)
      ·
        refine ⟨4124216691584021369859319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5498955588778695159812425 4124216691584021369859319)
        ·
          refine ⟨6186325037376032054788979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124216691584021369859319 6186325037376032054788979)
          ·
            refine ⟨9279487556064048082183469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186325037376032054788979 9279487556064048082183469)
            ·
              refine ⟨3479807833524018030818801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9279487556064048082183469 3479807833524018030818801)
              ·
                refine ⟨2609855875143013523114101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479807833524018030818801 2609855875143013523114101)
                ·
                  refine ⟨244673988294657517791947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609855875143013523114101 244673988294657517791947)
                  ·
                    rfl

theorem cell22_2144254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2144254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144254 prefixEnd_2144254 := by exact prefixLift 2144254
  have htrace : WordTrace (prefixWord ++ tailWord_2144254) baseStart_2144254 baseEnd_2144254 := by
    simpa [prefixWord, tailWord_2144254, baseEnd_2144254] using wordTrace_append hprefix tailTrace_2144254
  have hstable : (prefixWord ++ tailWord_2144254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144254).length < 2 ^ (prefixWord ++ tailWord_2144254).sum := by decide
  have hdescent : baseEnd_2144254 < baseStart_2144254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144284 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2144284 : Nat := 118140960795 + 2144284 * 2 ^ 59
def prefixEnd_2144284 : Nat := 4983230072969 + 3 ^ 40 * 2144284 * 2
def baseEnd_2144284 : Nat := 734032234497062475125749

theorem tailTrace_2144284 : CollatzResearch.WordTrace tailWord_2144284 prefixEnd_2144284 734032234497062475125749 := by
  unfold tailWord_2144284
  simp only [CollatzResearch.WordTrace]
  refine ⟨39104231281816378698239953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52138975042421838264319937 39104231281816378698239953)
  ·
    refine ⟨29328173461362284023679965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39104231281816378698239953 29328173461362284023679965)
    ·
      refine ⟨10998065048010856508879987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29328173461362284023679965 10998065048010856508879987)
      ·
        refine ⟨16497097572016284763319981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10998065048010856508879987 16497097572016284763319981)
        ·
          refine ⟨6186411589506106786244993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16497097572016284763319981 6186411589506106786244993)
          ·
            refine ⟨4639808692129580089683745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6186411589506106786244993 4639808692129580089683745)
            ·
              refine ⟨3479856519097185067262809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4639808692129580089683745 3479856519097185067262809)
              ·
                refine ⟨2609892389322888800447107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479856519097185067262809 2609892389322888800447107)
                ·
                  refine ⟨3914838583984333200670661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609892389322888800447107 3914838583984333200670661)
                  ·
                    refine ⟨734032234497062475125749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3914838583984333200670661 734032234497062475125749)
                    ·
                      rfl

theorem cell22_2144284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2144284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144284 prefixEnd_2144284 := by exact prefixLift 2144284
  have htrace : WordTrace (prefixWord ++ tailWord_2144284) baseStart_2144284 baseEnd_2144284 := by
    simpa [prefixWord, tailWord_2144284, baseEnd_2144284] using wordTrace_append hprefix tailTrace_2144284
  have hstable : (prefixWord ++ tailWord_2144284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144284).length < 2 ^ (prefixWord ++ tailWord_2144284).sum := by decide
  have hdescent : baseEnd_2144284 < baseStart_2144284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144355 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 9]
def baseStart_2144355 : Nat := 118140960795 + 2144355 * 2 ^ 59
def prefixEnd_2144355 : Nat := 4983230072969 + 3 ^ 40 * 2144355 * 2
def baseEnd_2144355 : Nat := 244685513082680652200177

theorem tailTrace_2144355 : CollatzResearch.WordTrace tailWord_2144355 prefixEnd_2144355 244685513082680652200177 := by
  unfold tailWord_2144355
  simp only [CollatzResearch.WordTrace]
  refine ⟨78211052146375536522314519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52140701430917024348209679 78211052146375536522314519)
  ·
    refine ⟨117316578219563304783471779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78211052146375536522314519 117316578219563304783471779)
    ·
      refine ⟨175974867329344957175207669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117316578219563304783471779 175974867329344957175207669)
      ·
        refine ⟨16497643812126089735175719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 175974867329344957175207669 16497643812126089735175719)
        ·
          refine ⟨24746465718189134602763579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16497643812126089735175719 24746465718189134602763579)
          ·
            refine ⟨37119698577283701904145369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24746465718189134602763579 37119698577283701904145369)
            ·
              refine ⟨27839773932962776428109027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37119698577283701904145369 27839773932962776428109027)
              ·
                refine ⟨41759660899444164642163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27839773932962776428109027 41759660899444164642163541)
                ·
                  refine ⟨244685513082680652200177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41759660899444164642163541 244685513082680652200177)
                  ·
                    rfl

theorem cell22_2144355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_2144355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144355 prefixEnd_2144355 := by exact prefixLift 2144355
  have htrace : WordTrace (prefixWord ++ tailWord_2144355) baseStart_2144355 baseEnd_2144355 := by
    simpa [prefixWord, tailWord_2144355, baseEnd_2144355] using wordTrace_append hprefix tailTrace_2144355
  have hstable : (prefixWord ++ tailWord_2144355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144355).length < 2 ^ (prefixWord ++ tailWord_2144355).sum := by decide
  have hdescent : baseEnd_2144355 < baseStart_2144355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144387 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_2144387 : Nat := 118140960795 + 2144387 * 2 ^ 59
def prefixEnd_2144387 : Nat := 4983230072969 + 3 ^ 40 * 2144387 * 2
def baseEnd_2144387 : Nat := 734067493502004539800433

theorem tailTrace_2144387 : CollatzResearch.WordTrace tailWord_2144387 prefixEnd_2144387 734067493502004539800433 := by
  unfold tailWord_2144387
  simp only [CollatzResearch.WordTrace]
  refine ⟨78212219282259605987479415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52141479521506403991652943 78212219282259605987479415)
  ·
    refine ⟨117318328923389408981219123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78212219282259605987479415 117318328923389408981219123)
    ·
      refine ⟨175977493385084113471828685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117318328923389408981219123 175977493385084113471828685)
      ·
        refine ⟨65991560019406542551935757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175977493385084113471828685 65991560019406542551935757)
        ·
          refine ⟨24746835007277453456975909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65991560019406542551935757 24746835007277453456975909)
          ·
            refine ⟨4640031563864522523182983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24746835007277453456975909 4640031563864522523182983)
            ·
              refine ⟨6960047345796783784774475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640031563864522523182983 6960047345796783784774475)
              ·
                refine ⟨10440071018695175677161713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960047345796783784774475 10440071018695175677161713)
                ·
                  refine ⟨7830053264021381757871285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10440071018695175677161713 7830053264021381757871285)
                  ·
                    refine ⟨734067493502004539800433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7830053264021381757871285 734067493502004539800433)
                    ·
                      rfl

theorem cell22_2144387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_2144387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144387 prefixEnd_2144387 := by exact prefixLift 2144387
  have htrace : WordTrace (prefixWord ++ tailWord_2144387) baseStart_2144387 baseEnd_2144387 := by
    simpa [prefixWord, tailWord_2144387, baseEnd_2144387] using wordTrace_append hprefix tailTrace_2144387
  have hstable : (prefixWord ++ tailWord_2144387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144387).length < 2 ^ (prefixWord ++ tailWord_2144387).sum := by decide
  have hdescent : baseEnd_2144387 < baseStart_2144387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144423 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 5]
def baseStart_2144423 : Nat := 118140960795 + 2144423 * 2 ^ 59
def prefixEnd_2144423 : Nat := 4983230072969 + 3 ^ 40 * 2144423 * 2
def baseEnd_2144423 : Nat := 244693272345904148633441

theorem tailTrace_2144423 : CollatzResearch.WordTrace tailWord_2144423 prefixEnd_2144423 244693272345904148633441 := by
  unfold tailWord_2144423
  simp only [CollatzResearch.WordTrace]
  refine ⟨78213532310129184135789923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52142354873419456090526615 78213532310129184135789923)
  ·
    refine ⟨117320298465193776203684885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78213532310129184135789923 117320298465193776203684885)
    ·
      refine ⟨5499388990555958259547729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117320298465193776203684885 5499388990555958259547729)
      ·
        refine ⟨4124541742916968694660797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5499388990555958259547729 4124541742916968694660797)
        ·
          refine ⟨1546703153593863260497799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4124541742916968694660797 1546703153593863260497799)
          ·
            refine ⟨2320054730390794890746699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546703153593863260497799 2320054730390794890746699)
            ·
              refine ⟨3480082095586192336120049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320054730390794890746699 3480082095586192336120049)
              ·
                refine ⟨2610061571689644252090037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3480082095586192336120049 2610061571689644252090037)
                ·
                  refine ⟨244693272345904148633441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610061571689644252090037 244693272345904148633441)
                  ·
                    rfl

theorem cell22_2144423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 5].length) (baseStart_2144423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144423 prefixEnd_2144423 := by exact prefixLift 2144423
  have htrace : WordTrace (prefixWord ++ tailWord_2144423) baseStart_2144423 baseEnd_2144423 := by
    simpa [prefixWord, tailWord_2144423, baseEnd_2144423] using wordTrace_append hprefix tailTrace_2144423
  have hstable : (prefixWord ++ tailWord_2144423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144423).length < 2 ^ (prefixWord ++ tailWord_2144423).sum := by decide
  have hdescent : baseEnd_2144423 < baseStart_2144423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144434 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 4]
def baseStart_2144434 : Nat := 118140960795 + 2144434 * 2 ^ 59
def prefixEnd_2144434 : Nat := 4983230072969 + 3 ^ 40 * 2144434 * 2
def baseEnd_2144434 : Nat := 244694527520837361291763

theorem tailTrace_2144434 : CollatzResearch.WordTrace tailWord_2144434 prefixEnd_2144434 244694527520837361291763 := by
  unfold tailWord_2144434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553483378272333253610089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52142622342059555342960237 19553483378272333253610089)
  ·
    refine ⟨14665112533704249940207567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19553483378272333253610089 14665112533704249940207567)
    ·
      refine ⟨21997668800556374910311351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14665112533704249940207567 21997668800556374910311351)
      ·
        refine ⟨32996503200834562365467027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21997668800556374910311351 32996503200834562365467027)
        ·
          refine ⟨49494754801251843548200541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32996503200834562365467027 49494754801251843548200541)
          ·
            refine ⟨18560533050469441330575203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49494754801251843548200541 18560533050469441330575203)
            ·
              refine ⟨27840799575704161995862805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18560533050469441330575203 27840799575704161995862805)
              ·
                refine ⟨1305037480111132593556069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27840799575704161995862805 1305037480111132593556069)
                ·
                  refine ⟨244694527520837361291763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305037480111132593556069 244694527520837361291763)
                  ·
                    rfl

theorem cell22_2144434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_2144434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144434 prefixEnd_2144434 := by exact prefixLift 2144434
  have htrace : WordTrace (prefixWord ++ tailWord_2144434) baseStart_2144434 baseEnd_2144434 := by
    simpa [prefixWord, tailWord_2144434, baseEnd_2144434] using wordTrace_append hprefix tailTrace_2144434
  have hstable : (prefixWord ++ tailWord_2144434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144434).length < 2 ^ (prefixWord ++ tailWord_2144434).sum := by decide
  have hdescent : baseEnd_2144434 < baseStart_2144434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144492 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_2144492 : Nat := 118140960795 + 2144492 * 2 ^ 59
def prefixEnd_2144492 : Nat := 4983230072969 + 3 ^ 40 * 2144492 * 2
def baseEnd_2144492 : Nat := 734103437147819265925111

theorem tailTrace_2144492 : CollatzResearch.WordTrace tailWord_2144492 prefixEnd_2144492 734103437147819265925111 := by
  unfold tailWord_2144492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39108024473439604460025865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52144032631252805946701153 39108024473439604460025865)
  ·
    refine ⟨29331018355079703345019399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39108024473439604460025865 29331018355079703345019399)
    ·
      refine ⟨43996527532619555017529099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29331018355079703345019399 43996527532619555017529099)
      ·
        refine ⟨65994791298929332526293649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43996527532619555017529099 65994791298929332526293649)
        ·
          refine ⟨49496093474196999394720237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65994791298929332526293649 49496093474196999394720237)
          ·
            refine ⟨18561035052823874773020089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49496093474196999394720237 18561035052823874773020089)
            ·
              refine ⟨13920776289617906079765067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18561035052823874773020089 13920776289617906079765067)
              ·
                refine ⟨20881164434426859119647601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13920776289617906079765067 20881164434426859119647601)
                ·
                  refine ⟨15660873325820144339735701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20881164434426859119647601 15660873325820144339735701)
                  ·
                    refine ⟨734103437147819265925111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15660873325820144339735701 734103437147819265925111)
                    ·
                      rfl

theorem cell22_2144492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_2144492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144492 prefixEnd_2144492 := by exact prefixLift 2144492
  have htrace : WordTrace (prefixWord ++ tailWord_2144492) baseStart_2144492 baseEnd_2144492 := by
    simpa [prefixWord, tailWord_2144492, baseEnd_2144492] using wordTrace_append hprefix tailTrace_2144492
  have hstable : (prefixWord ++ tailWord_2144492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144492).length < 2 ^ (prefixWord ++ tailWord_2144492).sum := by decide
  have hdescent : baseEnd_2144492 < baseStart_2144492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144569 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 8]
def baseStart_2144569 : Nat := 118140960795 + 2144569 * 2 ^ 59
def prefixEnd_2144569 : Nat := 4983230072969 + 3 ^ 40 * 2144569 * 2
def baseEnd_2144569 : Nat := 244709931940472243916625

theorem tailTrace_2144569 : CollatzResearch.WordTrace tailWord_2144569 prefixEnd_2144569 244709931940472243916625 := by
  unfold tailWord_2144569
  simp only [CollatzResearch.WordTrace]
  refine ⟨78218857367600251070604761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52145904911733500713736507 78218857367600251070604761)
  ·
    refine ⟨58664143025700188302953571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78218857367600251070604761 58664143025700188302953571)
    ·
      refine ⟨87996214538550282454430357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58664143025700188302953571 87996214538550282454430357)
      ·
        refine ⟨4124822556494544490051423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87996214538550282454430357 4124822556494544490051423)
        ·
          refine ⟨6187233834741816735077135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124822556494544490051423 6187233834741816735077135)
          ·
            refine ⟨9280850752112725102615703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187233834741816735077135 9280850752112725102615703)
            ·
              refine ⟨13921276128169087653923555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9280850752112725102615703 13921276128169087653923555)
              ·
                refine ⟨20881914192253631480885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13921276128169087653923555 20881914192253631480885333)
                ·
                  refine ⟨244709931940472243916625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20881914192253631480885333 244709931940472243916625)
                  ·
                    rfl

theorem cell22_2144569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_2144569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144569 prefixEnd_2144569 := by exact prefixLift 2144569
  have htrace : WordTrace (prefixWord ++ tailWord_2144569) baseStart_2144569 baseEnd_2144569 := by
    simpa [prefixWord, tailWord_2144569, baseEnd_2144569] using wordTrace_append hprefix tailTrace_2144569
  have hstable : (prefixWord ++ tailWord_2144569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144569).length < 2 ^ (prefixWord ++ tailWord_2144569).sum := by decide
  have hdescent : baseEnd_2144569 < baseStart_2144569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144584 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2144584 : Nat := 118140960795 + 2144584 * 2 ^ 59
def prefixEnd_2144584 : Nat := 4983230072969 + 3 ^ 40 * 2144584 * 2
def baseEnd_2144584 : Nat := 734134930627961692624829

theorem tailTrace_2144584 : CollatzResearch.WordTrace tailWord_2144584 prefixEnd_2144584 734134930627961692624829 := by
  unfold tailWord_2144584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39109702231272954316200403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52146269641697272421600537 39109702231272954316200403)
  ·
    refine ⟨58664553346909431474300605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39109702231272954316200403 58664553346909431474300605)
    ·
      refine ⟨21999207505091036802862727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58664553346909431474300605 21999207505091036802862727)
      ·
        refine ⟨32998811257636555204294091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21999207505091036802862727 32998811257636555204294091)
        ·
          refine ⟨49498216886454832806441137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32998811257636555204294091 49498216886454832806441137)
          ·
            refine ⟨37123662664841124604830853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49498216886454832806441137 37123662664841124604830853)
            ·
              refine ⟨6960686749657710863405785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37123662664841124604830853 6960686749657710863405785)
              ·
                refine ⟨5220515062243283147554339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6960686749657710863405785 5220515062243283147554339)
                ·
                  refine ⟨7830772593364924721331509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220515062243283147554339 7830772593364924721331509)
                  ·
                    refine ⟨734134930627961692624829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7830772593364924721331509 734134930627961692624829)
                    ·
                      rfl

theorem cell22_2144584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2144584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144584 prefixEnd_2144584 := by exact prefixLift 2144584
  have htrace : WordTrace (prefixWord ++ tailWord_2144584) baseStart_2144584 baseEnd_2144584 := by
    simpa [prefixWord, tailWord_2144584, baseEnd_2144584] using wordTrace_append hprefix tailTrace_2144584
  have hstable : (prefixWord ++ tailWord_2144584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144584).length < 2 ^ (prefixWord ++ tailWord_2144584).sum := by decide
  have hdescent : baseEnd_2144584 < baseStart_2144584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144599 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2144599 : Nat := 118140960795 + 2144599 * 2 ^ 59
def prefixEnd_2144599 : Nat := 4983230072969 + 3 ^ 40 * 2144599 * 2
def baseEnd_2144599 : Nat := 734140065434506653499783

theorem tailTrace_2144599 : CollatzResearch.WordTrace tailWord_2144599 prefixEnd_2144599 734140065434506653499783 := by
  unfold tailWord_2144599
  simp only [CollatzResearch.WordTrace]
  refine ⟨78219951557491566194196851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52146634371661044129464567 78219951557491566194196851)
  ·
    refine ⟨117329927336237349291295277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78219951557491566194196851 117329927336237349291295277)
    ·
      refine ⟨43998722751089005984235729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117329927336237349291295277 43998722751089005984235729)
      ·
        refine ⟨32999042063316754488176797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43998722751089005984235729 32999042063316754488176797)
        ·
          refine ⟨12374640773743782933066299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32999042063316754488176797 12374640773743782933066299)
          ·
            refine ⟨18561961160615674399599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12374640773743782933066299 18561961160615674399599449)
            ·
              refine ⟨13921470870461755799699587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18561961160615674399599449 13921470870461755799699587)
              ·
                refine ⟨20882206305692633699549381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13921470870461755799699587 20882206305692633699549381)
                ·
                  refine ⟨3915413682317368818665509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20882206305692633699549381 3915413682317368818665509)
                  ·
                    refine ⟨734140065434506653499783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3915413682317368818665509 734140065434506653499783)
                    ·
                      rfl

theorem cell22_2144599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2144599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144599 prefixEnd_2144599 := by exact prefixLift 2144599
  have htrace : WordTrace (prefixWord ++ tailWord_2144599) baseStart_2144599 baseEnd_2144599 := by
    simpa [prefixWord, tailWord_2144599, baseEnd_2144599] using wordTrace_append hprefix tailTrace_2144599
  have hstable : (prefixWord ++ tailWord_2144599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144599).length < 2 ^ (prefixWord ++ tailWord_2144599).sum := by decide
  have hdescent : baseEnd_2144599 < baseStart_2144599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144618 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2144618 : Nat := 118140960795 + 2144618 * 2 ^ 59
def prefixEnd_2144618 : Nat := 4983230072969 + 3 ^ 40 * 2144618 * 2
def baseEnd_2144618 : Nat := 734146569522796937274725

theorem tailTrace_2144618 : CollatzResearch.WordTrace tailWord_2144618 prefixEnd_2144618 734146569522796937274725 := by
  unfold tailWord_2144618
  simp only [CollatzResearch.WordTrace]
  refine ⟨19555161136105683109784627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52147096362948488292759005 19555161136105683109784627)
  ·
    refine ⟨29332741704158524664676941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19555161136105683109784627 29332741704158524664676941)
    ·
      refine ⟨10999778139059446749253853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29332741704158524664676941 10999778139059446749253853)
      ·
        refine ⟨4124916802147292530970195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10999778139059446749253853 4124916802147292530970195)
        ·
          refine ⟨6187375203220938796455293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124916802147292530970195 6187375203220938796455293)
          ·
            refine ⟨2320265701207852048670735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6187375203220938796455293 2320265701207852048670735)
            ·
              refine ⟨3480398551811778073006103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320265701207852048670735 3480398551811778073006103)
              ·
                refine ⟨5220597827717667109509155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480398551811778073006103 5220597827717667109509155)
                ·
                  refine ⟨7830896741576500664263733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220597827717667109509155 7830896741576500664263733)
                  ·
                    refine ⟨734146569522796937274725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7830896741576500664263733 734146569522796937274725)
                    ·
                      rfl

theorem cell22_2144618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2144618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144618 prefixEnd_2144618 := by exact prefixLift 2144618
  have htrace : WordTrace (prefixWord ++ tailWord_2144618) baseStart_2144618 baseEnd_2144618 := by
    simpa [prefixWord, tailWord_2144618, baseEnd_2144618] using wordTrace_append hprefix tailTrace_2144618
  have hstable : (prefixWord ++ tailWord_2144618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144618).length < 2 ^ (prefixWord ++ tailWord_2144618).sum := by decide
  have hdescent : baseEnd_2144618 < baseStart_2144618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144663 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 1, 3]
def baseStart_2144663 : Nat := 118140960795 + 2144663 * 2 ^ 59
def prefixEnd_2144663 : Nat := 4983230072969 + 3 ^ 40 * 2144663 * 2
def baseEnd_2144663 : Nat := 734161973942431819899587

theorem tailTrace_2144663 : CollatzResearch.WordTrace tailWord_2144663 prefixEnd_2144663 734161973942431819899587 := by
  unfold tailWord_2144663
  simp only [CollatzResearch.WordTrace]
  refine ⟨78222285829259705124526643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52148190552839803416351095 78222285829259705124526643)
  ·
    refine ⟨117333428743889557686789965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78222285829259705124526643 117333428743889557686789965)
    ·
      refine ⟨44000035778958584132546237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117333428743889557686789965 44000035778958584132546237)
      ·
        refine ⟨16500013417109469049704839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44000035778958584132546237 16500013417109469049704839)
        ·
          refine ⟨24750020125664203574557259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16500013417109469049704839 24750020125664203574557259)
          ·
            refine ⟨37125030188496305361835889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24750020125664203574557259 37125030188496305361835889)
            ·
              refine ⟨27843772641372229021376917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37125030188496305361835889 27843772641372229021376917)
              ·
                refine ⟨1305176842564323235377043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27843772641372229021376917 1305176842564323235377043)
                ·
                  refine ⟨1957765263846484853065565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305176842564323235377043 1957765263846484853065565)
                  ·
                    refine ⟨734161973942431819899587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1957765263846484853065565 734161973942431819899587)
                    ·
                      rfl

theorem cell22_2144663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_2144663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144663 prefixEnd_2144663 := by exact prefixLift 2144663
  have htrace : WordTrace (prefixWord ++ tailWord_2144663) baseStart_2144663 baseEnd_2144663 := by
    simpa [prefixWord, tailWord_2144663, baseEnd_2144663] using wordTrace_append hprefix tailTrace_2144663
  have hstable : (prefixWord ++ tailWord_2144663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144663).length < 2 ^ (prefixWord ++ tailWord_2144663).sum := by decide
  have hdescent : baseEnd_2144663 < baseStart_2144663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144719 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_2144719 : Nat := 118140960795 + 2144719 * 2 ^ 59
def prefixEnd_2144719 : Nat := 4983230072969 + 3 ^ 40 * 2144719 * 2
def baseEnd_2144719 : Nat := 734181143886866340499415

theorem tailTrace_2144719 : CollatzResearch.WordTrace tailWord_2144719 prefixEnd_2144719 734181143886866340499415 := by
  unfold tailWord_2144719
  simp only [CollatzResearch.WordTrace]
  refine ⟨78224328317056826688565211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52149552211371217792376807 78224328317056826688565211)
  ·
    refine ⟨117336492475585240032847817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78224328317056826688565211 117336492475585240032847817)
    ·
      refine ⟨88002369356688930024635863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117336492475585240032847817 88002369356688930024635863)
      ·
        refine ⟨132003554035033395036953795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88002369356688930024635863 132003554035033395036953795)
        ·
          refine ⟨198005331052550092555430693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132003554035033395036953795 198005331052550092555430693)
          ·
            refine ⟨37125999572353142354143255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198005331052550092555430693 37125999572353142354143255)
            ·
              refine ⟨55688999358529713531214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37125999572353142354143255 55688999358529713531214883)
              ·
                refine ⟨83533499037794570296822325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55688999358529713531214883 83533499037794570296822325)
                ·
                  refine ⟨7831265534793240965327093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83533499037794570296822325 7831265534793240965327093)
                  ·
                    refine ⟨734181143886866340499415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7831265534793240965327093 734181143886866340499415)
                    ·
                      rfl

theorem cell22_2144719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_2144719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144719 prefixEnd_2144719 := by exact prefixLift 2144719
  have htrace : WordTrace (prefixWord ++ tailWord_2144719) baseStart_2144719 baseEnd_2144719 := by
    simpa [prefixWord, tailWord_2144719, baseEnd_2144719] using wordTrace_append hprefix tailTrace_2144719
  have hstable : (prefixWord ++ tailWord_2144719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144719).length < 2 ^ (prefixWord ++ tailWord_2144719).sum := by decide
  have hdescent : baseEnd_2144719 < baseStart_2144719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144736 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_2144736 : Nat := 118140960795 + 2144736 * 2 ^ 59
def prefixEnd_2144736 : Nat := 4983230072969 + 3 ^ 40 * 2144736 * 2
def baseEnd_2144736 : Nat := 734186963334283962824363

theorem tailTrace_2144736 : CollatzResearch.WordTrace tailWord_2144736 prefixEnd_2144736 734186963334283962824363 := by
  unfold tailWord_2144736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39112474178997619295967031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52149965571996825727956041 39112474178997619295967031)
  ·
    refine ⟨58668711268496428943950547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39112474178997619295967031 58668711268496428943950547)
    ·
      refine ⟨88003066902744643415925821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58668711268496428943950547 88003066902744643415925821)
      ·
        refine ⟨33001150088529241280972183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88003066902744643415925821 33001150088529241280972183)
        ·
          refine ⟨49501725132793861921458275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33001150088529241280972183 49501725132793861921458275)
          ·
            refine ⟨74252587699190792882187413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49501725132793861921458275 74252587699190792882187413)
            ·
              refine ⟨3480590048399568416352535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74252587699190792882187413 3480590048399568416352535)
              ·
                refine ⟨5220885072599352624528803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480590048399568416352535 5220885072599352624528803)
                ·
                  refine ⟨7831327608899028936793205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220885072599352624528803 7831327608899028936793205)
                  ·
                    refine ⟨734186963334283962824363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7831327608899028936793205 734186963334283962824363)
                    ·
                      rfl

theorem cell22_2144736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_2144736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144736 prefixEnd_2144736 := by exact prefixLift 2144736
  have htrace : WordTrace (prefixWord ++ tailWord_2144736) baseStart_2144736 baseEnd_2144736 := by
    simpa [prefixWord, tailWord_2144736, baseEnd_2144736] using wordTrace_append hprefix tailTrace_2144736
  have hstable : (prefixWord ++ tailWord_2144736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144736).length < 2 ^ (prefixWord ++ tailWord_2144736).sum := by decide
  have hdescent : baseEnd_2144736 < baseStart_2144736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144800 : List Nat := [2, 1, 1, 6, 2, 2, 2, 6]
def baseStart_2144800 : Nat := 118140960795 + 2144800 * 2 ^ 59
def prefixEnd_2144800 : Nat := 4983230072969 + 3 ^ 40 * 2144800 * 2
def baseEnd_2144800 : Nat := 81578763538023236580463

theorem tailTrace_2144800 : CollatzResearch.WordTrace tailWord_2144800 prefixEnd_2144800 81578763538023236580463 := by
  unfold tailWord_2144800
  simp only [CollatzResearch.WordTrace]
  refine ⟨39113641314881688761131927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52151521753175585014842569 39113641314881688761131927)
  ·
    refine ⟨58670461972322533141697891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39113641314881688761131927 58670461972322533141697891)
    ·
      refine ⟨88005692958483799712546837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58670461972322533141697891 88005692958483799712546837)
      ·
        refine ⟨4125266857428928111525633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88005692958483799712546837 4125266857428928111525633)
        ·
          refine ⟨3093950143071696083644225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125266857428928111525633 3093950143071696083644225)
          ·
            refine ⟨2320462607303772062733169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3093950143071696083644225 2320462607303772062733169)
            ·
              refine ⟨1740346955477829047049877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320462607303772062733169 1740346955477829047049877)
              ·
                refine ⟨81578763538023236580463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1740346955477829047049877 81578763538023236580463)
                ·
                  rfl

theorem cell22_2144800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_2144800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144800 prefixEnd_2144800 := by exact prefixLift 2144800
  have htrace : WordTrace (prefixWord ++ tailWord_2144800) baseStart_2144800 baseEnd_2144800 := by
    simpa [prefixWord, tailWord_2144800, baseEnd_2144800] using wordTrace_append hprefix tailTrace_2144800
  have hstable : (prefixWord ++ tailWord_2144800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144800).length < 2 ^ (prefixWord ++ tailWord_2144800).sum := by decide
  have hdescent : baseEnd_2144800 < baseStart_2144800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144845 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2144845 : Nat := 118140960795 + 2144845 * 2 ^ 59
def prefixEnd_2144845 : Nat := 4983230072969 + 3 ^ 40 * 2144845 * 2
def baseEnd_2144845 : Nat := 244741425420614670616343

theorem tailTrace_2144845 : CollatzResearch.WordTrace tailWord_2144845 prefixEnd_2144845 244741425420614670616343 := by
  unfold tailWord_2144845
  simp only [CollatzResearch.WordTrace]
  refine ⟨78228923914600350207651989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52152615943066900138434659 78228923914600350207651989)
  ·
    refine ⟨3666980808496891415983687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78228923914600350207651989 3666980808496891415983687)
    ·
      refine ⟨5500471212745337123975531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666980808496891415983687 5500471212745337123975531)
      ·
        refine ⟨8250706819118005685963297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500471212745337123975531 8250706819118005685963297)
        ·
          refine ⟨6188030114338504264472473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8250706819118005685963297 6188030114338504264472473)
          ·
            refine ⟨4641022585753878198354355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6188030114338504264472473 4641022585753878198354355)
            ·
              refine ⟨6961533878630817297531533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641022585753878198354355 6961533878630817297531533)
              ·
                refine ⟨2610575204486556486574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6961533878630817297531533 2610575204486556486574325)
                ·
                  refine ⟨244741425420614670616343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610575204486556486574325 244741425420614670616343)
                  ·
                    rfl

theorem cell22_2144845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2144845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144845 prefixEnd_2144845 := by exact prefixLift 2144845
  have htrace : WordTrace (prefixWord ++ tailWord_2144845) baseStart_2144845 baseEnd_2144845 := by
    simpa [prefixWord, tailWord_2144845, baseEnd_2144845] using wordTrace_append hprefix tailTrace_2144845
  have hstable : (prefixWord ++ tailWord_2144845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144845).length < 2 ^ (prefixWord ++ tailWord_2144845).sum := by decide
  have hdescent : baseEnd_2144845 < baseStart_2144845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144856 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_2144856 : Nat := 118140960795 + 2144856 * 2 ^ 59
def prefixEnd_2144856 : Nat := 4983230072969 + 3 ^ 40 * 2144856 * 2
def baseEnd_2144856 : Nat := 244742680595547883274665

theorem tailTrace_2144856 : CollatzResearch.WordTrace tailWord_2144856 prefixEnd_2144856 244742680595547883274665 := by
  unfold tailWord_2144856
  simp only [CollatzResearch.WordTrace]
  refine ⟨39114662558780249543151211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52152883411706999390868281 39114662558780249543151211)
  ·
    refine ⟨58671993838170374314726817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39114662558780249543151211 58671993838170374314726817)
    ·
      refine ⟨44003995378627780736045113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58671993838170374314726817 44003995378627780736045113)
      ·
        refine ⟨33002996533970835552033835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44003995378627780736045113 33002996533970835552033835)
        ·
          refine ⟨49504494800956253328050753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33002996533970835552033835 49504494800956253328050753)
          ·
            refine ⟨37128371100717189996038065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49504494800956253328050753 37128371100717189996038065)
            ·
              refine ⟨27846278325537892497028549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37128371100717189996038065 27846278325537892497028549)
              ·
                refine ⟨5221177186038354843192853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27846278325537892497028549 5221177186038354843192853)
                ·
                  refine ⟨244742680595547883274665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5221177186038354843192853 244742680595547883274665)
                  ·
                    rfl

theorem cell22_2144856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_2144856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144856 prefixEnd_2144856 := by exact prefixLift 2144856
  have htrace : WordTrace (prefixWord ++ tailWord_2144856) baseStart_2144856 baseEnd_2144856 := by
    simpa [prefixWord, tailWord_2144856, baseEnd_2144856] using wordTrace_append hprefix tailTrace_2144856
  have hstable : (prefixWord ++ tailWord_2144856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144856).length < 2 ^ (prefixWord ++ tailWord_2144856).sum := by decide
  have hdescent : baseEnd_2144856 < baseStart_2144856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144873 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 4]
def baseStart_2144873 : Nat := 118140960795 + 2144873 * 2 ^ 59
def prefixEnd_2144873 : Nat := 4983230072969 + 3 ^ 40 * 2144873 * 2
def baseEnd_2144873 : Nat := 244744620411353757382981

theorem tailTrace_2144873 : CollatzResearch.WordTrace tailWord_2144873 prefixEnd_2144873 244744620411353757382981 := by
  unfold tailWord_2144873
  simp only [CollatzResearch.WordTrace]
  refine ⟨78229945158498910989671273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52153296772332607326447515 78229945158498910989671273)
  ·
    refine ⟨58672458868874183242253455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78229945158498910989671273 58672458868874183242253455)
    ·
      refine ⟨88008688303311274863380183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58672458868874183242253455 88008688303311274863380183)
      ·
        refine ⟨132013032454966912295070275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88008688303311274863380183 132013032454966912295070275)
        ·
          refine ⟨198019548682450368442605413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132013032454966912295070275 198019548682450368442605413)
          ·
            refine ⟨37128665377959444082988515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198019548682450368442605413 37128665377959444082988515)
            ·
              refine ⟨55692998066939166124482773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37128665377959444082988515 55692998066939166124482773)
              ·
                refine ⟨1305304642193886706042565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55692998066939166124482773 1305304642193886706042565)
                ·
                  refine ⟨244744620411353757382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305304642193886706042565 244744620411353757382981)
                  ·
                    rfl

theorem cell22_2144873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_2144873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144873 prefixEnd_2144873 := by exact prefixLift 2144873
  have htrace : WordTrace (prefixWord ++ tailWord_2144873) baseStart_2144873 baseEnd_2144873 := by
    simpa [prefixWord, tailWord_2144873, baseEnd_2144873] using wordTrace_append hprefix tailTrace_2144873
  have hstable : (prefixWord ++ tailWord_2144873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144873).length < 2 ^ (prefixWord ++ tailWord_2144873).sum := by decide
  have hdescent : baseEnd_2144873 < baseStart_2144873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144931 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_2144931 : Nat := 118140960795 + 2144931 * 2 ^ 59
def prefixEnd_2144931 : Nat := 4983230072969 + 3 ^ 40 * 2144931 * 2
def baseEnd_2144931 : Nat := 734253715819368454198765

theorem tailTrace_2144931 : CollatzResearch.WordTrace tailWord_2144931 prefixEnd_2144931 734253715819368454198765 := by
  unfold tailWord_2144931
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232060592288786895282647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52154707061525857930188431 78232060592288786895282647)
  ·
    refine ⟨117348090888433180342923971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78232060592288786895282647 117348090888433180342923971)
    ·
      refine ⟨176022136332649770514385957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117348090888433180342923971 176022136332649770514385957)
      ·
        refine ⟨33004150562371831971447367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176022136332649770514385957 33004150562371831971447367)
        ·
          refine ⟨49506225843557747957171051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33004150562371831971447367 49506225843557747957171051)
          ·
            refine ⟨74259338765336621935756577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49506225843557747957171051 74259338765336621935756577)
            ·
              refine ⟨55694504074002466451817433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74259338765336621935756577 55694504074002466451817433)
              ·
                refine ⟨41770878055501849838863075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55694504074002466451817433 41770878055501849838863075)
                ·
                  refine ⟨62656317083252774758294613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41770878055501849838863075 62656317083252774758294613)
                  ·
                    refine ⟨734253715819368454198765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62656317083252774758294613 734253715819368454198765)
                    ·
                      rfl

theorem cell22_2144931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_2144931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144931 prefixEnd_2144931 := by exact prefixLift 2144931
  have htrace : WordTrace (prefixWord ++ tailWord_2144931) baseStart_2144931 baseEnd_2144931 := by
    simpa [prefixWord, tailWord_2144931, baseEnd_2144931] using wordTrace_append hprefix tailTrace_2144931
  have hstable : (prefixWord ++ tailWord_2144931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144931).length < 2 ^ (prefixWord ++ tailWord_2144931).sum := by decide
  have hdescent : baseEnd_2144931 < baseStart_2144931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144933 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_2144933 : Nat := 118140960795 + 2144933 * 2 ^ 59
def prefixEnd_2144933 : Nat := 4983230072969 + 3 ^ 40 * 2144933 * 2
def baseEnd_2144933 : Nat := 734254400460241115648759

theorem tailTrace_2144933 : CollatzResearch.WordTrace tailWord_2144933 prefixEnd_2144933 734254400460241115648759 := by
  unfold tailWord_2144933
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232133538281541236855453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52154755692187694157903635 78232133538281541236855453)
  ·
    refine ⟨29337050076855577963820795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78232133538281541236855453 29337050076855577963820795)
    ·
      refine ⟨44005575115283366945731193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29337050076855577963820795 44005575115283366945731193)
      ·
        refine ⟨33004181336462525209298395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44005575115283366945731193 33004181336462525209298395)
        ·
          refine ⟨49506272004693787813947593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33004181336462525209298395 49506272004693787813947593)
          ·
            refine ⟨37129704003520340860460695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49506272004693787813947593 37129704003520340860460695)
            ·
              refine ⟨55694556005280511290691043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37129704003520340860460695 55694556005280511290691043)
              ·
                refine ⟨83541834007920766936036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55694556005280511290691043 83541834007920766936036565)
                ·
                  refine ⟨1958011734560642975063357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 83541834007920766936036565 1958011734560642975063357)
                  ·
                    refine ⟨734254400460241115648759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958011734560642975063357 734254400460241115648759)
                    ·
                      rfl

theorem cell22_2144933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_2144933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144933 prefixEnd_2144933 := by exact prefixLift 2144933
  have htrace : WordTrace (prefixWord ++ tailWord_2144933) baseStart_2144933 baseEnd_2144933 := by
    simpa [prefixWord, tailWord_2144933, baseEnd_2144933] using wordTrace_append hprefix tailTrace_2144933
  have hstable : (prefixWord ++ tailWord_2144933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144933).length < 2 ^ (prefixWord ++ tailWord_2144933).sum := by decide
  have hdescent : baseEnd_2144933 < baseStart_2144933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144935 : List Nat := [1, 1, 6, 3, 1, 1, 9]
def baseStart_2144935 : Nat := 118140960795 + 2144935 * 2 ^ 59
def prefixEnd_2144935 : Nat := 4983230072969 + 3 ^ 40 * 2144935 * 2
def baseEnd_2144935 : Nat := 27194632781522732485139

theorem tailTrace_2144935 : CollatzResearch.WordTrace tailWord_2144935 prefixEnd_2144935 27194632781522732485139 := by
  unfold tailWord_2144935
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232206484274295578428259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52154804322849530385618839 78232206484274295578428259)
  ·
    refine ⟨117348309726411443367642389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78232206484274295578428259 117348309726411443367642389)
    ·
      refine ⟨5500702018425536407858237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117348309726411443367642389 5500702018425536407858237)
      ·
        refine ⟨2062763256909576152946839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5500702018425536407858237 2062763256909576152946839)
        ·
          refine ⟨3094144885364364229420259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062763256909576152946839 3094144885364364229420259)
          ·
            refine ⟨4641217328046546344130389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094144885364364229420259 4641217328046546344130389)
            ·
              refine ⟨27194632781522732485139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4641217328046546344130389 27194632781522732485139)
              ·
                rfl

theorem cell22_2144935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 9].length) (baseStart_2144935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144935 prefixEnd_2144935 := by exact prefixLift 2144935
  have htrace : WordTrace (prefixWord ++ tailWord_2144935) baseStart_2144935 baseEnd_2144935 := by
    simpa [prefixWord, tailWord_2144935, baseEnd_2144935] using wordTrace_append hprefix tailTrace_2144935
  have hstable : (prefixWord ++ tailWord_2144935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144935).length < 2 ^ (prefixWord ++ tailWord_2144935).sum := by decide
  have hdescent : baseEnd_2144935 < baseStart_2144935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144984 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_2144984 : Nat := 118140960795 + 2144984 * 2 ^ 59
def prefixEnd_2144984 : Nat := 4983230072969 + 3 ^ 40 * 2144984 * 2
def baseEnd_2144984 : Nat := 734271858802493982623603

theorem tailTrace_2144984 : CollatzResearch.WordTrace tailWord_2144984 prefixEnd_2144984 734271858802493982623603 := by
  unfold tailWord_2144984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116996830548388473481003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52155995774064517964641337 39116996830548388473481003)
  ·
    refine ⟨58675495245822582710221505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39116996830548388473481003 58675495245822582710221505)
    ·
      refine ⟨44006621434366937032666129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58675495245822582710221505 44006621434366937032666129)
      ·
        refine ⟨33004966075775202774499597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44006621434366937032666129 33004966075775202774499597)
        ·
          refine ⟨12376862278415701040437349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33004966075775202774499597 12376862278415701040437349)
          ·
            refine ⟨2320661677202943945082003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12376862278415701040437349 2320661677202943945082003)
            ·
              refine ⟨3480992515804415917623005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320661677202943945082003 3480992515804415917623005)
              ·
                refine ⟨1305372193426655969108627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3480992515804415917623005 1305372193426655969108627)
                ·
                  refine ⟨1958058290139983953662941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305372193426655969108627 1958058290139983953662941)
                  ·
                    refine ⟨734271858802493982623603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958058290139983953662941 734271858802493982623603)
                    ·
                      rfl

theorem cell22_2144984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_2144984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2144984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2144984 prefixEnd_2144984 := by exact prefixLift 2144984
  have htrace : WordTrace (prefixWord ++ tailWord_2144984) baseStart_2144984 baseEnd_2144984 := by
    simpa [prefixWord, tailWord_2144984, baseEnd_2144984] using wordTrace_append hprefix tailTrace_2144984
  have hstable : (prefixWord ++ tailWord_2144984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144984).length < 2 ^ (prefixWord ++ tailWord_2144984).sum := by decide
  have hdescent : baseEnd_2144984 < baseStart_2144984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145023 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_2145023 : Nat := 118140960795 + 2145023 * 2 ^ 59
def prefixEnd_2145023 : Nat := 4983230072969 + 3 ^ 40 * 2145023 * 2
def baseEnd_2145023 : Nat := 734285209299510880898483

theorem tailTrace_2145023 : CollatzResearch.WordTrace tailWord_2145023 prefixEnd_2145023 734285209299510880898483 := by
  unfold tailWord_2145023
  simp only [CollatzResearch.WordTrace]
  refine ⟨78235416107955486607631723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52156944071970324405087815 78235416107955486607631723)
  ·
    refine ⟨117353124161933229911447585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78235416107955486607631723 117353124161933229911447585)
    ·
      refine ⟨88014843121449922433585689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117353124161933229911447585 88014843121449922433585689)
      ·
        refine ⟨66011132341087441825189267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88014843121449922433585689 66011132341087441825189267)
        ·
          refine ⟨99016698511631162737783901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66011132341087441825189267 99016698511631162737783901)
          ·
            refine ⟨37131261941861686026668963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99016698511631162737783901 37131261941861686026668963)
            ·
              refine ⟨55696892912792529040003445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37131261941861686026668963 55696892912792529040003445)
              ·
                refine ⟨5221583710574299597500323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55696892912792529040003445 5221583710574299597500323)
                ·
                  refine ⟨7832375565861449396250485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5221583710574299597500323 7832375565861449396250485)
                  ·
                    refine ⟨734285209299510880898483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7832375565861449396250485 734285209299510880898483)
                    ·
                      rfl

theorem cell22_2145023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_2145023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145023 prefixEnd_2145023 := by exact prefixLift 2145023
  have htrace : WordTrace (prefixWord ++ tailWord_2145023) baseStart_2145023 baseEnd_2145023 := by
    simpa [prefixWord, tailWord_2145023, baseEnd_2145023] using wordTrace_append hprefix tailTrace_2145023
  have hstable : (prefixWord ++ tailWord_2145023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145023).length < 2 ^ (prefixWord ++ tailWord_2145023).sum := by decide
  have hdescent : baseEnd_2145023 < baseStart_2145023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145055 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_2145055 : Nat := 118140960795 + 2145055 * 2 ^ 59
def prefixEnd_2145055 : Nat := 4983230072969 + 3 ^ 40 * 2145055 * 2
def baseEnd_2145055 : Nat := 734296163553473464098385

theorem tailTrace_2145055 : CollatzResearch.WordTrace tailWord_2145055 prefixEnd_2145055 734296163553473464098385 := by
  unfold tailWord_2145055
  simp only [CollatzResearch.WordTrace]
  refine ⟨78236583243839556072796619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52157722162559704048531079 78236583243839556072796619)
  ·
    refine ⟨117354874865759334109194929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78236583243839556072796619 117354874865759334109194929)
    ·
      refine ⟨88016156149319500581896197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117354874865759334109194929 88016156149319500581896197)
      ·
        refine ⟨16503029277997406359105537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88016156149319500581896197 16503029277997406359105537)
        ·
          refine ⟨12377271958498054769329153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16503029277997406359105537 12377271958498054769329153)
          ·
            refine ⟨9282953968873541076996865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12377271958498054769329153 9282953968873541076996865)
            ·
              refine ⟨6962215476655155807747649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9282953968873541076996865 6962215476655155807747649)
              ·
                refine ⟨5221661607491366855810737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6962215476655155807747649 5221661607491366855810737)
                ·
                  refine ⟨3916246205618525141858053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5221661607491366855810737 3916246205618525141858053)
                  ·
                    refine ⟨734296163553473464098385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3916246205618525141858053 734296163553473464098385)
                    ·
                      rfl

theorem cell22_2145055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_2145055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145055 prefixEnd_2145055 := by exact prefixLift 2145055
  have htrace : WordTrace (prefixWord ++ tailWord_2145055) baseStart_2145055 baseEnd_2145055 := by
    simpa [prefixWord, tailWord_2145055, baseEnd_2145055] using wordTrace_append hprefix tailTrace_2145055
  have hstable : (prefixWord ++ tailWord_2145055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145055).length < 2 ^ (prefixWord ++ tailWord_2145055).sum := by decide
  have hdescent : baseEnd_2145055 < baseStart_2145055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145057 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2145057 : Nat := 118140960795 + 2145057 * 2 ^ 59
def prefixEnd_2145057 : Nat := 4983230072969 + 3 ^ 40 * 2145057 * 2
def baseEnd_2145057 : Nat := 734296848194346125548379

theorem tailTrace_2145057 : CollatzResearch.WordTrace tailWord_2145057 prefixEnd_2145057 734296848194346125548379 := by
  unfold tailWord_2145057
  simp only [CollatzResearch.WordTrace]
  refine ⟨78236656189832310414369425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52157770793221540276246283 78236656189832310414369425)
  ·
    refine ⟨58677492142374232810777069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78236656189832310414369425 58677492142374232810777069)
    ·
      refine ⟨22004059553390337304041401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58677492142374232810777069 22004059553390337304041401)
      ·
        refine ⟨16503044665042752978031051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22004059553390337304041401 16503044665042752978031051)
        ·
          refine ⟨24754566997564129467046577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16503044665042752978031051 24754566997564129467046577)
          ·
            refine ⟨18565925248173097100284933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24754566997564129467046577 18565925248173097100284933)
            ·
              refine ⟨3481110984032455706303425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18565925248173097100284933 3481110984032455706303425)
              ·
                refine ⟨2610833238024341779727569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481110984032455706303425 2610833238024341779727569)
                ·
                  refine ⟨1958124928518256334795677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610833238024341779727569 1958124928518256334795677)
                  ·
                    refine ⟨734296848194346125548379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958124928518256334795677 734296848194346125548379)
                    ·
                      rfl

theorem cell22_2145057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2145057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145057 prefixEnd_2145057 := by exact prefixLift 2145057
  have htrace : WordTrace (prefixWord ++ tailWord_2145057) baseStart_2145057 baseEnd_2145057 := by
    simpa [prefixWord, tailWord_2145057, baseEnd_2145057] using wordTrace_append hprefix tailTrace_2145057
  have hstable : (prefixWord ++ tailWord_2145057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145057).length < 2 ^ (prefixWord ++ tailWord_2145057).sum := by decide
  have hdescent : baseEnd_2145057 < baseStart_2145057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145132 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_2145132 : Nat := 118140960795 + 2145132 * 2 ^ 59
def prefixEnd_2145132 : Nat := 4983230072969 + 3 ^ 40 * 2145132 * 2
def baseEnd_2145132 : Nat := 244774174075690309974383

theorem tailTrace_2145132 : CollatzResearch.WordTrace tailWord_2145132 prefixEnd_2145132 244774174075690309974383 := by
  unfold tailWord_2145132
  simp only [CollatzResearch.WordTrace]
  refine ⟨39119695832280299111674825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52159594443040398815566433 39119695832280299111674825)
  ·
    refine ⟨29339771874210224333756119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39119695832280299111674825 29339771874210224333756119)
    ·
      refine ⟨44009657811315336500634179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29339771874210224333756119 44009657811315336500634179)
      ·
        refine ⟨66014486716973004750951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44009657811315336500634179 66014486716973004750951269)
        ·
          refine ⟨12377716259432438390803363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66014486716973004750951269 12377716259432438390803363)
          ·
            refine ⟨18566574389148657586205045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12377716259432438390803363 18566574389148657586205045)
            ·
              refine ⟨1740616348982686648706723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18566574389148657586205045 1740616348982686648706723)
              ·
                refine ⟨2610924523474029973060085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740616348982686648706723 2610924523474029973060085)
                ·
                  refine ⟨244774174075690309974383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610924523474029973060085 244774174075690309974383)
                  ·
                    rfl

theorem cell22_2145132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_2145132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145132 prefixEnd_2145132 := by exact prefixLift 2145132
  have htrace : WordTrace (prefixWord ++ tailWord_2145132) baseStart_2145132 baseEnd_2145132 := by
    simpa [prefixWord, tailWord_2145132, baseEnd_2145132] using wordTrace_append hprefix tailTrace_2145132
  have hstable : (prefixWord ++ tailWord_2145132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145132).length < 2 ^ (prefixWord ++ tailWord_2145132).sum := by decide
  have hdescent : baseEnd_2145132 < baseStart_2145132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145205 : List Nat := [1, 3, 3, 2, 1, 1, 1, 10]
def baseStart_2145205 : Nat := 118140960795 + 2145205 * 2 ^ 59
def prefixEnd_2145205 : Nat := 4983230072969 + 3 ^ 40 * 2145205 * 2
def baseEnd_2145205 : Nat := 81594167957658119205325

theorem tailTrace_2145205 : CollatzResearch.WordTrace tailWord_2145205 prefixEnd_2145205 81594167957658119205325 := by
  unfold tailWord_2145205
  simp only [CollatzResearch.WordTrace]
  refine ⟨78242054193296131690757069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52161369462197421127171379 78242054193296131690757069)
  ·
    refine ⟨29340770322486049384033901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78242054193296131690757069 29340770322486049384033901)
    ·
      refine ⟨11002788870932268519012713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29340770322486049384033901 11002788870932268519012713)
      ·
        refine ⟨8252091653199201389259535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11002788870932268519012713 8252091653199201389259535)
        ·
          refine ⟨12378137479798802083889303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8252091653199201389259535 12378137479798802083889303)
          ·
            refine ⟨18567206219698203125833955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12378137479798802083889303 18567206219698203125833955)
            ·
              refine ⟨27850809329547304688750933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18567206219698203125833955 27850809329547304688750933)
              ·
                refine ⟨81594167957658119205325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27850809329547304688750933 81594167957658119205325)
                ·
                  rfl

theorem cell22_2145205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 10].length) (baseStart_2145205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145205 prefixEnd_2145205 := by exact prefixLift 2145205
  have htrace : WordTrace (prefixWord ++ tailWord_2145205) baseStart_2145205 baseEnd_2145205 := by
    simpa [prefixWord, tailWord_2145205, baseEnd_2145205] using wordTrace_append hprefix tailTrace_2145205
  have hstable : (prefixWord ++ tailWord_2145205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145205).length < 2 ^ (prefixWord ++ tailWord_2145205).sum := by decide
  have hdescent : baseEnd_2145205 < baseStart_2145205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145314 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2145314 : Nat := 118140960795 + 2145314 * 2 ^ 59
def prefixEnd_2145314 : Nat := 4983230072969 + 3 ^ 40 * 2145314 * 2
def baseEnd_2145314 : Nat := 734384824546483121872591

theorem tailTrace_2145314 : CollatzResearch.WordTrace tailWord_2145314 prefixEnd_2145314 734384824546483121872591 := by
  unfold tailWord_2145314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561507437475310826618749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52164019833267495537649997 19561507437475310826618749)
  ·
    refine ⟨7335565289053241559982031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19561507437475310826618749 7335565289053241559982031)
    ·
      refine ⟨11003347933579862339973047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335565289053241559982031 11003347933579862339973047)
      ·
        refine ⟨16505021900369793509959571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11003347933579862339973047 16505021900369793509959571)
        ·
          refine ⟨24757532850554690264939357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16505021900369793509959571 24757532850554690264939357)
          ·
            refine ⟨9284074818958008849352259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24757532850554690264939357 9284074818958008849352259)
            ·
              refine ⟨13926112228437013274028389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9284074818958008849352259 13926112228437013274028389)
              ·
                refine ⟨2611146042831939988880323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13926112228437013274028389 2611146042831939988880323)
                ·
                  refine ⟨3916719064247909983320485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611146042831939988880323 3916719064247909983320485)
                  ·
                    refine ⟨734384824546483121872591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3916719064247909983320485 734384824546483121872591)
                    ·
                      rfl

theorem cell22_2145314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2145314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145314 prefixEnd_2145314 := by exact prefixLift 2145314
  have htrace : WordTrace (prefixWord ++ tailWord_2145314) baseStart_2145314 baseEnd_2145314 := by
    simpa [prefixWord, tailWord_2145314, baseEnd_2145314] using wordTrace_append hprefix tailTrace_2145314
  have hstable : (prefixWord ++ tailWord_2145314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145314).length < 2 ^ (prefixWord ++ tailWord_2145314).sum := by decide
  have hdescent : baseEnd_2145314 < baseStart_2145314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145344 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_2145344 : Nat := 118140960795 + 2145344 * 2 ^ 59
def prefixEnd_2145344 : Nat := 4983230072969 + 3 ^ 40 * 2145344 * 2
def baseEnd_2145344 : Nat := 734395094159573043622499

theorem tailTrace_2145344 : CollatzResearch.WordTrace tailWord_2145344 prefixEnd_2145344 734395094159573043622499 := by
  unfold tailWord_2145344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39123561969896279215033543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52164749293195038953378057 39123561969896279215033543)
  ·
    refine ⟨58685342954844418822550315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39123561969896279215033543 58685342954844418822550315)
    ·
      refine ⟨88028014432266628233825473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58685342954844418822550315 88028014432266628233825473)
      ·
        refine ⟨66021010824199971175369105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88028014432266628233825473 66021010824199971175369105)
        ·
          refine ⟨49515758118149978381526829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66021010824199971175369105 49515758118149978381526829)
          ·
            refine ⟨18568409294306241893072561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49515758118149978381526829 18568409294306241893072561)
            ·
              refine ⟨13926306970729681419804421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18568409294306241893072561 13926306970729681419804421)
              ·
                refine ⟨2611182557011815266213329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13926306970729681419804421 2611182557011815266213329)
                ·
                  refine ⟨1958386917758861449659997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611182557011815266213329 1958386917758861449659997)
                  ·
                    refine ⟨734395094159573043622499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958386917758861449659997 734395094159573043622499)
                    ·
                      rfl

theorem cell22_2145344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_2145344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145344 prefixEnd_2145344 := by exact prefixLift 2145344
  have htrace : WordTrace (prefixWord ++ tailWord_2145344) baseStart_2145344 baseEnd_2145344 := by
    simpa [prefixWord, tailWord_2145344, baseEnd_2145344] using wordTrace_append hprefix tailTrace_2145344
  have hstable : (prefixWord ++ tailWord_2145344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145344).length < 2 ^ (prefixWord ++ tailWord_2145344).sum := by decide
  have hdescent : baseEnd_2145344 < baseStart_2145344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145361 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_2145361 : Nat := 118140960795 + 2145361 * 2 ^ 59
def prefixEnd_2145361 : Nat := 4983230072969 + 3 ^ 40 * 2145361 * 2
def baseEnd_2145361 : Nat := 734400913606990665947447

theorem tailTrace_2145361 : CollatzResearch.WordTrace tailWord_2145361 prefixEnd_2145361 734400913606990665947447 := by
  unfold tailWord_2145361
  simp only [CollatzResearch.WordTrace]
  refine ⟨78247743980730970333435937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52165162653820646888957291 78247743980730970333435937)
  ·
    refine ⟨58685807985548227750076953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78247743980730970333435937 58685807985548227750076953)
    ·
      refine ⟨44014355989161170812557715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58685807985548227750076953 44014355989161170812557715)
      ·
        refine ⟨66021533983741756218836573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44014355989161170812557715 66021533983741756218836573)
        ·
          refine ⟨24758075243903158582063715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66021533983741756218836573 24758075243903158582063715)
          ·
            refine ⟨37137112865854737873095573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24758075243903158582063715 37137112865854737873095573)
            ·
              refine ⟨1740802165586940837801355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37137112865854737873095573 1740802165586940837801355)
              ·
                refine ⟨2611203248380411256702033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740802165586940837801355 2611203248380411256702033)
                ·
                  refine ⟨1958402436285308442526525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611203248380411256702033 1958402436285308442526525)
                  ·
                    refine ⟨734400913606990665947447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958402436285308442526525 734400913606990665947447)
                    ·
                      rfl

theorem cell22_2145361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_2145361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145361 prefixEnd_2145361 := by exact prefixLift 2145361
  have htrace : WordTrace (prefixWord ++ tailWord_2145361) baseStart_2145361 baseEnd_2145361 := by
    simpa [prefixWord, tailWord_2145361, baseEnd_2145361] using wordTrace_append hprefix tailTrace_2145361
  have hstable : (prefixWord ++ tailWord_2145361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145361).length < 2 ^ (prefixWord ++ tailWord_2145361).sum := by decide
  have hdescent : baseEnd_2145361 < baseStart_2145361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145397 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 4]
def baseStart_2145397 : Nat := 118140960795 + 2145397 * 2 ^ 59
def prefixEnd_2145397 : Nat := 4983230072969 + 3 ^ 40 * 2145397 * 2
def baseEnd_2145397 : Nat := 244804412380899524015779

theorem tailTrace_2145397 : CollatzResearch.WordTrace tailWord_2145397 prefixEnd_2145397 244804412380899524015779 := by
  unfold tailWord_2145397
  simp only [CollatzResearch.WordTrace]
  refine ⟨78249057008600548481746445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52166038005733698987830963 78249057008600548481746445)
  ·
    refine ⟨29343396378225205680654917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78249057008600548481746445 29343396378225205680654917)
    ·
      refine ⟨5501886820917226065122797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29343396378225205680654917 5501886820917226065122797)
      ·
        refine ⟨2063207557843959774421049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5501886820917226065122797 2063207557843959774421049)
        ·
          refine ⟨1547405668382969830815787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063207557843959774421049 1547405668382969830815787)
          ·
            refine ⟨2321108502574454746223681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547405668382969830815787 2321108502574454746223681)
            ·
              refine ⟨1740831376930841059667761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2321108502574454746223681 1740831376930841059667761)
              ·
                refine ⟨1305623532698130794750821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740831376930841059667761 1305623532698130794750821)
                ·
                  refine ⟨244804412380899524015779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305623532698130794750821 244804412380899524015779)
                  ·
                    rfl

theorem cell22_2145397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_2145397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145397 prefixEnd_2145397 := by exact prefixLift 2145397
  have htrace : WordTrace (prefixWord ++ tailWord_2145397) baseStart_2145397 baseEnd_2145397 := by
    simpa [prefixWord, tailWord_2145397, baseEnd_2145397] using wordTrace_append hprefix tailTrace_2145397
  have hstable : (prefixWord ++ tailWord_2145397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145397).length < 2 ^ (prefixWord ++ tailWord_2145397).sum := by decide
  have hdescent : baseEnd_2145397 < baseStart_2145397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145417 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_2145417 : Nat := 118140960795 + 2145417 * 2 ^ 59
def prefixEnd_2145417 : Nat := 4983230072969 + 3 ^ 40 * 2145417 * 2
def baseEnd_2145417 : Nat := 734420083551425186547275

theorem tailTrace_2145417 : CollatzResearch.WordTrace tailWord_2145417 prefixEnd_2145417 734420083551425186547275 := by
  unfold tailWord_2145417
  simp only [CollatzResearch.WordTrace]
  refine ⟨78249786468528091897474505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52166524312352061264983003 78249786468528091897474505)
  ·
    refine ⟨58687339851396068923105879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78249786468528091897474505 58687339851396068923105879)
    ·
      refine ⟨88031009777094103384658819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58687339851396068923105879 88031009777094103384658819)
      ·
        refine ⟨132046514665641155076988229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88031009777094103384658819 132046514665641155076988229)
        ·
          refine ⟨24758721499807716576935293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132046514665641155076988229 24758721499807716576935293)
          ·
            refine ⟨9284520562427893716350735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24758721499807716576935293 9284520562427893716350735)
            ·
              refine ⟨13926780843641840574526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9284520562427893716350735 13926780843641840574526103)
              ·
                refine ⟨20890171265462760861789155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13926780843641840574526103 20890171265462760861789155)
                ·
                  refine ⟨31335256898194141292683733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20890171265462760861789155 31335256898194141292683733)
                  ·
                    refine ⟨734420083551425186547275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31335256898194141292683733 734420083551425186547275)
                    ·
                      rfl

theorem cell22_2145417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_2145417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145417 prefixEnd_2145417 := by exact prefixLift 2145417
  have htrace : WordTrace (prefixWord ++ tailWord_2145417) baseStart_2145417 baseEnd_2145417 := by
    simpa [prefixWord, tailWord_2145417, baseEnd_2145417] using wordTrace_append hprefix tailTrace_2145417
  have hstable : (prefixWord ++ tailWord_2145417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145417).length < 2 ^ (prefixWord ++ tailWord_2145417).sum := by decide
  have hdescent : baseEnd_2145417 < baseStart_2145417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145453 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2145453 : Nat := 118140960795 + 2145453 * 2 ^ 59
def prefixEnd_2145453 : Nat := 4983230072969 + 3 ^ 40 * 2145453 * 2
def baseEnd_2145453 : Nat := 244810802362377697549055

theorem tailTrace_2145453 : CollatzResearch.WordTrace tailWord_2145453 prefixEnd_2145453 244810802362377697549055 := by
  unfold tailWord_2145453
  simp only [CollatzResearch.WordTrace]
  refine ⟨78251099496397670045785013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52167399664265113363856675 78251099496397670045785013)
  ·
    refine ⟨7336040577787281566792345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78251099496397670045785013 7336040577787281566792345)
    ·
      refine ⟨5502030433340461175094259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7336040577787281566792345 5502030433340461175094259)
      ·
        refine ⟨8253045650010691762641389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502030433340461175094259 8253045650010691762641389)
        ·
          refine ⟨3094892118754009410990521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8253045650010691762641389 3094892118754009410990521)
          ·
            refine ⟨2321169089065507058242891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094892118754009410990521 2321169089065507058242891)
            ·
              refine ⟨3481753633598260587364337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321169089065507058242891 3481753633598260587364337)
              ·
                refine ⟨2611315225198695440523253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481753633598260587364337 2611315225198695440523253)
                ·
                  refine ⟨244810802362377697549055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2611315225198695440523253 244810802362377697549055)
                  ·
                    rfl

theorem cell22_2145453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2145453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145453 prefixEnd_2145453 := by exact prefixLift 2145453
  have htrace : WordTrace (prefixWord ++ tailWord_2145453) baseStart_2145453 baseEnd_2145453 := by
    simpa [prefixWord, tailWord_2145453, baseEnd_2145453] using wordTrace_append hprefix tailTrace_2145453
  have hstable : (prefixWord ++ tailWord_2145453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145453).length < 2 ^ (prefixWord ++ tailWord_2145453).sum := by decide
  have hdescent : baseEnd_2145453 < baseStart_2145453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2145569 : Nat := 118140960795 + 2145569 * 2 ^ 59
def prefixEnd_2145569 : Nat := 4983230072969 + 3 ^ 40 * 2145569 * 2
def baseEnd_2145569 : Nat := 734472116257747456746809

theorem tailTrace_2145569 : CollatzResearch.WordTrace tailWord_2145569 prefixEnd_2145569 734472116257747456746809 := by
  unfold tailWord_2145569
  simp only [CollatzResearch.WordTrace]
  refine ⟨78255330363977421857007761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52170220242651614571338507 78255330363977421857007761)
  ·
    refine ⟨58691497772983066392755821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78255330363977421857007761 58691497772983066392755821)
    ·
      refine ⟨22009311664868649897283433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58691497772983066392755821 22009311664868649897283433)
      ·
        refine ⟨16506983748651487422962575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22009311664868649897283433 16506983748651487422962575)
        ·
          refine ⟨24760475622977231134443863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16506983748651487422962575 24760475622977231134443863)
          ·
            refine ⟨37140713434465846701665795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24760475622977231134443863 37140713434465846701665795)
            ·
              refine ⟨55711070151698770052498693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37140713434465846701665795 55711070151698770052498693)
              ·
                refine ⟨10445825653443519384843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55711070151698770052498693 10445825653443519384843505)
                ·
                  refine ⟨7834369240082639538632629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10445825653443519384843505 7834369240082639538632629)
                  ·
                    refine ⟨734472116257747456746809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7834369240082639538632629 734472116257747456746809)
                    ·
                      rfl

theorem cell22_2145569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2145569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145569 prefixEnd_2145569 := by exact prefixLift 2145569
  have htrace : WordTrace (prefixWord ++ tailWord_2145569) baseStart_2145569 baseEnd_2145569 := by
    simpa [prefixWord, tailWord_2145569, baseEnd_2145569] using wordTrace_append hprefix tailTrace_2145569
  have hstable : (prefixWord ++ tailWord_2145569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145569).length < 2 ^ (prefixWord ++ tailWord_2145569).sum := by decide
  have hdescent : baseEnd_2145569 < baseStart_2145569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145571 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 5]
def baseStart_2145571 : Nat := 118140960795 + 2145571 * 2 ^ 59
def prefixEnd_2145571 : Nat := 4983230072969 + 3 ^ 40 * 2145571 * 2
def baseEnd_2145571 : Nat := 244824266966206706065601

theorem tailTrace_2145571 : CollatzResearch.WordTrace tailWord_2145571 prefixEnd_2145571 244824266966206706065601 := by
  unfold tailWord_2145571
  simp only [CollatzResearch.WordTrace]
  refine ⟨78255403309970176198580567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52170268873313450799053711 78255403309970176198580567)
  ·
    refine ⟨117383104964955264297870851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78255403309970176198580567 117383104964955264297870851)
    ·
      refine ⟨176074657447432896446806277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117383104964955264297870851 176074657447432896446806277)
      ·
        refine ⟨33013998271393668083776177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176074657447432896446806277 33013998271393668083776177)
        ·
          refine ⟨24760498703545251062832133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33013998271393668083776177 24760498703545251062832133)
          ·
            refine ⟨4642593506914734574281025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24760498703545251062832133 4642593506914734574281025)
            ·
              refine ⟨3481945130186050930710769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642593506914734574281025 3481945130186050930710769)
              ·
                refine ⟨2611458847639538198033077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481945130186050930710769 2611458847639538198033077)
                ·
                  refine ⟨244824266966206706065601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2611458847639538198033077 244824266966206706065601)
                  ·
                    rfl

theorem cell22_2145571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].length) (baseStart_2145571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145571 prefixEnd_2145571 := by exact prefixLift 2145571
  have htrace : WordTrace (prefixWord ++ tailWord_2145571) baseStart_2145571 baseEnd_2145571 := by
    simpa [prefixWord, tailWord_2145571, baseEnd_2145571] using wordTrace_append hprefix tailTrace_2145571
  have hstable : (prefixWord ++ tailWord_2145571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145571).length < 2 ^ (prefixWord ++ tailWord_2145571).sum := by decide
  have hdescent : baseEnd_2145571 < baseStart_2145571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145584 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_2145584 : Nat := 118140960795 + 2145584 * 2 ^ 59
def prefixEnd_2145584 : Nat := 4983230072969 + 3 ^ 40 * 2145584 * 2
def baseEnd_2145584 : Nat := 734477251064292417621763

theorem tailTrace_2145584 : CollatzResearch.WordTrace tailWord_2145584 prefixEnd_2145584 734477251064292417621763 := by
  unfold tailWord_2145584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39127938729461539709401903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52170584972615386279202537 39127938729461539709401903)
  ·
    refine ⟨58691908094192309564102855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39127938729461539709401903 58691908094192309564102855)
    ·
      refine ⟨88037862141288464346154283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58691908094192309564102855 88037862141288464346154283)
      ·
        refine ⟨132056793211932696519231425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88037862141288464346154283 132056793211932696519231425)
        ·
          refine ⟨99042594908949522389423569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132056793211932696519231425 99042594908949522389423569)
          ·
            refine ⟨74281946181712141792067677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99042594908949522389423569 74281946181712141792067677)
            ·
              refine ⟨27855729818142053172025379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74281946181712141792067677 27855729818142053172025379)
              ·
                refine ⟨41783594727213079758038069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27855729818142053172025379 41783594727213079758038069)
                ·
                  refine ⟨3917212005676226227316069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41783594727213079758038069 3917212005676226227316069)
                  ·
                    refine ⟨734477251064292417621763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3917212005676226227316069 734477251064292417621763)
                    ·
                      rfl

theorem cell22_2145584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_2145584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145584 prefixEnd_2145584 := by exact prefixLift 2145584
  have htrace : WordTrace (prefixWord ++ tailWord_2145584) baseStart_2145584 baseEnd_2145584 := by
    simpa [prefixWord, tailWord_2145584, baseEnd_2145584] using wordTrace_append hprefix tailTrace_2145584
  have hstable : (prefixWord ++ tailWord_2145584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145584).length < 2 ^ (prefixWord ++ tailWord_2145584).sum := by decide
  have hdescent : baseEnd_2145584 < baseStart_2145584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145586 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2145586 : Nat := 118140960795 + 2145586 * 2 ^ 59
def prefixEnd_2145586 : Nat := 4983230072969 + 3 ^ 40 * 2145586 * 2
def baseEnd_2145586 : Nat := 734477935705165079071757

theorem tailTrace_2145586 : CollatzResearch.WordTrace tailWord_2145586 prefixEnd_2145586 734477935705165079071757 := by
  unfold tailWord_2145586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563987601228958440094153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52170633603277222506917741 19563987601228958440094153)
  ·
    refine ⟨14672990700921718830070615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19563987601228958440094153 14672990700921718830070615)
    ·
      refine ⟨22009486051382578245105923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14672990700921718830070615 22009486051382578245105923)
      ·
        refine ⟨33014229077073867367658885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22009486051382578245105923 33014229077073867367658885)
        ·
          refine ⟨6190167951951350131436041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33014229077073867367658885 6190167951951350131436041)
          ·
            refine ⟨4642625963963512598577031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6190167951951350131436041 4642625963963512598577031)
            ·
              refine ⟨6963938945945268897865547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642625963963512598577031 6963938945945268897865547)
              ·
                refine ⟨10445908418917903346798321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6963938945945268897865547 10445908418917903346798321)
                ·
                  refine ⟨7834431314188427510098741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10445908418917903346798321 7834431314188427510098741)
                  ·
                    refine ⟨734477935705165079071757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7834431314188427510098741 734477935705165079071757)
                    ·
                      rfl

theorem cell22_2145586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2145586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145586 prefixEnd_2145586 := by exact prefixLift 2145586
  have htrace : WordTrace (prefixWord ++ tailWord_2145586) baseStart_2145586 baseEnd_2145586 := by
    simpa [prefixWord, tailWord_2145586, baseEnd_2145586] using wordTrace_append hprefix tailTrace_2145586
  have hstable : (prefixWord ++ tailWord_2145586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145586).length < 2 ^ (prefixWord ++ tailWord_2145586).sum := by decide
  have hdescent : baseEnd_2145586 < baseStart_2145586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145599 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 8]
def baseStart_2145599 : Nat := 118140960795 + 2145599 * 2 ^ 59
def prefixEnd_2145599 : Nat := 4983230072969 + 3 ^ 40 * 2145599 * 2
def baseEnd_2145599 : Nat := 244827461956945792832239

theorem tailTrace_2145599 : CollatzResearch.WordTrace tailWord_2145599 prefixEnd_2145599 244827461956945792832239 := by
  unfold tailWord_2145599
  simp only [CollatzResearch.WordTrace]
  refine ⟨78256424553868736980599851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52170949702579157987066567 78256424553868736980599851)
  ·
    refine ⟨117384636830803105470899777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78256424553868736980599851 117384636830803105470899777)
    ·
      refine ⟨88038477623102329103174833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117384636830803105470899777 88038477623102329103174833)
      ·
        refine ⟨66028858217326746827381125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88038477623102329103174833 66028858217326746827381125)
        ·
          refine ⟨12380410915748765030133961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66028858217326746827381125 12380410915748765030133961)
          ·
            refine ⟨9285308186811573772600471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12380410915748765030133961 9285308186811573772600471)
            ·
              refine ⟨13927962280217360658900707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9285308186811573772600471 13927962280217360658900707)
              ·
                refine ⟨20891943420326040988351061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13927962280217360658900707 20891943420326040988351061)
                ·
                  refine ⟨244827461956945792832239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20891943420326040988351061 244827461956945792832239)
                  ·
                    rfl

theorem cell22_2145599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_2145599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145599 prefixEnd_2145599 := by exact prefixLift 2145599
  have htrace : WordTrace (prefixWord ++ tailWord_2145599) baseStart_2145599 baseEnd_2145599 := by
    simpa [prefixWord, tailWord_2145599, baseEnd_2145599] using wordTrace_append hprefix tailTrace_2145599
  have hstable : (prefixWord ++ tailWord_2145599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145599).length < 2 ^ (prefixWord ++ tailWord_2145599).sum := by decide
  have hdescent : baseEnd_2145599 < baseStart_2145599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145622 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2145622 : Nat := 118140960795 + 2145622 * 2 ^ 59
def prefixEnd_2145622 : Nat := 4983230072969 + 3 ^ 40 * 2145622 * 2
def baseEnd_2145622 : Nat := 244830086413624328390549

theorem tailTrace_2145622 : CollatzResearch.WordTrace tailWord_2145622 prefixEnd_2145622 244830086413624328390549 := by
  unfold tailWord_2145622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891078964549088244292945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52171508955190274605791413 4891078964549088244292945)
  ·
    refine ⟨3668309223411816183219709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4891078964549088244292945 3668309223411816183219709)
    ·
      refine ⟨1375615958779431068707391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3668309223411816183219709 1375615958779431068707391)
      ·
        refine ⟨2063423938169146603061087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375615958779431068707391 2063423938169146603061087)
        ·
          refine ⟨3095135907253719904591631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063423938169146603061087 3095135907253719904591631)
          ·
            refine ⟨4642703860880579856887447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095135907253719904591631 4642703860880579856887447)
            ·
              refine ⟨6964055791320869785331171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642703860880579856887447 6964055791320869785331171)
              ·
                refine ⟨10446083686981304677996757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6964055791320869785331171 10446083686981304677996757)
                ·
                  refine ⟨244830086413624328390549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10446083686981304677996757 244830086413624328390549)
                  ·
                    rfl

theorem cell22_2145622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2145622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145622 prefixEnd_2145622 := by exact prefixLift 2145622
  have htrace : WordTrace (prefixWord ++ tailWord_2145622) baseStart_2145622 baseEnd_2145622 := by
    simpa [prefixWord, tailWord_2145622, baseEnd_2145622] using wordTrace_append hprefix tailTrace_2145622
  have hstable : (prefixWord ++ tailWord_2145622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145622).length < 2 ^ (prefixWord ++ tailWord_2145622).sum := by decide
  have hdescent : baseEnd_2145622 < baseStart_2145622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145659 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_2145659 : Nat := 118140960795 + 2145659 * 2 ^ 59
def prefixEnd_2145659 : Nat := 4983230072969 + 3 ^ 40 * 2145659 * 2
def baseEnd_2145659 : Nat := 734502925097017221996533

theorem tailTrace_2145659 : CollatzResearch.WordTrace tailWord_2145659 prefixEnd_2145659 734502925097017221996533 := by
  unfold tailWord_2145659
  simp only [CollatzResearch.WordTrace]
  refine ⟨78258612933651367227784031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52172408622434244818522687 78258612933651367227784031)
  ·
    refine ⟨117387919400477050841676047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78258612933651367227784031 117387919400477050841676047)
    ·
      refine ⟨176081879100715576262514071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117387919400477050841676047 176081879100715576262514071)
      ·
        refine ⟨264122818651073364393771107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176081879100715576262514071 264122818651073364393771107)
        ·
          refine ⟨396184227976610046590656661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264122818651073364393771107 396184227976610046590656661)
          ·
            refine ⟨18571135686403595933937031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 396184227976610046590656661 18571135686403595933937031)
            ·
              refine ⟨27856703529605393900905547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18571135686403595933937031 27856703529605393900905547)
              ·
                refine ⟨41785055294408090851358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27856703529605393900905547 41785055294408090851358321)
                ·
                  refine ⟨31338791470806068138518741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41785055294408090851358321 31338791470806068138518741)
                  ·
                    refine ⟨734502925097017221996533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31338791470806068138518741 734502925097017221996533)
                    ·
                      rfl

theorem cell22_2145659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_2145659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145659 prefixEnd_2145659 := by exact prefixLift 2145659
  have htrace : WordTrace (prefixWord ++ tailWord_2145659) baseStart_2145659 baseEnd_2145659 := by
    simpa [prefixWord, tailWord_2145659, baseEnd_2145659] using wordTrace_append hprefix tailTrace_2145659
  have hstable : (prefixWord ++ tailWord_2145659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145659).length < 2 ^ (prefixWord ++ tailWord_2145659).sum := by decide
  have hdescent : baseEnd_2145659 < baseStart_2145659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145678 : List Nat := [4, 1, 1, 4, 2, 2, 8]
def baseStart_2145678 : Nat := 118140960795 + 2145678 * 2 ^ 59
def prefixEnd_2145678 : Nat := 4983230072969 + 3 ^ 40 * 2145678 * 2
def baseEnd_2145678 : Nat := 27204052932789166880425

theorem tailTrace_2145678 : CollatzResearch.WordTrace tailWord_2145678 prefixEnd_2145678 27204052932789166880425 := by
  unfold tailWord_2145678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9782413240072816684090711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52172870613721688981817125 9782413240072816684090711)
  ·
    refine ⟨14673619860109225026136067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9782413240072816684090711 14673619860109225026136067)
    ·
      refine ⟨22010429790163837539204101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14673619860109225026136067 22010429790163837539204101)
      ·
        refine ⟨4126955585655719538600769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22010429790163837539204101 4126955585655719538600769)
        ·
          refine ⟨3095216689241789653950577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4126955585655719538600769 3095216689241789653950577)
          ·
            refine ⟨2321412516931342240462933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095216689241789653950577 2321412516931342240462933)
            ·
              refine ⟨27204052932789166880425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2321412516931342240462933 27204052932789166880425)
              ·
                rfl

theorem cell22_2145678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 8].length) (baseStart_2145678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145678 prefixEnd_2145678 := by exact prefixLift 2145678
  have htrace : WordTrace (prefixWord ++ tailWord_2145678) baseStart_2145678 baseEnd_2145678 := by
    simpa [prefixWord, tailWord_2145678, baseEnd_2145678] using wordTrace_append hprefix tailTrace_2145678
  have hstable : (prefixWord ++ tailWord_2145678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145678).length < 2 ^ (prefixWord ++ tailWord_2145678).sum := by decide
  have hdescent : baseEnd_2145678 < baseStart_2145678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145800 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2145800 : Nat := 118140960795 + 2145800 * 2 ^ 59
def prefixEnd_2145800 : Nat := 4983230072969 + 3 ^ 40 * 2145800 * 2
def baseEnd_2145800 : Nat := 734551192278539854221101

theorem tailTrace_2145800 : CollatzResearch.WordTrace tailWord_2145800 prefixEnd_2145800 734551192278539854221101 := by
  unfold tailWord_2145800
  simp only [CollatzResearch.WordTrace]
  refine ⟨39131877813070274154333427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52175837084093698872444569 39131877813070274154333427)
  ·
    refine ⟨58697816719605411231500141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39131877813070274154333427 58697816719605411231500141)
    ·
      refine ⟨22011681269852029211812553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58697816719605411231500141 22011681269852029211812553)
      ·
        refine ⟨16508760952389021908859415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22011681269852029211812553 16508760952389021908859415)
        ·
          refine ⟨24763141428583532863289123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16508760952389021908859415 24763141428583532863289123)
          ·
            refine ⟨37144712142875299294933685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24763141428583532863289123 37144712142875299294933685)
            ·
              refine ⟨3482316763394559308900033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37144712142875299294933685 3482316763394559308900033)
              ·
                refine ⟨2611737572545919481675025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482316763394559308900033 2611737572545919481675025)
                ·
                  refine ⟨1958803179409439611256269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611737572545919481675025 1958803179409439611256269)
                  ·
                    refine ⟨734551192278539854221101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1958803179409439611256269 734551192278539854221101)
                    ·
                      rfl

theorem cell22_2145800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2145800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145800 prefixEnd_2145800 := by exact prefixLift 2145800
  have htrace : WordTrace (prefixWord ++ tailWord_2145800) baseStart_2145800 baseEnd_2145800 := by
    simpa [prefixWord, tailWord_2145800, baseEnd_2145800] using wordTrace_append hprefix tailTrace_2145800
  have hstable : (prefixWord ++ tailWord_2145800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145800).length < 2 ^ (prefixWord ++ tailWord_2145800).sum := by decide
  have hdescent : baseEnd_2145800 < baseStart_2145800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145871 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_2145871 : Nat := 118140960795 + 2145871 * 2 ^ 59
def prefixEnd_2145871 : Nat := 4983230072969 + 3 ^ 40 * 2145871 * 2
def baseEnd_2145871 : Nat := 734575497029519335695883

theorem tailTrace_2145871 : CollatzResearch.WordTrace tailWord_2145871 prefixEnd_2145871 734575497029519335695883 := by
  unfold tailWord_2145871
  simp only [CollatzResearch.WordTrace]
  refine ⟨78266345208883327434501467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52177563472588884956334311 78266345208883327434501467)
  ·
    refine ⟨117399517813324991151752201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78266345208883327434501467 117399517813324991151752201)
    ·
      refine ⟨88049638359993743363814151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117399517813324991151752201 88049638359993743363814151)
      ·
        refine ⟨132074457539990615045721227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88049638359993743363814151 132074457539990615045721227)
        ·
          refine ⟨198111686309985922568581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132074457539990615045721227 198111686309985922568581841)
          ·
            refine ⟨148583764732489441926436381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198111686309985922568581841 148583764732489441926436381)
            ·
              refine ⟨55718911774683540722413643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148583764732489441926436381 55718911774683540722413643)
              ·
                refine ⟨83578367662025311083620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55718911774683540722413643 83578367662025311083620465)
                ·
                  refine ⟨62683775746518983312715349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83578367662025311083620465 62683775746518983312715349)
                  ·
                    refine ⟨734575497029519335695883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62683775746518983312715349 734575497029519335695883)
                    ·
                      rfl

theorem cell22_2145871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_2145871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145871 prefixEnd_2145871 := by exact prefixLift 2145871
  have htrace : WordTrace (prefixWord ++ tailWord_2145871) baseStart_2145871 baseEnd_2145871 := by
    simpa [prefixWord, tailWord_2145871, baseEnd_2145871] using wordTrace_append hprefix tailTrace_2145871
  have hstable : (prefixWord ++ tailWord_2145871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145871).length < 2 ^ (prefixWord ++ tailWord_2145871).sum := by decide
  have hdescent : baseEnd_2145871 < baseStart_2145871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145920 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_2145920 : Nat := 118140960795 + 2145920 * 2 ^ 59
def prefixEnd_2145920 : Nat := 4983230072969 + 3 ^ 40 * 2145920 * 2
def baseEnd_2145920 : Nat := 244864090243633180406911

theorem tailTrace_2145920 : CollatzResearch.WordTrace tailWord_2145920 prefixEnd_2145920 244864090243633180406911 := by
  unfold tailWord_2145920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39134066192852904401517607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52178754923803872535356809 39134066192852904401517607)
  ·
    refine ⟨58701099289279356602276411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39134066192852904401517607 58701099289279356602276411)
    ·
      refine ⟨88051648933919034903414617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58701099289279356602276411 88051648933919034903414617)
      ·
        refine ⟨66038736700439276177560963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88051648933919034903414617 66038736700439276177560963)
        ·
          refine ⟨99058105050658914266341445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66038736700439276177560963 99058105050658914266341445)
          ·
            refine ⟨18573394696998546424939021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99058105050658914266341445 18573394696998546424939021)
            ·
              refine ⟨6965023011374454909352133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18573394696998546424939021 6965023011374454909352133)
              ·
                refine ⟨1305941814632710295503525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6965023011374454909352133 1305941814632710295503525)
                ·
                  refine ⟨244864090243633180406911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305941814632710295503525 244864090243633180406911)
                  ·
                    rfl

theorem cell22_2145920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_2145920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2145920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2145920 prefixEnd_2145920 := by exact prefixLift 2145920
  have htrace : WordTrace (prefixWord ++ tailWord_2145920) baseStart_2145920 baseEnd_2145920 := by
    simpa [prefixWord, tailWord_2145920, baseEnd_2145920] using wordTrace_append hprefix tailTrace_2145920
  have hstable : (prefixWord ++ tailWord_2145920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145920).length < 2 ^ (prefixWord ++ tailWord_2145920).sum := by decide
  have hdescent : baseEnd_2145920 < baseStart_2145920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146074 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_2146074 : Nat := 118140960795 + 2146074 * 2 ^ 59
def prefixEnd_2146074 : Nat := 4983230072969 + 3 ^ 40 * 2146074 * 2
def baseEnd_2146074 : Nat := 734644988078094472870261

theorem tailTrace_2146074 : CollatzResearch.WordTrace tailWord_2146074 prefixEnd_2146074 734644988078094472870261 := by
  unfold tailWord_2146074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19568437306786973276035319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52182499484765262069427517 19568437306786973276035319)
  ·
    refine ⟨29352655960180459914052979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19568437306786973276035319 29352655960180459914052979)
    ·
      refine ⟨44028983940270689871079469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29352655960180459914052979 44028983940270689871079469)
      ·
        refine ⟨16510868977601508701654801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44028983940270689871079469 16510868977601508701654801)
        ·
          refine ⟨12383151733201131526241101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16510868977601508701654801 12383151733201131526241101)
          ·
            refine ⟨4643681899950424322340413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12383151733201131526241101 4643681899950424322340413)
            ·
              refine ⟨1741380712481409120877655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4643681899950424322340413 1741380712481409120877655)
              ·
                refine ⟨2612071068722113681316483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741380712481409120877655 2612071068722113681316483)
                ·
                  refine ⟨3918106603083170521974725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612071068722113681316483 3918106603083170521974725)
                  ·
                    refine ⟨734644988078094472870261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3918106603083170521974725 734644988078094472870261)
                    ·
                      rfl

theorem cell22_2146074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_2146074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146074 prefixEnd_2146074 := by exact prefixLift 2146074
  have htrace : WordTrace (prefixWord ++ tailWord_2146074) baseStart_2146074 baseEnd_2146074 := by
    simpa [prefixWord, tailWord_2146074, baseEnd_2146074] using wordTrace_append hprefix tailTrace_2146074
  have hstable : (prefixWord ++ tailWord_2146074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146074).length < 2 ^ (prefixWord ++ tailWord_2146074).sum := by decide
  have hdescent : baseEnd_2146074 < baseStart_2146074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146145 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 7]
def baseStart_2146145 : Nat := 118140960795 + 2146145 * 2 ^ 59
def prefixEnd_2146145 : Nat := 4983230072969 + 3 ^ 40 * 2146145 * 2
def baseEnd_2146145 : Nat := 244889764276357984781681

theorem tailTrace_2146145 : CollatzResearch.WordTrace tailWord_2146145 prefixEnd_2146145 244889764276357984781681 := by
  unfold tailWord_2146145
  simp only [CollatzResearch.WordTrace]
  refine ⟨78276338809890672229975889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52184225873260448153317259 78276338809890672229975889)
  ·
    refine ⟨58707254107418004172481917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78276338809890672229975889 58707254107418004172481917)
    ·
      refine ⟨22015220290281751564680719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58707254107418004172481917 22015220290281751564680719)
      ·
        refine ⟨33022830435422627347021079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22015220290281751564680719 33022830435422627347021079)
        ·
          refine ⟨49534245653133941020531619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33022830435422627347021079 49534245653133941020531619)
          ·
            refine ⟨74301368479700911530797429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49534245653133941020531619 74301368479700911530797429)
            ·
              refine ⟨6965753294971960456012259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74301368479700911530797429 6965753294971960456012259)
              ·
                refine ⟨10448629942457940684018389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6965753294971960456012259 10448629942457940684018389)
                ·
                  refine ⟨244889764276357984781681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10448629942457940684018389 244889764276357984781681)
                  ·
                    rfl

theorem cell22_2146145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_2146145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146145 prefixEnd_2146145 := by exact prefixLift 2146145
  have htrace : WordTrace (prefixWord ++ tailWord_2146145) baseStart_2146145 baseEnd_2146145 := by
    simpa [prefixWord, tailWord_2146145, baseEnd_2146145] using wordTrace_append hprefix tailTrace_2146145
  have hstable : (prefixWord ++ tailWord_2146145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146145).length < 2 ^ (prefixWord ++ tailWord_2146145).sum := by decide
  have hdescent : baseEnd_2146145 < baseStart_2146145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146183 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2146183 : Nat := 118140960795 + 2146183 * 2 ^ 59
def prefixEnd_2146183 : Nat := 4983230072969 + 3 ^ 40 * 2146183 * 2
def baseEnd_2146183 : Nat := 734682301005654521894927

theorem tailTrace_2146183 : CollatzResearch.WordTrace tailWord_2146183 prefixEnd_2146183 734682301005654521894927 := by
  unfold tailWord_2146183
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277724783753004719859203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52185149855835336479906135 78277724783753004719859203)
  ·
    refine ⟨117416587175629507079788805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78277724783753004719859203 117416587175629507079788805)
    ·
      refine ⟨22015610095430532577460401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117416587175629507079788805 22015610095430532577460401)
      ·
        refine ⟨16511707571572899433095301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22015610095430532577460401 16511707571572899433095301)
        ·
          refine ⟨3095945169669918643705369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16511707571572899433095301 3095945169669918643705369)
          ·
            refine ⟨2321958877252438982779027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095945169669918643705369 2321958877252438982779027)
            ·
              refine ⟨3482938315878658474168541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321958877252438982779027 3482938315878658474168541)
              ·
                refine ⟨1306101868454496927813203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3482938315878658474168541 1306101868454496927813203)
                ·
                  refine ⟨1959152802681745391719805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306101868454496927813203 1959152802681745391719805)
                  ·
                    refine ⟨734682301005654521894927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959152802681745391719805 734682301005654521894927)
                    ·
                      rfl

theorem cell22_2146183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2146183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146183 prefixEnd_2146183 := by exact prefixLift 2146183
  have htrace : WordTrace (prefixWord ++ tailWord_2146183) baseStart_2146183 baseEnd_2146183 := by
    simpa [prefixWord, tailWord_2146183, baseEnd_2146183] using wordTrace_append hprefix tailTrace_2146183
  have hstable : (prefixWord ++ tailWord_2146183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146183).length < 2 ^ (prefixWord ++ tailWord_2146183).sum := by decide
  have hdescent : baseEnd_2146183 < baseStart_2146183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146200 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_2146200 : Nat := 118140960795 + 2146200 * 2 ^ 59
def prefixEnd_2146200 : Nat := 4983230072969 + 3 ^ 40 * 2146200 * 2
def baseEnd_2146200 : Nat := 734688120453072144219875

theorem tailTrace_2146200 : CollatzResearch.WordTrace tailWord_2146200 prefixEnd_2146200 734688120453072144219875 := by
  unfold tailWord_2146200
  simp only [CollatzResearch.WordTrace]
  refine ⟨39139172412345708311614027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52185563216460944415485369 39139172412345708311614027)
  ·
    refine ⟨58708758618518562467421041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39139172412345708311614027 58708758618518562467421041)
    ·
      refine ⟨44031568963888921850565781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58708758618518562467421041 44031568963888921850565781)
      ·
        refine ⟨2063979795182293211745271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44031568963888921850565781 2063979795182293211745271)
        ·
          refine ⟨3095969692773439817617907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063979795182293211745271 3095969692773439817617907)
          ·
            refine ⟨4643954539160159726426861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095969692773439817617907 4643954539160159726426861)
            ·
              refine ⟨1741482952185059897410073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4643954539160159726426861 1741482952185059897410073)
              ·
                refine ⟨1306112214138794923057555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741482952185059897410073 1306112214138794923057555)
                ·
                  refine ⟨1959168321208192384586333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306112214138794923057555 1959168321208192384586333)
                  ·
                    refine ⟨734688120453072144219875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959168321208192384586333 734688120453072144219875)
                    ·
                      rfl

theorem cell22_2146200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_2146200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146200 prefixEnd_2146200 := by exact prefixLift 2146200
  have htrace : WordTrace (prefixWord ++ tailWord_2146200) baseStart_2146200 baseEnd_2146200 := by
    simpa [prefixWord, tailWord_2146200, baseEnd_2146200] using wordTrace_append hprefix tailTrace_2146200
  have hstable : (prefixWord ++ tailWord_2146200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146200).length < 2 ^ (prefixWord ++ tailWord_2146200).sum := by decide
  have hdescent : baseEnd_2146200 < baseStart_2146200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146282 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2146282 : Nat := 118140960795 + 2146282 * 2 ^ 59
def prefixEnd_2146282 : Nat := 4983230072969 + 3 ^ 40 * 2146282 * 2
def baseEnd_2146282 : Nat := 734716190728851263669623

theorem tailTrace_2146282 : CollatzResearch.WordTrace tailWord_2146282 prefixEnd_2146282 734716190728851263669623 := by
  unfold tailWord_2146282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570333902598586156928275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52187557073596229751808733 19570333902598586156928275)
  ·
    refine ⟨29355500853897879235392413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19570333902598586156928275 29355500853897879235392413)
    ·
      refine ⟨11008312820211704713272155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29355500853897879235392413 11008312820211704713272155)
      ·
        refine ⟨16512469230317557069908233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11008312820211704713272155 16512469230317557069908233)
        ·
          refine ⟨12384351922738167802431175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16512469230317557069908233 12384351922738167802431175)
          ·
            refine ⟨18576527884107251703646763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12384351922738167802431175 18576527884107251703646763)
            ·
              refine ⟨27864791826160877555470145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18576527884107251703646763 27864791826160877555470145)
              ·
                refine ⟨20898593869620658166602609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27864791826160877555470145 20898593869620658166602609)
                ·
                  refine ⟨15673945402215493624951957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20898593869620658166602609 15673945402215493624951957)
                  ·
                    refine ⟨734716190728851263669623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15673945402215493624951957 734716190728851263669623)
                    ·
                      rfl

theorem cell22_2146282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2146282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146282 prefixEnd_2146282 := by exact prefixLift 2146282
  have htrace : WordTrace (prefixWord ++ tailWord_2146282) baseStart_2146282 baseEnd_2146282 := by
    simpa [prefixWord, tailWord_2146282, baseEnd_2146282] using wordTrace_append hprefix tailTrace_2146282
  have hstable : (prefixWord ++ tailWord_2146282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146282).length < 2 ^ (prefixWord ++ tailWord_2146282).sum := by decide
  have hdescent : baseEnd_2146282 < baseStart_2146282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146301 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_2146301 : Nat := 118140960795 + 2146301 * 2 ^ 59
def prefixEnd_2146301 : Nat := 4983230072969 + 3 ^ 40 * 2146301 * 2
def baseEnd_2146301 : Nat := 734722694817141547444565

theorem tailTrace_2146301 : CollatzResearch.WordTrace tailWord_2146301 prefixEnd_2146301 734722694817141547444565 := by
  unfold tailWord_2146301
  simp only [CollatzResearch.WordTrace]
  refine ⟨78282028597325510872654757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52188019064883673915103171 78282028597325510872654757)
  ·
    refine ⟨14677880361998533288622767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78282028597325510872654757 14677880361998533288622767)
    ·
      refine ⟨22016820542997799932934151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14677880361998533288622767 22016820542997799932934151)
      ·
        refine ⟨33025230814496699899401227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22016820542997799932934151 33025230814496699899401227)
        ·
          refine ⟨49537846221745049849101841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33025230814496699899401227 49537846221745049849101841)
          ·
            refine ⟨37153384666308787386826381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49537846221745049849101841 37153384666308787386826381)
            ·
              refine ⟨13932519249865795270059893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37153384666308787386826381 13932519249865795270059893)
              ·
                refine ⟨1306173679674918306568115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13932519249865795270059893 1306173679674918306568115)
                ·
                  refine ⟨1959260519512377459852173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306173679674918306568115 1959260519512377459852173)
                  ·
                    refine ⟨734722694817141547444565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959260519512377459852173 734722694817141547444565)
                    ·
                      rfl

theorem cell22_2146301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_2146301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146301 prefixEnd_2146301 := by exact prefixLift 2146301
  have htrace : WordTrace (prefixWord ++ tailWord_2146301) baseStart_2146301 baseEnd_2146301 := by
    simpa [prefixWord, tailWord_2146301, baseEnd_2146301] using wordTrace_append hprefix tailTrace_2146301
  have hstable : (prefixWord ++ tailWord_2146301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146301).length < 2 ^ (prefixWord ++ tailWord_2146301).sum := by decide
  have hdescent : baseEnd_2146301 < baseStart_2146301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146312 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2146312 : Nat := 118140960795 + 2146312 * 2 ^ 59
def prefixEnd_2146312 : Nat := 4983230072969 + 3 ^ 40 * 2146312 * 2
def baseEnd_2146312 : Nat := 734726460341941185419531

theorem tailTrace_2146312 : CollatzResearch.WordTrace tailWord_2146312 prefixEnd_2146312 734726460341941185419531 := by
  unfold tailWord_2146312
  simp only [CollatzResearch.WordTrace]
  refine ⟨39141214900142829875652595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52188286533523773167536793 39141214900142829875652595)
  ·
    refine ⟨58711822350214244813478893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39141214900142829875652595 58711822350214244813478893)
    ·
      refine ⟨22016933381330341805054585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58711822350214244813478893 22016933381330341805054585)
      ·
        refine ⟨16512700035997756353790939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22016933381330341805054585 16512700035997756353790939)
        ·
          refine ⟨24769050053996634530686409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16512700035997756353790939 24769050053996634530686409)
          ·
            refine ⟨18576787540497475898014807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24769050053996634530686409 18576787540497475898014807)
            ·
              refine ⟨27865181310746213847022211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18576787540497475898014807 27865181310746213847022211)
              ·
                refine ⟨41797771966119320770533317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27865181310746213847022211 41797771966119320770533317)
                ·
                  refine ⟨7837082243647372644474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41797771966119320770533317 7837082243647372644474997)
                  ·
                    refine ⟨734726460341941185419531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7837082243647372644474997 734726460341941185419531)
                    ·
                      rfl

theorem cell22_2146312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2146312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146312 prefixEnd_2146312 := by exact prefixLift 2146312
  have htrace : WordTrace (prefixWord ++ tailWord_2146312) baseStart_2146312 baseEnd_2146312 := by
    simpa [prefixWord, tailWord_2146312, baseEnd_2146312] using wordTrace_append hprefix tailTrace_2146312
  have hstable : (prefixWord ++ tailWord_2146312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146312).length < 2 ^ (prefixWord ++ tailWord_2146312).sum := by decide
  have hdescent : baseEnd_2146312 < baseStart_2146312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146314 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_2146314 : Nat := 118140960795 + 2146314 * 2 ^ 59
def prefixEnd_2146314 : Nat := 4983230072969 + 3 ^ 40 * 2146314 * 2
def baseEnd_2146314 : Nat := 244909048327604615623175

theorem tailTrace_2146314 : CollatzResearch.WordTrace tailWord_2146314 prefixEnd_2146314 244909048327604615623175 := by
  unfold tailWord_2146314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570625686569603523219499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52188335164185609395251997 19570625686569603523219499)
  ·
    refine ⟨29355938529854405284829249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19570625686569603523219499 29355938529854405284829249)
    ·
      refine ⟨22016953897390803963621937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29355938529854405284829249 22016953897390803963621937)
      ·
        refine ⟨16512715423043102972716453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22016953897390803963621937 16512715423043102972716453)
        ·
          refine ⟨3096134141820581807384335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16512715423043102972716453 3096134141820581807384335)
          ·
            refine ⟨4644201212730872711076503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096134141820581807384335 4644201212730872711076503)
            ·
              refine ⟨6966301819096309066614755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644201212730872711076503 6966301819096309066614755)
              ·
                refine ⟨10449452728644463599922133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6966301819096309066614755 10449452728644463599922133)
                ·
                  refine ⟨244909048327604615623175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10449452728644463599922133 244909048327604615623175)
                  ·
                    rfl

theorem cell22_2146314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_2146314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146314 prefixEnd_2146314 := by exact prefixLift 2146314
  have htrace : WordTrace (prefixWord ++ tailWord_2146314) baseStart_2146314 baseEnd_2146314 := by
    simpa [prefixWord, tailWord_2146314, baseEnd_2146314] using wordTrace_append hprefix tailTrace_2146314
  have hstable : (prefixWord ++ tailWord_2146314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146314).length < 2 ^ (prefixWord ++ tailWord_2146314).sum := by decide
  have hdescent : baseEnd_2146314 < baseStart_2146314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146436 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2146436 : Nat := 118140960795 + 2146436 * 2 ^ 59
def prefixEnd_2146436 : Nat := 4983230072969 + 3 ^ 40 * 2146436 * 2
def baseEnd_2146436 : Nat := 734768908076046195319151

theorem tailTrace_2146436 : CollatzResearch.WordTrace tailWord_2146436 prefixEnd_2146436 734768908076046195319151 := by
  unfold tailWord_2146436
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143476225918214464409581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52191301634557619285879441 39143476225918214464409581)
  ·
    refine ⟨14678803584719330424153593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39143476225918214464409581 14678803584719330424153593)
    ·
      refine ⟨11009102688539497818115195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14678803584719330424153593 11009102688539497818115195)
      ·
        refine ⟨16513654032809246727172793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11009102688539497818115195 16513654032809246727172793)
        ·
          refine ⟨12385240524606935045379595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16513654032809246727172793 12385240524606935045379595)
          ·
            refine ⟨18577860786910402568069393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12385240524606935045379595 18577860786910402568069393)
            ·
              refine ⟨13933395590182801926052045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18577860786910402568069393 13933395590182801926052045)
              ·
                refine ⟨5225023346318550722269517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13933395590182801926052045 5225023346318550722269517)
                ·
                  refine ⟨1959383754869456520851069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5225023346318550722269517 1959383754869456520851069)
                  ·
                    refine ⟨734768908076046195319151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959383754869456520851069 734768908076046195319151)
                    ·
                      rfl

theorem cell22_2146436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2146436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146436 prefixEnd_2146436 := by exact prefixLift 2146436
  have htrace : WordTrace (prefixWord ++ tailWord_2146436) baseStart_2146436 baseEnd_2146436 := by
    simpa [prefixWord, tailWord_2146436, baseEnd_2146436] using wordTrace_append hprefix tailTrace_2146436
  have hstable : (prefixWord ++ tailWord_2146436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146436).length < 2 ^ (prefixWord ++ tailWord_2146436).sum := by decide
  have hdescent : baseEnd_2146436 < baseStart_2146436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146556 : List Nat := [2, 2, 2, 1, 4, 2, 2, 7]
def baseStart_2146556 : Nat := 118140960795 + 2146556 * 2 ^ 59
def prefixEnd_2146556 : Nat := 4983230072969 + 3 ^ 40 * 2146556 * 2
def baseEnd_2146556 : Nat := 81645554058711764702087

theorem tailTrace_2146556 : CollatzResearch.WordTrace tailWord_2146556 prefixEnd_2146556 81645554058711764702087 := by
  unfold tailWord_2146556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39145664605700844711593761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52194219474267792948791681 39145664605700844711593761)
  ·
    refine ⟨29359248454275633533695321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39145664605700844711593761 29359248454275633533695321)
    ·
      refine ⟨22019436340706725150271491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29359248454275633533695321 22019436340706725150271491)
      ·
        refine ⟨33029154511060087725407237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22019436340706725150271491 33029154511060087725407237)
        ·
          refine ⟨6192966470823766448513857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33029154511060087725407237 6192966470823766448513857)
          ·
            refine ⟨4644724853117824836385393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192966470823766448513857 4644724853117824836385393)
            ·
              refine ⟨3483543639838368627289045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4644724853117824836385393 3483543639838368627289045)
              ·
                refine ⟨81645554058711764702087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3483543639838368627289045 81645554058711764702087)
                ·
                  rfl

theorem cell22_2146556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_2146556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146556 prefixEnd_2146556 := by exact prefixLift 2146556
  have htrace : WordTrace (prefixWord ++ tailWord_2146556) baseStart_2146556 baseEnd_2146556 := by
    simpa [prefixWord, tailWord_2146556, baseEnd_2146556] using wordTrace_append hprefix tailTrace_2146556
  have hstable : (prefixWord ++ tailWord_2146556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146556).length < 2 ^ (prefixWord ++ tailWord_2146556).sum := by decide
  have hdescent : baseEnd_2146556 < baseStart_2146556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146571 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 5, 3]
def baseStart_2146571 : Nat := 118140960795 + 2146571 * 2 ^ 59
def prefixEnd_2146571 : Nat := 4983230072969 + 3 ^ 40 * 2146571 * 2
def baseEnd_2146571 : Nat := 734815121334950843193737

theorem tailTrace_2146571 : CollatzResearch.WordTrace tailWord_2146571 prefixEnd_2146571 734815121334950843193737 := by
  unfold tailWord_2146571
  simp only [CollatzResearch.WordTrace]
  refine ⟨78291876306347346984983567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52194584204231564656655711 78291876306347346984983567)
  ·
    refine ⟨117437814459521020477475351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78291876306347346984983567 117437814459521020477475351)
    ·
      refine ⟨176156721689281530716213027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117437814459521020477475351 176156721689281530716213027)
      ·
        refine ⟨264235082533922296074319541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176156721689281530716213027 264235082533922296074319541)
        ·
          refine ⟨24772038987555215256967457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264235082533922296074319541 24772038987555215256967457)
          ·
            refine ⟨18579029240666411442725593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24772038987555215256967457 18579029240666411442725593)
            ·
              refine ⟨13934271930499808582044195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18579029240666411442725593 13934271930499808582044195)
              ·
                refine ⟨20901407895749712873066293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13934271930499808582044195 20901407895749712873066293)
                ·
                  refine ⟨1959506990226535581849965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20901407895749712873066293 1959506990226535581849965)
                  ·
                    refine ⟨734815121334950843193737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959506990226535581849965 734815121334950843193737)
                    ·
                      rfl

theorem cell22_2146571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].length) (baseStart_2146571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146571 prefixEnd_2146571 := by exact prefixLift 2146571
  have htrace : WordTrace (prefixWord ++ tailWord_2146571) baseStart_2146571 baseEnd_2146571 := by
    simpa [prefixWord, tailWord_2146571, baseEnd_2146571] using wordTrace_append hprefix tailTrace_2146571
  have hstable : (prefixWord ++ tailWord_2146571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146571).length < 2 ^ (prefixWord ++ tailWord_2146571).sum := by decide
  have hdescent : baseEnd_2146571 < baseStart_2146571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146631 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2146631 : Nat := 118140960795 + 2146631 * 2 ^ 59
def prefixEnd_2146631 : Nat := 4983230072969 + 3 ^ 40 * 2146631 * 2
def baseEnd_2146631 : Nat := 734835660561130686693553

theorem tailTrace_2146631 : CollatzResearch.WordTrace tailWord_2146631 prefixEnd_2146631 734835660561130686693553 := by
  unfold tailWord_2146631
  simp only [CollatzResearch.WordTrace]
  refine ⟨78294064686129977232167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52196043124086651488111831 78294064686129977232167747)
  ·
    refine ⟨117441097029194965848251621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78294064686129977232167747 117441097029194965848251621)
    ·
      refine ⟨22020205692974056096547179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117441097029194965848251621 22020205692974056096547179)
      ·
        refine ⟨33030308539461084144820769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22020205692974056096547179 33030308539461084144820769)
        ·
          refine ⟨24772731404595813108615577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33030308539461084144820769 24772731404595813108615577)
          ·
            refine ⟨18579548553446859831461683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24772731404595813108615577 18579548553446859831461683)
            ·
              refine ⟨27869322830170289747192525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18579548553446859831461683 27869322830170289747192525)
              ·
                refine ⟨10450996061313858655197197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27869322830170289747192525 10450996061313858655197197)
                ·
                  refine ⟨3919123522992696995698949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10450996061313858655197197 3919123522992696995698949)
                  ·
                    refine ⟨734835660561130686693553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919123522992696995698949 734835660561130686693553)
                    ·
                      rfl

theorem cell22_2146631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2146631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146631 prefixEnd_2146631 := by exact prefixLift 2146631
  have htrace : WordTrace (prefixWord ++ tailWord_2146631) baseStart_2146631 baseEnd_2146631 := by
    simpa [prefixWord, tailWord_2146631, baseEnd_2146631] using wordTrace_append hprefix tailTrace_2146631
  have hstable : (prefixWord ++ tailWord_2146631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146631).length < 2 ^ (prefixWord ++ tailWord_2146631).sum := by decide
  have hdescent : baseEnd_2146631 < baseStart_2146631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146652 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_2146652 : Nat := 118140960795 + 2146652 * 2 ^ 59
def prefixEnd_2146652 : Nat := 4983230072969 + 3 ^ 40 * 2146652 * 2
def baseEnd_2146652 : Nat := 244947616430097877306163

theorem tailTrace_2146652 : CollatzResearch.WordTrace tailWord_2146652 prefixEnd_2146652 244947616430097877306163 := by
  unfold tailWord_2146652
  simp only [CollatzResearch.WordTrace]
  refine ⟨39147415309526948909341105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52196553746035931879121473 39147415309526948909341105)
  ·
    refine ⟨29360561482145211682005829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39147415309526948909341105 29360561482145211682005829)
    ·
      refine ⟨5505105277902227190376093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29360561482145211682005829 5505105277902227190376093)
      ·
        refine ⟨2064414479213335196391035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5505105277902227190376093 2064414479213335196391035)
        ·
          refine ⟨3096621718820002794586553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064414479213335196391035 3096621718820002794586553)
          ·
            refine ⟨2322466289115002095939915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3096621718820002794586553 2322466289115002095939915)
            ·
              refine ⟨3483699433672503143909873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322466289115002095939915 3483699433672503143909873)
              ·
                refine ⟨2612774575254377357932405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3483699433672503143909873 2612774575254377357932405)
                ·
                  refine ⟨244947616430097877306163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612774575254377357932405 244947616430097877306163)
                  ·
                    rfl

theorem cell22_2146652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_2146652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146652 prefixEnd_2146652 := by exact prefixLift 2146652
  have htrace : WordTrace (prefixWord ++ tailWord_2146652) baseStart_2146652 baseEnd_2146652 := by
    simpa [prefixWord, tailWord_2146652, baseEnd_2146652] using wordTrace_append hprefix tailTrace_2146652
  have hstable : (prefixWord ++ tailWord_2146652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146652).length < 2 ^ (prefixWord ++ tailWord_2146652).sum := by decide
  have hdescent : baseEnd_2146652 < baseStart_2146652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146663 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 6]
def baseStart_2146663 : Nat := 118140960795 + 2146663 * 2 ^ 59
def prefixEnd_2146663 : Nat := 4983230072969 + 3 ^ 40 * 2146663 * 2
def baseEnd_2146663 : Nat := 244948871605031089964485

theorem tailTrace_2146663 : CollatzResearch.WordTrace tailWord_2146663 prefixEnd_2146663 244948871605031089964485 := by
  unfold tailWord_2146663
  simp only [CollatzResearch.WordTrace]
  refine ⟨78295231822014046697332643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52196821214676031131555095 78295231822014046697332643)
  ·
    refine ⟨117442847733021070045998965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78295231822014046697332643 117442847733021070045998965)
    ·
      refine ⟨11010266974970725316812403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117442847733021070045998965 11010266974970725316812403)
      ·
        refine ⟨16515400462456087975218605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010266974970725316812403 16515400462456087975218605)
        ·
          refine ⟨6193275173421032990706977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16515400462456087975218605 6193275173421032990706977)
          ·
            refine ⟨4644956380065774743030233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6193275173421032990706977 4644956380065774743030233)
            ·
              refine ⟨3483717285049331057272675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4644956380065774743030233 3483717285049331057272675)
              ·
                refine ⟨5225575927573996585909013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483717285049331057272675 5225575927573996585909013)
                ·
                  refine ⟨244948871605031089964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5225575927573996585909013 244948871605031089964485)
                  ·
                    rfl

theorem cell22_2146663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_2146663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146663 prefixEnd_2146663 := by exact prefixLift 2146663
  have htrace : WordTrace (prefixWord ++ tailWord_2146663) baseStart_2146663 baseEnd_2146663 := by
    simpa [prefixWord, tailWord_2146663, baseEnd_2146663] using wordTrace_append hprefix tailTrace_2146663
  have hstable : (prefixWord ++ tailWord_2146663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146663).length < 2 ^ (prefixWord ++ tailWord_2146663).sum := by decide
  have hdescent : baseEnd_2146663 < baseStart_2146663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146751 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_2146751 : Nat := 118140960795 + 2146751 * 2 ^ 59
def prefixEnd_2146751 : Nat := 4983230072969 + 3 ^ 40 * 2146751 * 2
def baseEnd_2146751 : Nat := 734876739013490373693185

theorem tailTrace_2146751 : CollatzResearch.WordTrace tailWord_2146751 prefixEnd_2146751 734876739013490373693185 := by
  unfold tailWord_2146751
  simp only [CollatzResearch.WordTrace]
  refine ⟨78298441445695237726536107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52198960963796825151024071 78298441445695237726536107)
  ·
    refine ⟨117447662168542856589804161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78298441445695237726536107 117447662168542856589804161)
    ·
      refine ⟨88085746626407142442353121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117447662168542856589804161 88085746626407142442353121)
      ·
        refine ⟨66064309969805356831764841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88085746626407142442353121 66064309969805356831764841)
        ·
          refine ⟨49548232477354017623823631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66064309969805356831764841 49548232477354017623823631)
          ·
            refine ⟨74322348716031026435735447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49548232477354017623823631 74322348716031026435735447)
            ·
              refine ⟨111483523074046539653603171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74322348716031026435735447 111483523074046539653603171)
              ·
                refine ⟨167225284611069809480404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111483523074046539653603171 167225284611069809480404757)
                ·
                  refine ⟨7838685216143897319393973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167225284611069809480404757 7838685216143897319393973)
                  ·
                    refine ⟨734876739013490373693185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7838685216143897319393973 734876739013490373693185)
                    ·
                      rfl

theorem cell22_2146751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_2146751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146751 prefixEnd_2146751 := by exact prefixLift 2146751
  have htrace : WordTrace (prefixWord ++ tailWord_2146751) baseStart_2146751 baseEnd_2146751 := by
    simpa [prefixWord, tailWord_2146751, baseEnd_2146751] using wordTrace_append hprefix tailTrace_2146751
  have hstable : (prefixWord ++ tailWord_2146751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146751).length < 2 ^ (prefixWord ++ tailWord_2146751).sum := by decide
  have hdescent : baseEnd_2146751 < baseStart_2146751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146774 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2146774 : Nat := 118140960795 + 2146774 * 2 ^ 59
def prefixEnd_2146774 : Nat := 4983230072969 + 3 ^ 40 * 2146774 * 2
def baseEnd_2146774 : Nat := 734884612383525980368115

theorem tailTrace_2146774 : CollatzResearch.WordTrace tailWord_2146774 prefixEnd_2146774 734884612383525980368115 := by
  unfold tailWord_2146774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893705020288244540913961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52199520216407941769748917 4893705020288244540913961)
  ·
    refine ⟨3670278765216183405685471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4893705020288244540913961 3670278765216183405685471)
    ·
      refine ⟨5505418147824275108528207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3670278765216183405685471 5505418147824275108528207)
      ·
        refine ⟨8258127221736412662792311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505418147824275108528207 8258127221736412662792311)
        ·
          refine ⟨12387190832604618994188467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8258127221736412662792311 12387190832604618994188467)
          ·
            refine ⟨18580786248906928491282701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12387190832604618994188467 18580786248906928491282701)
            ·
              refine ⟨6967794843340098184231013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18580786248906928491282701 6967794843340098184231013)
              ·
                refine ⟨1306461533126268409543315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6967794843340098184231013 1306461533126268409543315)
                ·
                  refine ⟨1959692299689402614314973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306461533126268409543315 1959692299689402614314973)
                  ·
                    refine ⟨734884612383525980368115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959692299689402614314973 734884612383525980368115)
                    ·
                      rfl

theorem cell22_2146774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2146774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146774 prefixEnd_2146774 := by exact prefixLift 2146774
  have htrace : WordTrace (prefixWord ++ tailWord_2146774) baseStart_2146774 baseEnd_2146774 := by
    simpa [prefixWord, tailWord_2146774, baseEnd_2146774] using wordTrace_append hprefix tailTrace_2146774
  have hstable : (prefixWord ++ tailWord_2146774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146774).length < 2 ^ (prefixWord ++ tailWord_2146774).sum := by decide
  have hdescent : baseEnd_2146774 < baseStart_2146774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146783 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_2146783 : Nat := 118140960795 + 2146783 * 2 ^ 59
def prefixEnd_2146783 : Nat := 4983230072969 + 3 ^ 40 * 2146783 * 2
def baseEnd_2146783 : Nat := 734887693267452956893087

theorem tailTrace_2146783 : CollatzResearch.WordTrace tailWord_2146783 prefixEnd_2146783 734887693267452956893087 := by
  unfold tailWord_2146783
  simp only [CollatzResearch.WordTrace]
  refine ⟨78299608581579307191701003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52199739054386204794467335 78299608581579307191701003)
  ·
    refine ⟨117449412872368960787551505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78299608581579307191701003 117449412872368960787551505)
    ·
      refine ⟨88087059654276720590663629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117449412872368960787551505 88087059654276720590663629)
      ·
        refine ⟨33032647370353770221498861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88087059654276720590663629 33032647370353770221498861)
        ·
          refine ⟨12387242763882663833062073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33032647370353770221498861 12387242763882663833062073)
          ·
            refine ⟨9290432072911997874796555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12387242763882663833062073 9290432072911997874796555)
            ·
              refine ⟨13935648109367996812194833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9290432072911997874796555 13935648109367996812194833)
              ·
                refine ⟨10451736082025997609146125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13935648109367996812194833 10451736082025997609146125)
                ·
                  refine ⟨3919401030759749103429797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10451736082025997609146125 3919401030759749103429797)
                  ·
                    refine ⟨734887693267452956893087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919401030759749103429797 734887693267452956893087)
                    ·
                      rfl

theorem cell22_2146783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_2146783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146783 prefixEnd_2146783 := by exact prefixLift 2146783
  have htrace : WordTrace (prefixWord ++ tailWord_2146783) baseStart_2146783 baseEnd_2146783 := by
    simpa [prefixWord, tailWord_2146783, baseEnd_2146783] using wordTrace_append hprefix tailTrace_2146783
  have hstable : (prefixWord ++ tailWord_2146783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146783).length < 2 ^ (prefixWord ++ tailWord_2146783).sum := by decide
  have hdescent : baseEnd_2146783 < baseStart_2146783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146798 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_2146798 : Nat := 118140960795 + 2146798 * 2 ^ 59
def prefixEnd_2146798 : Nat := 4983230072969 + 3 ^ 40 * 2146798 * 2
def baseEnd_2146798 : Nat := 244964276024665972589347

theorem tailTrace_2146798 : CollatzResearch.WordTrace tailWord_2146798 prefixEnd_2146798 244964276024665972589347 := by
  unfold tailWord_2146798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787519459565620594187131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52200103784349976502331365 9787519459565620594187131)
  ·
    refine ⟨14681279189348430891280697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9787519459565620594187131 14681279189348430891280697)
    ·
      refine ⟨11010959392011323168460523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14681279189348430891280697 11010959392011323168460523)
      ·
        refine ⟨16516439088016984752690785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010959392011323168460523 16516439088016984752690785)
        ·
          refine ⟨12387329316012738564518089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16516439088016984752690785 12387329316012738564518089)
          ·
            refine ⟨9290496987009553923388567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12387329316012738564518089 9290496987009553923388567)
            ·
              refine ⟨13935745480514330885082851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9290496987009553923388567 13935745480514330885082851)
              ·
                refine ⟨20903618220771496327624277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13935745480514330885082851 20903618220771496327624277)
                ·
                  refine ⟨244964276024665972589347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20903618220771496327624277 244964276024665972589347)
                  ·
                    rfl

theorem cell22_2146798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_2146798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146798 prefixEnd_2146798 := by exact prefixLift 2146798
  have htrace : WordTrace (prefixWord ++ tailWord_2146798) baseStart_2146798 baseEnd_2146798 := by
    simpa [prefixWord, tailWord_2146798, baseEnd_2146798] using wordTrace_append hprefix tailTrace_2146798
  have hstable : (prefixWord ++ tailWord_2146798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146798).length < 2 ^ (prefixWord ++ tailWord_2146798).sum := by decide
  have hdescent : baseEnd_2146798 < baseStart_2146798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146813 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2146813 : Nat := 118140960795 + 2146813 * 2 ^ 59
def prefixEnd_2146813 : Nat := 4983230072969 + 3 ^ 40 * 2146813 * 2
def baseEnd_2146813 : Nat := 734897962880542878642995

theorem tailTrace_2146813 : CollatzResearch.WordTrace tailWord_2146813 prefixEnd_2146813 734897962880542878642995 := by
  unfold tailWord_2146813
  simp only [CollatzResearch.WordTrace]
  refine ⟨78300702771470622315293093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52200468514313748210195395 78300702771470622315293093)
  ·
    refine ⟨14681381769650741684117455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78300702771470622315293093 14681381769650741684117455)
    ·
      refine ⟨22022072654476112526176183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14681381769650741684117455 22022072654476112526176183)
      ·
        refine ⟨33033108981714168789264275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22022072654476112526176183 33033108981714168789264275)
        ·
          refine ⟨49549663472571253183896413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33033108981714168789264275 49549663472571253183896413)
          ·
            refine ⟨18581123802214219943961155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49549663472571253183896413 18581123802214219943961155)
            ·
              refine ⟨27871685703321329915941733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18581123802214219943961155 27871685703321329915941733)
              ·
                refine ⟨5225941069372749359239075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27871685703321329915941733 5225941069372749359239075)
                ·
                  refine ⟨7838911604059124038858613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5225941069372749359239075 7838911604059124038858613)
                  ·
                    refine ⟨734897962880542878642995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7838911604059124038858613 734897962880542878642995)
                    ·
                      rfl

theorem cell22_2146813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2146813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146813 prefixEnd_2146813 := by exact prefixLift 2146813
  have htrace : WordTrace (prefixWord ++ tailWord_2146813) baseStart_2146813 baseEnd_2146813 := by
    simpa [prefixWord, tailWord_2146813, baseEnd_2146813] using wordTrace_append hprefix tailTrace_2146813
  have hstable : (prefixWord ++ tailWord_2146813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146813).length < 2 ^ (prefixWord ++ tailWord_2146813).sum := by decide
  have hdescent : baseEnd_2146813 < baseStart_2146813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146815 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 4]
def baseStart_2146815 : Nat := 118140960795 + 2146815 * 2 ^ 59
def prefixEnd_2146815 : Nat := 4983230072969 + 3 ^ 40 * 2146815 * 2
def baseEnd_2146815 : Nat := 244966215840471846697663

theorem tailTrace_2146815 : CollatzResearch.WordTrace tailWord_2146815 prefixEnd_2146815 244966215840471846697663 := by
  unfold tailWord_2146815
  simp only [CollatzResearch.WordTrace]
  refine ⟨78300775717463376656865899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52200517144975584437910599 78300775717463376656865899)
  ·
    refine ⟨117451163576195064985298849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78300775717463376656865899 117451163576195064985298849)
    ·
      refine ⟨88088372682146298738974137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117451163576195064985298849 88088372682146298738974137)
      ·
        refine ⟨66066279511609724054230603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88088372682146298738974137 66066279511609724054230603)
        ·
          refine ⟨99099419267414586081345905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66066279511609724054230603 99099419267414586081345905)
          ·
            refine ⟨74324564450560939561009429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99099419267414586081345905 74324564450560939561009429)
            ·
              refine ⟨3483963958620044041922317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74324564450560939561009429 3483963958620044041922317)
              ·
                refine ⟨1306486484482516515720869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3483963958620044041922317 1306486484482516515720869)
                ·
                  refine ⟨244966215840471846697663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306486484482516515720869 244966215840471846697663)
                  ·
                    rfl

theorem cell22_2146815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 4].length) (baseStart_2146815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146815 prefixEnd_2146815 := by exact prefixLift 2146815
  have htrace : WordTrace (prefixWord ++ tailWord_2146815) baseStart_2146815 baseEnd_2146815 := by
    simpa [prefixWord, tailWord_2146815, baseEnd_2146815] using wordTrace_append hprefix tailTrace_2146815
  have hstable : (prefixWord ++ tailWord_2146815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146815).length < 2 ^ (prefixWord ++ tailWord_2146815).sum := by decide
  have hdescent : baseEnd_2146815 < baseStart_2146815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146817 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2146817 : Nat := 118140960795 + 2146817 * 2 ^ 59
def prefixEnd_2146817 : Nat := 4983230072969 + 3 ^ 40 * 2146817 * 2
def baseEnd_2146817 : Nat := 734899332162288201542983

theorem tailTrace_2146817 : CollatzResearch.WordTrace tailWord_2146817 prefixEnd_2146817 734899332162288201542983 := by
  unfold tailWord_2146817
  simp only [CollatzResearch.WordTrace]
  refine ⟨78300848663456130998438705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52200565775637420665625803 78300848663456130998438705)
  ·
    refine ⟨58725636497592098248829029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78300848663456130998438705 58725636497592098248829029)
    ·
      refine ⟨11011056843298518421655443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58725636497592098248829029 11011056843298518421655443)
      ·
        refine ⟨16516585264947777632483165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11011056843298518421655443 16516585264947777632483165)
        ·
          refine ⟨6193719474355416612181187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16516585264947777632483165 6193719474355416612181187)
          ·
            refine ⟨9290579211533124918271781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193719474355416612181187 9290579211533124918271781)
            ·
              refine ⟨1741983602162460922175959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9290579211533124918271781 1741983602162460922175959)
              ·
                refine ⟨2612975403243691383263939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741983602162460922175959 2612975403243691383263939)
                ·
                  refine ⟨3919463104865537074895909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612975403243691383263939 3919463104865537074895909)
                  ·
                    refine ⟨734899332162288201542983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919463104865537074895909 734899332162288201542983)
                    ·
                      rfl

theorem cell22_2146817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2146817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146817 prefixEnd_2146817 := by exact prefixLift 2146817
  have htrace : WordTrace (prefixWord ++ tailWord_2146817) baseStart_2146817 baseEnd_2146817 := by
    simpa [prefixWord, tailWord_2146817, baseEnd_2146817] using wordTrace_append hprefix tailTrace_2146817
  have hstable : (prefixWord ++ tailWord_2146817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146817).length < 2 ^ (prefixWord ++ tailWord_2146817).sum := by decide
  have hdescent : baseEnd_2146817 < baseStart_2146817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146903 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2146903 : Nat := 118140960795 + 2146903 * 2 ^ 59
def prefixEnd_2146903 : Nat := 4983230072969 + 3 ^ 40 * 2146903 * 2
def baseEnd_2146903 : Nat := 734928771719812643892719

theorem tailTrace_2146903 : CollatzResearch.WordTrace tailWord_2146903 prefixEnd_2146903 734928771719812643892719 := by
  unfold tailWord_2146903
  simp only [CollatzResearch.WordTrace]
  refine ⟨78303985341144567686069363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52202656894096378457379575 78303985341144567686069363)
  ·
    refine ⟨117455978011716851529104045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78303985341144567686069363 117455978011716851529104045)
    ·
      refine ⟨44045991754393819323414017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117455978011716851529104045 44045991754393819323414017)
      ·
        refine ⟨33034493815795364492560513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44045991754393819323414017 33034493815795364492560513)
        ·
          refine ⟨24775870361846523369420385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33034493815795364492560513 24775870361846523369420385)
          ·
            refine ⟨18581902771384892527065289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24775870361846523369420385 18581902771384892527065289)
            ·
              refine ⟨13936427078538669395298967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18581902771384892527065289 13936427078538669395298967)
              ·
                refine ⟨20904640617808004092948451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13936427078538669395298967 20904640617808004092948451)
                ·
                  refine ⟨31356960926712006139422677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20904640617808004092948451 31356960926712006139422677)
                  ·
                    refine ⟨734928771719812643892719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31356960926712006139422677 734928771719812643892719)
                    ·
                      rfl

theorem cell22_2146903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2146903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146903 prefixEnd_2146903 := by exact prefixLift 2146903
  have htrace : WordTrace (prefixWord ++ tailWord_2146903) baseStart_2146903 baseEnd_2146903 := by
    simpa [prefixWord, tailWord_2146903, baseEnd_2146903] using wordTrace_append hprefix tailTrace_2146903
  have hstable : (prefixWord ++ tailWord_2146903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146903).length < 2 ^ (prefixWord ++ tailWord_2146903).sum := by decide
  have hdescent : baseEnd_2146903 < baseStart_2146903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146935 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2146935 : Nat := 118140960795 + 2146935 * 2 ^ 59
def prefixEnd_2146935 : Nat := 4983230072969 + 3 ^ 40 * 2146935 * 2
def baseEnd_2146935 : Nat := 734939725973775227092621

theorem tailTrace_2146935 : CollatzResearch.WordTrace tailWord_2146935 prefixEnd_2146935 734939725973775227092621 := by
  unfold tailWord_2146935
  simp only [CollatzResearch.WordTrace]
  refine ⟨78305152477028637151234259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52203434984685758100822839 78305152477028637151234259)
  ·
    refine ⟨117457728715542955726851389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78305152477028637151234259 117457728715542955726851389)
    ·
      refine ⟨44046648268328608397569271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117457728715542955726851389 44046648268328608397569271)
      ·
        refine ⟨66069972402492912596353907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44046648268328608397569271 66069972402492912596353907)
        ·
          refine ⟨99104958603739368894530861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66069972402492912596353907 99104958603739368894530861)
          ·
            refine ⟨37164359476402263335449073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99104958603739368894530861 37164359476402263335449073)
            ·
              refine ⟨27873269607301697501586805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37164359476402263335449073 27873269607301697501586805)
              ·
                refine ⟨2613119025684534140773763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27873269607301697501586805 2613119025684534140773763)
                ·
                  refine ⟨3919678538526801211160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613119025684534140773763 3919678538526801211160645)
                  ·
                    refine ⟨734939725973775227092621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919678538526801211160645 734939725973775227092621)
                    ·
                      rfl

theorem cell22_2146935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2146935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146935 prefixEnd_2146935 := by exact prefixLift 2146935
  have htrace : WordTrace (prefixWord ++ tailWord_2146935) baseStart_2146935 baseEnd_2146935 := by
    simpa [prefixWord, tailWord_2146935, baseEnd_2146935] using wordTrace_append hprefix tailTrace_2146935
  have hstable : (prefixWord ++ tailWord_2146935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146935).length < 2 ^ (prefixWord ++ tailWord_2146935).sum := by decide
  have hdescent : baseEnd_2146935 < baseStart_2146935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146963 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_2146963 : Nat := 118140960795 + 2146963 * 2 ^ 59
def prefixEnd_2146963 : Nat := 4983230072969 + 3 ^ 40 * 2146963 * 2
def baseEnd_2146963 : Nat := 734949310945992487392535

theorem tailTrace_2146963 : CollatzResearch.WordTrace tailWord_2146963 prefixEnd_2146963 734949310945992487392535 := by
  unfold tailWord_2146963
  simp only [CollatzResearch.WordTrace]
  refine ⟨78306173720927197933253543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52204115813951465288835695 78306173720927197933253543)
  ·
    refine ⟨117459260581390796899880315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78306173720927197933253543 117459260581390796899880315)
    ·
      refine ⟨176188890872086195349820473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117459260581390796899880315 176188890872086195349820473)
      ·
        refine ⟨132141668154064646512365355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176188890872086195349820473 132141668154064646512365355)
        ·
          refine ⟨198212502231096969768548033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132141668154064646512365355 198212502231096969768548033)
          ·
            refine ⟨148659376673322727326411025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198212502231096969768548033 148659376673322727326411025)
            ·
              refine ⟨111494532504992045494808269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148659376673322727326411025 111494532504992045494808269)
              ·
                refine ⟨41810449689372017060553101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111494532504992045494808269 41810449689372017060553101)
                ·
                  refine ⟨15678918633514506397707413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41810449689372017060553101 15678918633514506397707413)
                  ·
                    refine ⟨734949310945992487392535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15678918633514506397707413 734949310945992487392535)
                    ·
                      rfl

theorem cell22_2146963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_2146963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146963 prefixEnd_2146963 := by exact prefixLift 2146963
  have htrace : WordTrace (prefixWord ++ tailWord_2146963) baseStart_2146963 baseEnd_2146963 := by
    simpa [prefixWord, tailWord_2146963, baseEnd_2146963] using wordTrace_append hprefix tailTrace_2146963
  have hstable : (prefixWord ++ tailWord_2146963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146963).length < 2 ^ (prefixWord ++ tailWord_2146963).sum := by decide
  have hdescent : baseEnd_2146963 < baseStart_2146963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146965 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_2146965 : Nat := 118140960795 + 2146965 * 2 ^ 59
def prefixEnd_2146965 : Nat := 4983230072969 + 3 ^ 40 * 2146965 * 2
def baseEnd_2146965 : Nat := 734949995586865148842529

theorem tailTrace_2146965 : CollatzResearch.WordTrace tailWord_2146965 prefixEnd_2146965 734949995586865148842529 := by
  unfold tailWord_2146965
  simp only [CollatzResearch.WordTrace]
  refine ⟨78306246666919952274826349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52204164444613301516550899 78306246666919952274826349)
  ·
    refine ⟨29364842500094982103059881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78306246666919952274826349 29364842500094982103059881)
    ·
      refine ⟨22023631875071236577294911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29364842500094982103059881 22023631875071236577294911)
      ·
        refine ⟨33035447812606854865942367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22023631875071236577294911 33035447812606854865942367)
        ·
          refine ⟨49553171718910282298913551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33035447812606854865942367 49553171718910282298913551)
          ·
            refine ⟨74329757578365423448370327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49553171718910282298913551 74329757578365423448370327)
            ·
              refine ⟨111494636367548135172555491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74329757578365423448370327 111494636367548135172555491)
              ·
                refine ⟨167241954551322202758833237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111494636367548135172555491 167241954551322202758833237)
                ·
                  refine ⟨1959866654898307063580077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 167241954551322202758833237 1959866654898307063580077)
                  ·
                    refine ⟨734949995586865148842529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1959866654898307063580077 734949995586865148842529)
                    ·
                      rfl

theorem cell22_2146965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_2146965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146965 prefixEnd_2146965 := by exact prefixLift 2146965
  have htrace : WordTrace (prefixWord ++ tailWord_2146965) baseStart_2146965 baseEnd_2146965 := by
    simpa [prefixWord, tailWord_2146965, baseEnd_2146965] using wordTrace_append hprefix tailTrace_2146965
  have hstable : (prefixWord ++ tailWord_2146965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146965).length < 2 ^ (prefixWord ++ tailWord_2146965).sum := by decide
  have hdescent : baseEnd_2146965 < baseStart_2146965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146980 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2146980 : Nat := 118140960795 + 2146980 * 2 ^ 59
def prefixEnd_2146980 : Nat := 4983230072969 + 3 ^ 40 * 2146980 * 2
def baseEnd_2146980 : Nat := 734955130393410109717483

theorem tailTrace_2146980 : CollatzResearch.WordTrace tailWord_2146980 prefixEnd_2146980 734955130393410109717483 := by
  unfold tailWord_2146980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39153396880932804918311197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52204529174577073224414929 39153396880932804918311197)
  ·
    refine ⟨14682523830349801844366699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39153396880932804918311197 14682523830349801844366699)
    ·
      refine ⟨22023785745524702766550049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14682523830349801844366699 22023785745524702766550049)
      ·
        refine ⟨16517839309143527074912537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22023785745524702766550049 16517839309143527074912537)
        ·
          refine ⟨12388379481857645306184403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16517839309143527074912537 12388379481857645306184403)
          ·
            refine ⟨18582569222786467959276605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12388379481857645306184403 18582569222786467959276605)
            ·
              refine ⟨6968463458544925484728727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18582569222786467959276605 6968463458544925484728727)
              ·
                refine ⟨10452695187817388227093091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968463458544925484728727 10452695187817388227093091)
                ·
                  refine ⟨15679042781726082340639637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10452695187817388227093091 15679042781726082340639637)
                  ·
                    refine ⟨734955130393410109717483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15679042781726082340639637 734955130393410109717483)
                    ·
                      rfl

theorem cell22_2146980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2146980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146980 prefixEnd_2146980 := by exact prefixLift 2146980
  have htrace : WordTrace (prefixWord ++ tailWord_2146980) baseStart_2146980 baseEnd_2146980 := by
    simpa [prefixWord, tailWord_2146980, baseEnd_2146980] using wordTrace_append hprefix tailTrace_2146980
  have hstable : (prefixWord ++ tailWord_2146980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146980).length < 2 ^ (prefixWord ++ tailWord_2146980).sum := by decide
  have hdescent : baseEnd_2146980 < baseStart_2146980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146986 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2146986 : Nat := 118140960795 + 2146986 * 2 ^ 59
def prefixEnd_2146986 : Nat := 4983230072969 + 3 ^ 40 * 2146986 * 2
def baseEnd_2146986 : Nat := 734957184316028094067465

theorem tailTrace_2146986 : CollatzResearch.WordTrace tailWord_2146986 prefixEnd_2146986 734957184316028094067465 := by
  unfold tailWord_2146986
  simp only [CollatzResearch.WordTrace]
  refine ⟨19576753149960968215335203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52204675066562581907560541 19576753149960968215335203)
  ·
    refine ⟨29365129724941452323002805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19576753149960968215335203 29365129724941452323002805)
    ·
      refine ⟨2752980911713261155281513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29365129724941452323002805 2752980911713261155281513)
      ·
        refine ⟨2064735683784945866461135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2752980911713261155281513 2064735683784945866461135)
        ·
          refine ⟨3097103525677418799691703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064735683784945866461135 3097103525677418799691703)
          ·
            refine ⟨4645655288516128199537555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097103525677418799691703 4645655288516128199537555)
            ·
              refine ⟨6968482932774192299306333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645655288516128199537555 6968482932774192299306333)
              ·
                refine ⟨2613181099790322112239875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6968482932774192299306333 2613181099790322112239875)
                ·
                  refine ⟨3919771649685483168359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613181099790322112239875 3919771649685483168359813)
                  ·
                    refine ⟨734957184316028094067465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3919771649685483168359813 734957184316028094067465)
                    ·
                      rfl

theorem cell22_2146986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2146986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2146986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2146986 prefixEnd_2146986 := by exact prefixLift 2146986
  have htrace : WordTrace (prefixWord ++ tailWord_2146986) baseStart_2146986 baseEnd_2146986 := by
    simpa [prefixWord, tailWord_2146986, baseEnd_2146986] using wordTrace_append hprefix tailTrace_2146986
  have hstable : (prefixWord ++ tailWord_2146986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146986).length < 2 ^ (prefixWord ++ tailWord_2146986).sum := by decide
  have hdescent : baseEnd_2146986 < baseStart_2146986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147074 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2147074 : Nat := 118140960795 + 2147074 * 2 ^ 59
def prefixEnd_2147074 : Nat := 4983230072969 + 3 ^ 40 * 2147074 * 2
def baseEnd_2147074 : Nat := 244995769504808399289065

theorem tailTrace_2147074 : CollatzResearch.WordTrace tailWord_2147074 prefixEnd_2147074 244995769504808399289065 := by
  unfold tailWord_2147074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577555555881265972636069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52206814815683375927029517 19577555555881265972636069)
  ·
    refine ⟨3670791666727737369869263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19577555555881265972636069 3670791666727737369869263)
    ·
      refine ⟨5506187500091606054803895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3670791666727737369869263 5506187500091606054803895)
      ·
        refine ⟨8259281250137409082205843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506187500091606054803895 8259281250137409082205843)
        ·
          refine ⟨12388921875206113623308765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259281250137409082205843 12388921875206113623308765)
          ·
            refine ⟨4645845703202292608740787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12388921875206113623308765 4645845703202292608740787)
            ·
              refine ⟨6968768554803438913111181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645845703202292608740787 6968768554803438913111181)
              ·
                refine ⟨2613288208051289592416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6968768554803438913111181 2613288208051289592416693)
                ·
                  refine ⟨244995769504808399289065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2613288208051289592416693 244995769504808399289065)
                  ·
                    rfl

theorem cell22_2147074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2147074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147074 prefixEnd_2147074 := by exact prefixLift 2147074
  have htrace : WordTrace (prefixWord ++ tailWord_2147074) baseStart_2147074 baseEnd_2147074 := by
    simpa [prefixWord, tailWord_2147074, baseEnd_2147074] using wordTrace_append hprefix tailTrace_2147074
  have hstable : (prefixWord ++ tailWord_2147074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147074).length < 2 ^ (prefixWord ++ tailWord_2147074).sum := by decide
  have hdescent : baseEnd_2147074 < baseStart_2147074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147198 : List Nat := [4, 2, 3, 1, 2, 2, 2, 6]
def baseStart_2147198 : Nat := 118140960795 + 2147198 * 2 ^ 59
def prefixEnd_2147198 : Nat := 4983230072969 + 3 ^ 40 * 2147198 * 2
def baseEnd_2147198 : Nat := 81669972916503356418535

theorem tailTrace_2147198 : CollatzResearch.WordTrace tailWord_2147198 prefixEnd_2147198 81669972916503356418535 := by
  unfold tailWord_2147198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789343109384479133507281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52209829916717222045372165 9789343109384479133507281)
  ·
    refine ⟨7342007332038359350130461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9789343109384479133507281 7342007332038359350130461)
    ·
      refine ⟨2753252749514384756298923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7342007332038359350130461 2753252749514384756298923)
      ·
        refine ⟨4129879124271577134448385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753252749514384756298923 4129879124271577134448385)
        ·
          refine ⟨3097409343203682850836289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129879124271577134448385 3097409343203682850836289)
          ·
            refine ⟨2323057007402762138127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097409343203682850836289 2323057007402762138127217)
            ·
              refine ⟨1742292755552071603595413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323057007402762138127217 1742292755552071603595413)
              ·
                refine ⟨81669972916503356418535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1742292755552071603595413 81669972916503356418535)
                ·
                  rfl

theorem cell22_2147198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_2147198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147198 prefixEnd_2147198 := by exact prefixLift 2147198
  have htrace : WordTrace (prefixWord ++ tailWord_2147198) baseStart_2147198 baseEnd_2147198 := by
    simpa [prefixWord, tailWord_2147198, baseEnd_2147198] using wordTrace_append hprefix tailTrace_2147198
  have hstable : (prefixWord ++ tailWord_2147198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147198).length < 2 ^ (prefixWord ++ tailWord_2147198).sum := by decide
  have hdescent : baseEnd_2147198 < baseStart_2147198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147256 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_2147256 : Nat := 118140960795 + 2147256 * 2 ^ 59
def prefixEnd_2147256 : Nat := 4983230072969 + 3 ^ 40 * 2147256 * 2
def baseEnd_2147256 : Nat := 735049610833837389816637

theorem tailTrace_2147256 : CollatzResearch.WordTrace tailWord_2147256 prefixEnd_2147256 735049610833837389816637 := by
  unfold tailWord_2147256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39158430154432854486834811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52211240205910472649113081 39158430154432854486834811)
  ·
    refine ⟨58737645231649281730252217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39158430154432854486834811 58737645231649281730252217)
    ·
      refine ⟨44053233923736961297689163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58737645231649281730252217 44053233923736961297689163)
      ·
        refine ⟨66079850885605441946533745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44053233923736961297689163 66079850885605441946533745)
        ·
          refine ⟨49559888164204081459900309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66079850885605441946533745 49559888164204081459900309)
          ·
            refine ⟨2323119757697066318432827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49559888164204081459900309 2323119757697066318432827)
            ·
              refine ⟨3484679636545599477649241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323119757697066318432827 3484679636545599477649241)
              ·
                refine ⟨2613509727409199608236931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484679636545599477649241 2613509727409199608236931)
                ·
                  refine ⟨3920264591113799412355397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613509727409199608236931 3920264591113799412355397)
                  ·
                    refine ⟨735049610833837389816637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920264591113799412355397 735049610833837389816637)
                    ·
                      rfl

theorem cell22_2147256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_2147256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147256 prefixEnd_2147256 := by exact prefixLift 2147256
  have htrace : WordTrace (prefixWord ++ tailWord_2147256) baseStart_2147256 baseEnd_2147256 := by
    simpa [prefixWord, tailWord_2147256, baseEnd_2147256] using wordTrace_append hprefix tailTrace_2147256
  have hstable : (prefixWord ++ tailWord_2147256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147256).length < 2 ^ (prefixWord ++ tailWord_2147256).sum := by decide
  have hdescent : baseEnd_2147256 < baseStart_2147256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_2147267 : Nat := 118140960795 + 2147267 * 2 ^ 59
def prefixEnd_2147267 : Nat := 4983230072969 + 3 ^ 40 * 2147267 * 2
def baseEnd_2147267 : Nat := 735053376358637027791603

theorem tailTrace_2147267 : CollatzResearch.WordTrace tailWord_2147267 prefixEnd_2147267 735053376358637027791603 := by
  unfold tailWord_2147267
  simp only [CollatzResearch.WordTrace]
  refine ⟨78317261511825857852320055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52211507674550571901546703 78317261511825857852320055)
  ·
    refine ⟨117475892267738786778480083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78317261511825857852320055 117475892267738786778480083)
    ·
      refine ⟨176213838401608180167720125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117475892267738786778480083 176213838401608180167720125)
      ·
        refine ⟨66080189400603067562895047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176213838401608180167720125 66080189400603067562895047)
        ·
          refine ⟨99120284100904601344342571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66080189400603067562895047 99120284100904601344342571)
          ·
            refine ⟨148680426151356902016513857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99120284100904601344342571 148680426151356902016513857)
            ·
              refine ⟨111510319613517676512385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148680426151356902016513857 111510319613517676512385393)
              ·
                refine ⟨83632739710138257384289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111510319613517676512385393 83632739710138257384289045)
                ·
                  refine ⟨3920284673912730814888549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83632739710138257384289045 3920284673912730814888549)
                  ·
                    refine ⟨735053376358637027791603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920284673912730814888549 735053376358637027791603)
                    ·
                      rfl

theorem cell22_2147267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_2147267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147267 prefixEnd_2147267 := by exact prefixLift 2147267
  have htrace : WordTrace (prefixWord ++ tailWord_2147267) baseStart_2147267 baseEnd_2147267 := by
    simpa [prefixWord, tailWord_2147267, baseEnd_2147267] using wordTrace_append hprefix tailTrace_2147267
  have hstable : (prefixWord ++ tailWord_2147267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147267).length < 2 ^ (prefixWord ++ tailWord_2147267).sum := by decide
  have hdescent : baseEnd_2147267 < baseStart_2147267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147288 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_2147288 : Nat := 118140960795 + 2147288 * 2 ^ 59
def prefixEnd_2147288 : Nat := 4983230072969 + 3 ^ 40 * 2147288 * 2
def baseEnd_2147288 : Nat := 245020188362599991005513

theorem tailTrace_2147288 : CollatzResearch.WordTrace tailWord_2147288 prefixEnd_2147288 245020188362599991005513 := by
  unfold tailWord_2147288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39159013722374889219417259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52212018296499852292556345 39159013722374889219417259)
  ·
    refine ⟨58738520583562333829125889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39159013722374889219417259 58738520583562333829125889)
    ·
      refine ⟨44053890437671750371844417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58738520583562333829125889 44053890437671750371844417)
      ·
        refine ⟨33040417828253812778883313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44053890437671750371844417 33040417828253812778883313)
        ·
          refine ⟨24780313371190359584162485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33040417828253812778883313 24780313371190359584162485)
          ·
            refine ⟨2323154378549096211015233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24780313371190359584162485 2323154378549096211015233)
            ·
              refine ⟨1742365783911822158261425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323154378549096211015233 1742365783911822158261425)
              ·
                refine ⟨1306774337933866618696069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742365783911822158261425 1306774337933866618696069)
                ·
                  refine ⟨245020188362599991005513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306774337933866618696069 245020188362599991005513)
                  ·
                    rfl

theorem cell22_2147288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_2147288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147288 prefixEnd_2147288 := by exact prefixLift 2147288
  have htrace : WordTrace (prefixWord ++ tailWord_2147288) baseStart_2147288 baseEnd_2147288 := by
    simpa [prefixWord, tailWord_2147288, baseEnd_2147288] using wordTrace_append hprefix tailTrace_2147288
  have hstable : (prefixWord ++ tailWord_2147288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147288).length < 2 ^ (prefixWord ++ tailWord_2147288).sum := by decide
  have hdescent : baseEnd_2147288 < baseStart_2147288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147297 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2147297 : Nat := 118140960795 + 2147297 * 2 ^ 59
def prefixEnd_2147297 : Nat := 4983230072969 + 3 ^ 40 * 2147297 * 2
def baseEnd_2147297 : Nat := 735063645971726949541511

theorem tailTrace_2147297 : CollatzResearch.WordTrace tailWord_2147297 prefixEnd_2147297 735063645971726949541511 := by
  unfold tailWord_2147297
  simp only [CollatzResearch.WordTrace]
  refine ⟨78318355701717172975912145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52212237134478115317274763 78318355701717172975912145)
  ·
    refine ⟨58738766776287879731934109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78318355701717172975912145 58738766776287879731934109)
    ·
      refine ⟨22027037541107954899475291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58738766776287879731934109 22027037541107954899475291)
      ·
        refine ⟨33040556311661932349212937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22027037541107954899475291 33040556311661932349212937)
        ·
          refine ⟨24780417233746449261909703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33040556311661932349212937 24780417233746449261909703)
          ·
            refine ⟨37170625850619673892864555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24780417233746449261909703 37170625850619673892864555)
            ·
              refine ⟨55755938775929510839296833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37170625850619673892864555 55755938775929510839296833)
              ·
                refine ⟨41816954081947133129472625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55755938775929510839296833 41816954081947133129472625)
                ·
                  refine ⟨31362715561460349847104469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41816954081947133129472625 31362715561460349847104469)
                  ·
                    refine ⟨735063645971726949541511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31362715561460349847104469 735063645971726949541511)
                    ·
                      rfl

theorem cell22_2147297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2147297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147297 prefixEnd_2147297 := by exact prefixLift 2147297
  have htrace : WordTrace (prefixWord ++ tailWord_2147297) baseStart_2147297 baseEnd_2147297 := by
    simpa [prefixWord, tailWord_2147297, baseEnd_2147297] using wordTrace_append hprefix tailTrace_2147297
  have hstable : (prefixWord ++ tailWord_2147297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147297).length < 2 ^ (prefixWord ++ tailWord_2147297).sum := by decide
  have hdescent : baseEnd_2147297 < baseStart_2147297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147312 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_2147312 : Nat := 118140960795 + 2147312 * 2 ^ 59
def prefixEnd_2147312 : Nat := 4983230072969 + 3 ^ 40 * 2147312 * 2
def baseEnd_2147312 : Nat := 735068780778271910416465

theorem tailTrace_2147312 : CollatzResearch.WordTrace tailWord_2147312 prefixEnd_2147312 735068780778271910416465 := by
  unfold tailWord_2147312
  simp only [CollatzResearch.WordTrace]
  refine ⟨39159451398331415268854095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52212601864441887025138793 39159451398331415268854095)
  ·
    refine ⟨58739177097497122903281143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39159451398331415268854095 58739177097497122903281143)
    ·
      refine ⟨88108765646245684354921715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58739177097497122903281143 88108765646245684354921715)
      ·
        refine ⟨132163148469368526532382573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88108765646245684354921715 132163148469368526532382573)
        ·
          refine ⟨49561180676013197449643465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132163148469368526532382573 49561180676013197449643465)
          ·
            refine ⟨37170885507009898087232599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49561180676013197449643465 37170885507009898087232599)
            ·
              refine ⟨55756328260514847130848899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37170885507009898087232599 55756328260514847130848899)
              ·
                refine ⟨83634492390772270696273349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55756328260514847130848899 83634492390772270696273349)
                ·
                  refine ⟨15681467323269800755551253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83634492390772270696273349 15681467323269800755551253)
                  ·
                    refine ⟨735068780778271910416465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15681467323269800755551253 735068780778271910416465)
                    ·
                      rfl

theorem cell22_2147312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_2147312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147312 prefixEnd_2147312 := by exact prefixLift 2147312
  have htrace : WordTrace (prefixWord ++ tailWord_2147312) baseStart_2147312 baseEnd_2147312 := by
    simpa [prefixWord, tailWord_2147312, baseEnd_2147312] using wordTrace_append hprefix tailTrace_2147312
  have hstable : (prefixWord ++ tailWord_2147312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147312).length < 2 ^ (prefixWord ++ tailWord_2147312).sum := by decide
  have hdescent : baseEnd_2147312 < baseStart_2147312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147318 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2147318 : Nat := 118140960795 + 2147318 * 2 ^ 59
def prefixEnd_2147318 : Nat := 4983230072969 + 3 ^ 40 * 2147318 * 2
def baseEnd_2147318 : Nat := 735070834700889894766447

theorem tailTrace_2147318 : CollatzResearch.WordTrace tailWord_2147318 prefixEnd_2147318 735070834700889894766447 := by
  unfold tailWord_2147318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894945102165068347651663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52212747756427395708284405 4894945102165068347651663)
  ·
    refine ⟨7342417653247602521477495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4894945102165068347651663 7342417653247602521477495)
    ·
      refine ⟨11013626479871403782216243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342417653247602521477495 11013626479871403782216243)
      ·
        refine ⟨16520439719807105673324365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013626479871403782216243 16520439719807105673324365)
        ·
          refine ⟨6195164894927664627496637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16520439719807105673324365 6195164894927664627496637)
          ·
            refine ⟨2323186835597874235311239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6195164894927664627496637 2323186835597874235311239)
            ·
              refine ⟨3484780253396811352966859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323186835597874235311239 3484780253396811352966859)
              ·
                refine ⟨5227170380095217029450289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484780253396811352966859 5227170380095217029450289)
                ·
                  refine ⟨3920377785071412772087717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5227170380095217029450289 3920377785071412772087717)
                  ·
                    refine ⟨735070834700889894766447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920377785071412772087717 735070834700889894766447)
                    ·
                      rfl

theorem cell22_2147318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2147318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147318 prefixEnd_2147318 := by exact prefixLift 2147318
  have htrace : WordTrace (prefixWord ++ tailWord_2147318) baseStart_2147318 baseEnd_2147318 := by
    simpa [prefixWord, tailWord_2147318, baseEnd_2147318] using wordTrace_append hprefix tailTrace_2147318
  have hstable : (prefixWord ++ tailWord_2147318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147318).length < 2 ^ (prefixWord ++ tailWord_2147318).sum := by decide
  have hdescent : baseEnd_2147318 < baseStart_2147318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147359 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_2147359 : Nat := 118140960795 + 2147359 * 2 ^ 59
def prefixEnd_2147359 : Nat := 4983230072969 + 3 ^ 40 * 2147359 * 2
def baseEnd_2147359 : Nat := 735084869838779454491321

theorem tailTrace_2147359 : CollatzResearch.WordTrace tailWord_2147359 prefixEnd_2147359 735084869838779454491321 := by
  unfold tailWord_2147359
  simp only [CollatzResearch.WordTrace]
  refine ⟨78320617027492557564669131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52213744684995038376446087 78320617027492557564669131)
  ·
    refine ⟨117480925541238836347003697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78320617027492557564669131 117480925541238836347003697)
    ·
      refine ⟨88110694155929127260252773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117480925541238836347003697 88110694155929127260252773)
      ·
        refine ⟨16520755154236711361297395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88110694155929127260252773 16520755154236711361297395)
        ·
          refine ⟨24781132731355067041946093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16520755154236711361297395 24781132731355067041946093)
          ·
            refine ⟨9292924774258150140729785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24781132731355067041946093 9292924774258150140729785)
            ·
              refine ⟨6969693580693612605547339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9292924774258150140729785 6969693580693612605547339)
              ·
                refine ⟨10454540371040418908321009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6969693580693612605547339 10454540371040418908321009)
                ·
                  refine ⟨7840905278280314181240757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10454540371040418908321009 7840905278280314181240757)
                  ·
                    refine ⟨735084869838779454491321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7840905278280314181240757 735084869838779454491321)
                    ·
                      rfl

theorem cell22_2147359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_2147359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147359 prefixEnd_2147359 := by exact prefixLift 2147359
  have htrace : WordTrace (prefixWord ++ tailWord_2147359) baseStart_2147359 baseEnd_2147359 := by
    simpa [prefixWord, tailWord_2147359, baseEnd_2147359] using wordTrace_append hprefix tailTrace_2147359
  have hstable : (prefixWord ++ tailWord_2147359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147359).length < 2 ^ (prefixWord ++ tailWord_2147359).sum := by decide
  have hdescent : baseEnd_2147359 < baseStart_2147359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147382 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2147382 : Nat := 118140960795 + 2147382 * 2 ^ 59
def prefixEnd_2147382 : Nat := 4983230072969 + 3 ^ 40 * 2147382 * 2
def baseEnd_2147382 : Nat := 735092743208815061166251

theorem tailTrace_2147382 : CollatzResearch.WordTrace tailWord_2147382 prefixEnd_2147382 735092743208815061166251 := by
  unfold tailWord_2147382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895090994150577030797275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52214303937606154995170933 4895090994150577030797275)
  ·
    refine ⟨7342636491225865546195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895090994150577030797275 7342636491225865546195913)
    ·
      refine ⟨5506977368419399159646935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7342636491225865546195913 5506977368419399159646935)
      ·
        refine ⟨8260466052629098739470403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5506977368419399159646935 8260466052629098739470403)
        ·
          refine ⟨12390699078943648109205605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8260466052629098739470403 12390699078943648109205605)
          ·
            refine ⟨2323256077301934020476051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12390699078943648109205605 2323256077301934020476051)
            ·
              refine ⟨3484884115952901030714077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323256077301934020476051 3484884115952901030714077)
              ·
                refine ⟨1306831543482337886517779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3484884115952901030714077 1306831543482337886517779)
                ·
                  refine ⟨1960247315223506829776669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306831543482337886517779 1960247315223506829776669)
                  ·
                    refine ⟨735092743208815061166251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1960247315223506829776669 735092743208815061166251)
                    ·
                      rfl

theorem cell22_2147382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2147382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147382 prefixEnd_2147382 := by exact prefixLift 2147382
  have htrace : WordTrace (prefixWord ++ tailWord_2147382) baseStart_2147382 baseEnd_2147382 := by
    simpa [prefixWord, tailWord_2147382, baseEnd_2147382] using wordTrace_append hprefix tailTrace_2147382
  have hstable : (prefixWord ++ tailWord_2147382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147382).length < 2 ^ (prefixWord ++ tailWord_2147382).sum := by decide
  have hdescent : baseEnd_2147382 < baseStart_2147382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147436 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_2147436 : Nat := 118140960795 + 2147436 * 2 ^ 59
def prefixEnd_2147436 : Nat := 4983230072969 + 3 ^ 40 * 2147436 * 2
def baseEnd_2147436 : Nat := 735111228512376920316085

theorem tailTrace_2147436 : CollatzResearch.WordTrace tailWord_2147436 prefixEnd_2147436 735111228512376920316085 := by
  unfold tailWord_2147436
  simp only [CollatzResearch.WordTrace]
  refine ⟨39161712724106799857611081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52215616965475733143481441 39161712724106799857611081)
  ·
    refine ⟨29371284543080099893208311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39161712724106799857611081 29371284543080099893208311)
    ·
      refine ⟨44056926814620149839812467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29371284543080099893208311 44056926814620149839812467)
      ·
        refine ⟨66085390221930224759718701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44056926814620149839812467 66085390221930224759718701)
        ·
          refine ⟨24782021333223834284894513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66085390221930224759718701 24782021333223834284894513)
          ·
            refine ⟨18586515999917875713670885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24782021333223834284894513 18586515999917875713670885)
            ·
              refine ⟨3484971749984601696313291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18586515999917875713670885 3484971749984601696313291)
              ·
                refine ⟨5227457624976902544469937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484971749984601696313291 5227457624976902544469937)
                ·
                  refine ⟨3920593218732676908352453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5227457624976902544469937 3920593218732676908352453)
                  ·
                    refine ⟨735111228512376920316085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920593218732676908352453 735111228512376920316085)
                    ·
                      rfl

theorem cell22_2147436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_2147436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147436 prefixEnd_2147436 := by exact prefixLift 2147436
  have htrace : WordTrace (prefixWord ++ tailWord_2147436) baseStart_2147436 baseEnd_2147436 := by
    simpa [prefixWord, tailWord_2147436, baseEnd_2147436] using wordTrace_append hprefix tailTrace_2147436
  have hstable : (prefixWord ++ tailWord_2147436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147436).length < 2 ^ (prefixWord ++ tailWord_2147436).sum := by decide
  have hdescent : baseEnd_2147436 < baseStart_2147436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147513 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 5]
def baseStart_2147513 : Nat := 118140960795 + 2147513 * 2 ^ 59
def prefixEnd_2147513 : Nat := 4983230072969 + 3 ^ 40 * 2147513 * 2
def baseEnd_2147513 : Nat := 245045862395324795380283

theorem tailTrace_2147513 : CollatzResearch.WordTrace tailWord_2147513 prefixEnd_2147513 245045862395324795380283 := by
  unfold tailWord_2147513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78326233868934641865775193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52217489245956427910516795 78326233868934641865775193)
  ·
    refine ⟨58744675401700981399331395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78326233868934641865775193 58744675401700981399331395)
    ·
      refine ⟨88117013102551472098997093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58744675401700981399331395 88117013102551472098997093)
      ·
        refine ⟨16521939956728401018561955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88117013102551472098997093 16521939956728401018561955)
        ·
          refine ⟨24782909935092601527842933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16521939956728401018561955 24782909935092601527842933)
          ·
            refine ⟨2323397806414931393235275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24782909935092601527842933 2323397806414931393235275)
            ·
              refine ⟨3485096709622397089852913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323397806414931393235275 3485096709622397089852913)
              ·
                refine ⟨2613822532216797817389685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3485096709622397089852913 2613822532216797817389685)
                ·
                  refine ⟨245045862395324795380283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2613822532216797817389685 245045862395324795380283)
                  ·
                    rfl

theorem cell22_2147513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_2147513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147513 prefixEnd_2147513 := by exact prefixLift 2147513
  have htrace : WordTrace (prefixWord ++ tailWord_2147513) baseStart_2147513 baseEnd_2147513 := by
    simpa [prefixWord, tailWord_2147513, baseEnd_2147513] using wordTrace_append hprefix tailTrace_2147513
  have hstable : (prefixWord ++ tailWord_2147513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147513).length < 2 ^ (prefixWord ++ tailWord_2147513).sum := by decide
  have hdescent : baseEnd_2147513 < baseStart_2147513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147556 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2147556 : Nat := 118140960795 + 2147556 * 2 ^ 59
def prefixEnd_2147556 : Nat := 4983230072969 + 3 ^ 40 * 2147556 * 2
def baseEnd_2147556 : Nat := 735152306964736607315717

theorem tailTrace_2147556 : CollatzResearch.WordTrace tailWord_2147556 prefixEnd_2147556 735152306964736607315717 := by
  unfold tailWord_2147556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39163901103889430104795261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52218534805185906806393681 39163901103889430104795261)
  ·
    refine ⟨14686462913958536289298223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39163901103889430104795261 14686462913958536289298223)
    ·
      refine ⟨22029694370937804433947335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14686462913958536289298223 22029694370937804433947335)
      ·
        refine ⟨33044541556406706650921003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22029694370937804433947335 33044541556406706650921003)
        ·
          refine ⟨49566812334610059976381505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33044541556406706650921003 49566812334610059976381505)
          ·
            refine ⟨37175109250957544982286129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49566812334610059976381505 37175109250957544982286129)
            ·
              refine ⟨27881331938218158736714597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37175109250957544982286129 27881331938218158736714597)
              ·
                refine ⟨5227749738415904763133987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27881331938218158736714597 5227749738415904763133987)
                ·
                  refine ⟨7841624607623857144700981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5227749738415904763133987 7841624607623857144700981)
                  ·
                    refine ⟨735152306964736607315717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7841624607623857144700981 735152306964736607315717)
                    ·
                      rfl

theorem cell22_2147556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2147556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147556 prefixEnd_2147556 := by exact prefixLift 2147556
  have htrace : WordTrace (prefixWord ++ tailWord_2147556) baseStart_2147556 baseEnd_2147556 := by
    simpa [prefixWord, tailWord_2147556, baseEnd_2147556] using wordTrace_append hprefix tailTrace_2147556
  have hstable : (prefixWord ++ tailWord_2147556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147556).length < 2 ^ (prefixWord ++ tailWord_2147556).sum := by decide
  have hdescent : baseEnd_2147556 < baseStart_2147556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147571 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_2147571 : Nat := 118140960795 + 2147571 * 2 ^ 59
def prefixEnd_2147571 : Nat := 4983230072969 + 3 ^ 40 * 2147571 * 2
def baseEnd_2147571 : Nat := 735157441771281568190671

theorem tailTrace_2147571 : CollatzResearch.WordTrace tailWord_2147571 prefixEnd_2147571 735157441771281568190671 := by
  unfold tailWord_2147571
  simp only [CollatzResearch.WordTrace]
  refine ⟨78328349302724517771386567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52218899535149678514257711 78328349302724517771386567)
  ·
    refine ⟨117492523954086776657079851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78328349302724517771386567 117492523954086776657079851)
    ·
      refine ⟨176238785931130164985619777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117492523954086776657079851 176238785931130164985619777)
      ·
        refine ⟨132179089448347623739214833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176238785931130164985619777 132179089448347623739214833)
        ·
          refine ⟨99134317086260717804411125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132179089448347623739214833 99134317086260717804411125)
          ·
            refine ⟨9293842226836942294163543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99134317086260717804411125 9293842226836942294163543)
            ·
              refine ⟨13940763340255413441245315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9293842226836942294163543 13940763340255413441245315)
              ·
                refine ⟨20911145010383120161867973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13940763340255413441245315 20911145010383120161867973)
                ·
                  refine ⟨3920839689446835030350245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20911145010383120161867973 3920839689446835030350245)
                  ·
                    refine ⟨735157441771281568190671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3920839689446835030350245 735157441771281568190671)
                    ·
                      rfl

theorem cell22_2147571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_2147571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147571 prefixEnd_2147571 := by exact prefixLift 2147571
  have htrace : WordTrace (prefixWord ++ tailWord_2147571) baseStart_2147571 baseEnd_2147571 := by
    simpa [prefixWord, tailWord_2147571, baseEnd_2147571] using wordTrace_append hprefix tailTrace_2147571
  have hstable : (prefixWord ++ tailWord_2147571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147571).length < 2 ^ (prefixWord ++ tailWord_2147571).sum := by decide
  have hdescent : baseEnd_2147571 < baseStart_2147571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147652 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2147652 : Nat := 118140960795 + 2147652 * 2 ^ 59
def prefixEnd_2147652 : Nat := 4983230072969 + 3 ^ 40 * 2147652 * 2
def baseEnd_2147652 : Nat := 735185169726624356915423

theorem tailTrace_2147652 : CollatzResearch.WordTrace tailWord_2147652 prefixEnd_2147652 735185169726624356915423 := by
  unfold tailWord_2147652
  simp only [CollatzResearch.WordTrace]
  refine ⟨39165651807715534302542605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52220869076954045736723473 39165651807715534302542605)
  ·
    refine ⟨14687119427893325363453477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39165651807715534302542605 14687119427893325363453477)
    ·
      refine ⟨2753834892729998505647527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14687119427893325363453477 2753834892729998505647527)
      ·
        refine ⟨4130752339094997758471291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753834892729998505647527 4130752339094997758471291)
        ·
          refine ⟨6196128508642496637706937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130752339094997758471291 6196128508642496637706937)
          ·
            refine ⟨4647096381481872478280203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196128508642496637706937 4647096381481872478280203)
            ·
              refine ⟨6970644572222808717420305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647096381481872478280203 6970644572222808717420305)
              ·
                refine ⟨5227983429167106538065229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6970644572222808717420305 5227983429167106538065229)
                ·
                  refine ⟨1960493785937664951774461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5227983429167106538065229 1960493785937664951774461)
                  ·
                    refine ⟨735185169726624356915423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1960493785937664951774461 735185169726624356915423)
                    ·
                      rfl

theorem cell22_2147652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2147652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147652 prefixEnd_2147652 := by exact prefixLift 2147652
  have htrace : WordTrace (prefixWord ++ tailWord_2147652) baseStart_2147652 baseEnd_2147652 := by
    simpa [prefixWord, tailWord_2147652, baseEnd_2147652] using wordTrace_append hprefix tailTrace_2147652
  have hstable : (prefixWord ++ tailWord_2147652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147652).length < 2 ^ (prefixWord ++ tailWord_2147652).sum := by decide
  have hdescent : baseEnd_2147652 < baseStart_2147652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147654 : List Nat := [6, 1, 1, 3, 1, 1, 3, 6]
def baseStart_2147654 : Nat := 118140960795 + 2147654 * 2 ^ 59
def prefixEnd_2147654 : Nat := 4983230072969 + 3 ^ 40 * 2147654 * 2
def baseEnd_2147654 : Nat := 81687317151944113151713

theorem tailTrace_2147654 : CollatzResearch.WordTrace tailWord_2147654 prefixEnd_2147654 81687317151944113151713 := by
  unfold tailWord_2147654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447855517544494467083063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52220917707615881964438677 2447855517544494467083063)
  ·
    refine ⟨3671783276316741700624595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447855517544494467083063 3671783276316741700624595)
    ·
      refine ⟨5507674914475112550936893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3671783276316741700624595 5507674914475112550936893)
      ·
        refine ⟨2065378092928167206601335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5507674914475112550936893 2065378092928167206601335)
        ·
          refine ⟨3098067139392250809902003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065378092928167206601335 3098067139392250809902003)
          ·
            refine ⟨4647100709088376214853005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098067139392250809902003 4647100709088376214853005)
            ·
              refine ⟨1742662765908141080569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4647100709088376214853005 1742662765908141080569877)
              ·
                refine ⟨81687317151944113151713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1742662765908141080569877 81687317151944113151713)
                ·
                  rfl

theorem cell22_2147654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_2147654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147654 prefixEnd_2147654 := by exact prefixLift 2147654
  have htrace : WordTrace (prefixWord ++ tailWord_2147654) baseStart_2147654 baseEnd_2147654 := by
    simpa [prefixWord, tailWord_2147654, baseEnd_2147654] using wordTrace_append hprefix tailTrace_2147654
  have hstable : (prefixWord ++ tailWord_2147654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147654).length < 2 ^ (prefixWord ++ tailWord_2147654).sum := by decide
  have hdescent : baseEnd_2147654 < baseStart_2147654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147693 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2147693 : Nat := 118140960795 + 2147693 * 2 ^ 59
def prefixEnd_2147693 : Nat := 4983230072969 + 3 ^ 40 * 2147693 * 2
def baseEnd_2147693 : Nat := 245066401621504638880099

theorem tailTrace_2147693 : CollatzResearch.WordTrace tailWord_2147693 prefixEnd_2147693 245066401621504638880099 := by
  unfold tailWord_2147693
  simp only [CollatzResearch.WordTrace]
  refine ⟨78332799008282532607327733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52221866005521688404885155 78332799008282532607327733)
  ·
    refine ⟨7343699907026487431936975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78332799008282532607327733 7343699907026487431936975)
    ·
      refine ⟨11015549860539731147905463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343699907026487431936975 11015549860539731147905463)
      ·
        refine ⟨16523324790809596721858195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11015549860539731147905463 16523324790809596721858195)
        ·
          refine ⟨24784987186214395082787293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16523324790809596721858195 24784987186214395082787293)
          ·
            refine ⟨9294370194830398156045235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24784987186214395082787293 9294370194830398156045235)
            ·
              refine ⟨13941555292245597234067853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294370194830398156045235 13941555292245597234067853)
              ·
                refine ⟨5228083234592098962775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13941555292245597234067853 5228083234592098962775445)
                ·
                  refine ⟨245066401621504638880099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5228083234592098962775445 245066401621504638880099)
                  ·
                    rfl

theorem cell22_2147693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2147693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147693 prefixEnd_2147693 := by exact prefixLift 2147693
  have htrace : WordTrace (prefixWord ++ tailWord_2147693) baseStart_2147693 baseEnd_2147693 := by
    simpa [prefixWord, tailWord_2147693, baseEnd_2147693] using wordTrace_append hprefix tailTrace_2147693
  have hstable : (prefixWord ++ tailWord_2147693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147693).length < 2 ^ (prefixWord ++ tailWord_2147693).sum := by decide
  have hdescent : baseEnd_2147693 < baseStart_2147693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147723 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_2147723 : Nat := 118140960795 + 2147723 * 2 ^ 59
def prefixEnd_2147723 : Nat := 4983230072969 + 3 ^ 40 * 2147723 * 2
def baseEnd_2147723 : Nat := 735209474477603838390205

theorem tailTrace_2147723 : CollatzResearch.WordTrace tailWord_2147723 prefixEnd_2147723 735209474477603838390205 := by
  unfold tailWord_2147723
  simp only [CollatzResearch.WordTrace]
  refine ⟨78333893198173847730919823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52222595465449231820613215 78333893198173847730919823)
  ·
    refine ⟨117500839797260771596379735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78333893198173847730919823 117500839797260771596379735)
    ·
      refine ⟨176251259695891157394569603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117500839797260771596379735 176251259695891157394569603)
      ·
        refine ⟨264376889543836736091854405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176251259695891157394569603 264376889543836736091854405)
        ·
          refine ⟨49570666789469388017222701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264376889543836736091854405 49570666789469388017222701)
          ·
            refine ⟨18589000046051020506458513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49570666789469388017222701 18589000046051020506458513)
            ·
              refine ⟨13941750034538265379843885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18589000046051020506458513 13941750034538265379843885)
              ·
                refine ⟨5228156262951849517441457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13941750034538265379843885 5228156262951849517441457)
                ·
                  refine ⟨3921117197213887138081093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5228156262951849517441457 3921117197213887138081093)
                  ·
                    refine ⟨735209474477603838390205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921117197213887138081093 735209474477603838390205)
                    ·
                      rfl

theorem cell22_2147723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_2147723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147723 prefixEnd_2147723 := by exact prefixLift 2147723
  have htrace : WordTrace (prefixWord ++ tailWord_2147723) baseStart_2147723 baseEnd_2147723 := by
    simpa [prefixWord, tailWord_2147723, baseEnd_2147723] using wordTrace_append hprefix tailTrace_2147723
  have hstable : (prefixWord ++ tailWord_2147723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147723).length < 2 ^ (prefixWord ++ tailWord_2147723).sum := by decide
  have hdescent : baseEnd_2147723 < baseStart_2147723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147815 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2147815 : Nat := 118140960795 + 2147815 * 2 ^ 59
def prefixEnd_2147815 : Nat := 4983230072969 + 3 ^ 40 * 2147815 * 2
def baseEnd_2147815 : Nat := 735240967957746265089923

theorem tailTrace_2147815 : CollatzResearch.WordTrace tailWord_2147815 prefixEnd_2147815 735240967957746265089923 := by
  unfold tailWord_2147815
  simp only [CollatzResearch.WordTrace]
  refine ⟨78337248713840547443268899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52224832475893698295512599 78337248713840547443268899)
  ·
    refine ⟨117505873070760821164903349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78337248713840547443268899 117505873070760821164903349)
    ·
      refine ⟨11016175600383826984209689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117505873070760821164903349 11016175600383826984209689)
      ·
        refine ⟨8262131700287870238157267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11016175600383826984209689 8262131700287870238157267)
        ·
          refine ⟨12393197550431805357235901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262131700287870238157267 12393197550431805357235901)
          ·
            refine ⟨4647449081411927008963463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12393197550431805357235901 4647449081411927008963463)
            ·
              refine ⟨6971173622117890513445195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647449081411927008963463 6971173622117890513445195)
              ·
                refine ⟨10456760433176835770167793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6971173622117890513445195 10456760433176835770167793)
                ·
                  refine ⟨7842570324882626827625845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10456760433176835770167793 7842570324882626827625845)
                  ·
                    refine ⟨735240967957746265089923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7842570324882626827625845 735240967957746265089923)
                    ·
                      rfl

theorem cell22_2147815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2147815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147815 prefixEnd_2147815 := by exact prefixLift 2147815
  have htrace : WordTrace (prefixWord ++ tailWord_2147815) baseStart_2147815 baseEnd_2147815 := by
    simpa [prefixWord, tailWord_2147815, baseEnd_2147815] using wordTrace_append hprefix tailTrace_2147815
  have hstable : (prefixWord ++ tailWord_2147815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147815).length < 2 ^ (prefixWord ++ tailWord_2147815).sum := by decide
  have hdescent : baseEnd_2147815 < baseStart_2147815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147838 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2147838 : Nat := 118140960795 + 2147838 * 2 ^ 59
def prefixEnd_2147838 : Nat := 4983230072969 + 3 ^ 40 * 2147838 * 2
def baseEnd_2147838 : Nat := 735248841327781871764853

theorem tailTrace_2147838 : CollatzResearch.WordTrace tailWord_2147838 prefixEnd_2147838 735248841327781871764853 := by
  unfold tailWord_2147838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9792260949094652796419521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52225391728504814914237445 9792260949094652796419521)
  ·
    refine ⟨7344195711820989597314641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9792260949094652796419521 7344195711820989597314641)
    ·
      refine ⟨5508146783865742197985981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344195711820989597314641 5508146783865742197985981)
      ·
        refine ⟨2065555043949653324244743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5508146783865742197985981 2065555043949653324244743)
        ·
          refine ⟨3098332565924479986367115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065555043949653324244743 3098332565924479986367115)
          ·
            refine ⟨4647498848886719979550673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098332565924479986367115 4647498848886719979550673)
            ·
              refine ⟨3485624136665039984663005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4647498848886719979550673 3485624136665039984663005)
              ·
                refine ⟨1307109051249389994248627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485624136665039984663005 1307109051249389994248627)
                ·
                  refine ⟨1960663576874084991372941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307109051249389994248627 1960663576874084991372941)
                  ·
                    refine ⟨735248841327781871764853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1960663576874084991372941 735248841327781871764853)
                    ·
                      rfl

theorem cell22_2147838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2147838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147838 prefixEnd_2147838 := by exact prefixLift 2147838
  have htrace : WordTrace (prefixWord ++ tailWord_2147838) baseStart_2147838 baseEnd_2147838 := by
    simpa [prefixWord, tailWord_2147838, baseEnd_2147838] using wordTrace_append hprefix tailTrace_2147838
  have hstable : (prefixWord ++ tailWord_2147838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147838).length < 2 ^ (prefixWord ++ tailWord_2147838).sum := by decide
  have hdescent : baseEnd_2147838 < baseStart_2147838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147843 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_2147843 : Nat := 118140960795 + 2147843 * 2 ^ 59
def prefixEnd_2147843 : Nat := 4983230072969 + 3 ^ 40 * 2147843 * 2
def baseEnd_2147843 : Nat := 735250552929963525389837

theorem tailTrace_2147843 : CollatzResearch.WordTrace tailWord_2147843 prefixEnd_2147843 735250552929963525389837 := by
  unfold tailWord_2147843
  simp only [CollatzResearch.WordTrace]
  refine ⟨78338269957739108225288183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52225513305159405483525455 78338269957739108225288183)
  ·
    refine ⟨117507404936608662337932275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78338269957739108225288183 117507404936608662337932275)
    ·
      refine ⟨176261107404912993506898413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117507404936608662337932275 176261107404912993506898413)
      ·
        refine ⟨66097915276842372565086905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176261107404912993506898413 66097915276842372565086905)
        ·
          refine ⟨49573436457631779423815179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66097915276842372565086905 49573436457631779423815179)
          ·
            refine ⟨74360154686447669135722769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49573436457631779423815179 74360154686447669135722769)
            ·
              refine ⟨55770116014835751851792077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74360154686447669135722769 55770116014835751851792077)
              ·
                refine ⟨20913793505563406944422029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55770116014835751851792077 20913793505563406944422029)
                ·
                  refine ⟨7842672564586277604158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20913793505563406944422029 7842672564586277604158261)
                  ·
                    refine ⟨735250552929963525389837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7842672564586277604158261 735250552929963525389837)
                    ·
                      rfl

theorem cell22_2147843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_2147843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147843 prefixEnd_2147843 := by exact prefixLift 2147843
  have htrace : WordTrace (prefixWord ++ tailWord_2147843) baseStart_2147843 baseEnd_2147843 := by
    simpa [prefixWord, tailWord_2147843, baseEnd_2147843] using wordTrace_append hprefix tailTrace_2147843
  have hstable : (prefixWord ++ tailWord_2147843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147843).length < 2 ^ (prefixWord ++ tailWord_2147843).sum := by decide
  have hdescent : baseEnd_2147843 < baseStart_2147843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147847 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2147847 : Nat := 118140960795 + 2147847 * 2 ^ 59
def prefixEnd_2147847 : Nat := 4983230072969 + 3 ^ 40 * 2147847 * 2
def baseEnd_2147847 : Nat := 735251922211708848289825

theorem tailTrace_2147847 : CollatzResearch.WordTrace tailWord_2147847 prefixEnd_2147847 735251922211708848289825 := by
  unfold tailWord_2147847
  simp only [CollatzResearch.WordTrace]
  refine ⟨78338415849724616908433795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52225610566483077938955863 78338415849724616908433795)
  ·
    refine ⟨117507623774586925362650693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78338415849724616908433795 117507623774586925362650693)
    ·
      refine ⟨22032679457735048505497005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117507623774586925362650693 22032679457735048505497005)
      ·
        refine ⟨8262254796650643189561377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22032679457735048505497005 8262254796650643189561377)
        ·
          refine ⟨6196691097487982392171033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8262254796650643189561377 6196691097487982392171033)
          ·
            refine ⟨4647518323115986794128275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6196691097487982392171033 4647518323115986794128275)
            ·
              refine ⟨6971277484673980191192413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4647518323115986794128275 6971277484673980191192413)
              ·
                refine ⟨2614229056752742571697155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6971277484673980191192413 2614229056752742571697155)
                ·
                  refine ⟨3921343585129113857545733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2614229056752742571697155 3921343585129113857545733)
                  ·
                    refine ⟨735251922211708848289825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921343585129113857545733 735251922211708848289825)
                    ·
                      rfl

theorem cell22_2147847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2147847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147847 prefixEnd_2147847 := by exact prefixLift 2147847
  have htrace : WordTrace (prefixWord ++ tailWord_2147847) baseStart_2147847 baseEnd_2147847 := by
    simpa [prefixWord, tailWord_2147847, baseEnd_2147847] using wordTrace_append hprefix tailTrace_2147847
  have hstable : (prefixWord ++ tailWord_2147847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147847).length < 2 ^ (prefixWord ++ tailWord_2147847).sum := by decide
  have hdescent : baseEnd_2147847 < baseStart_2147847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147888 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_2147888 : Nat := 118140960795 + 2147888 * 2 ^ 59
def prefixEnd_2147888 : Nat := 4983230072969 + 3 ^ 40 * 2147888 * 2
def baseEnd_2147888 : Nat := 735265957349598408014699

theorem tailTrace_2147888 : CollatzResearch.WordTrace tailWord_2147888 prefixEnd_2147888 735265957349598408014699 := by
  unfold tailWord_2147888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39169955621288040455338159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52226607495050720607117545 39169955621288040455338159)
  ·
    refine ⟨58754933431932060683007239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39169955621288040455338159 58754933431932060683007239)
    ·
      refine ⟨88132400147898091024510859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58754933431932060683007239 88132400147898091024510859)
      ·
        refine ⟨132198600221847136536766289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88132400147898091024510859 132198600221847136536766289)
        ·
          refine ⟨99148950166385352402574717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132198600221847136536766289 99148950166385352402574717)
          ·
            refine ⟨37180856312394507150965519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99148950166385352402574717 37180856312394507150965519)
            ·
              refine ⟨55771284468591760726448279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37180856312394507150965519 55771284468591760726448279)
              ·
                refine ⟨83656926702887641089672419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55771284468591760726448279 83656926702887641089672419)
                ·
                  refine ⟨125485390054331461634508629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83656926702887641089672419 125485390054331461634508629)
                  ·
                    refine ⟨735265957349598408014699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125485390054331461634508629 735265957349598408014699)
                    ·
                      rfl

theorem cell22_2147888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_2147888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147888 prefixEnd_2147888 := by exact prefixLift 2147888
  have htrace : WordTrace (prefixWord ++ tailWord_2147888) baseStart_2147888 baseEnd_2147888 := by
    simpa [prefixWord, tailWord_2147888, baseEnd_2147888] using wordTrace_append hprefix tailTrace_2147888
  have hstable : (prefixWord ++ tailWord_2147888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147888).length < 2 ^ (prefixWord ++ tailWord_2147888).sum := by decide
  have hdescent : baseEnd_2147888 < baseStart_2147888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147980 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_2147980 : Nat := 118140960795 + 2147980 * 2 ^ 59
def prefixEnd_2147980 : Nat := 4983230072969 + 3 ^ 40 * 2147980 * 2
def baseEnd_2147980 : Nat := 245099150276580278238139

theorem tailTrace_2147980 : CollatzResearch.WordTrace tailWord_2147980 prefixEnd_2147980 245099150276580278238139 := by
  unfold tailWord_2147980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39171633379121390311512697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52228844505495187082016929 39171633379121390311512697)
  ·
    refine ⟨29378725034341042733634523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39171633379121390311512697 29378725034341042733634523)
    ·
      refine ⟨44068087551511564100451785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29378725034341042733634523 44068087551511564100451785)
      ·
        refine ⟨33051065663633673075338839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44068087551511564100451785 33051065663633673075338839)
        ·
          refine ⟨49576598495450509613008259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33051065663633673075338839 49576598495450509613008259)
          ·
            refine ⟨74364897743175764419512389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49576598495450509613008259 74364897743175764419512389)
            ·
              refine ⟨13943418326845455828658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74364897743175764419512389 13943418326845455828658573)
              ·
                refine ⟨5228781872567045935746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13943418326845455828658573 5228781872567045935746965)
                ·
                  refine ⟨245099150276580278238139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5228781872567045935746965 245099150276580278238139)
                  ·
                    rfl

theorem cell22_2147980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_2147980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147980 prefixEnd_2147980 := by exact prefixLift 2147980
  have htrace : WordTrace (prefixWord ++ tailWord_2147980) baseStart_2147980 baseEnd_2147980 := by
    simpa [prefixWord, tailWord_2147980, baseEnd_2147980] using wordTrace_append hprefix tailTrace_2147980
  have hstable : (prefixWord ++ tailWord_2147980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147980).length < 2 ^ (prefixWord ++ tailWord_2147980).sum := by decide
  have hdescent : baseEnd_2147980 < baseStart_2147980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2147982 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2147982 : Nat := 118140960795 + 2147982 * 2 ^ 59
def prefixEnd_2147982 : Nat := 4983230072969 + 3 ^ 40 * 2147982 * 2
def baseEnd_2147982 : Nat := 735298135470613496164411

theorem tailTrace_2147982 : CollatzResearch.WordTrace tailWord_2147982 prefixEnd_2147982 735298135470613496164411 := by
  unfold tailWord_2147982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9792917463029441870574775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52228893136157023309732133 9792917463029441870574775)
  ·
    refine ⟨14689376194544162805862163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9792917463029441870574775 14689376194544162805862163)
    ·
      refine ⟨22034064291816244208793245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689376194544162805862163 22034064291816244208793245)
      ·
        refine ⟨8262774109431091578297467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22034064291816244208793245 8262774109431091578297467)
        ·
          refine ⟨12394161164146637367446201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262774109431091578297467 12394161164146637367446201)
          ·
            refine ⟨9295620873109978025584651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12394161164146637367446201 9295620873109978025584651)
            ·
              refine ⟨13943431309664967038376977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9295620873109978025584651 13943431309664967038376977)
              ·
                refine ⟨10457573482248725278782733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13943431309664967038376977 10457573482248725278782733)
                ·
                  refine ⟨3921590055843271979543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10457573482248725278782733 3921590055843271979543525)
                  ·
                    refine ⟨735298135470613496164411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3921590055843271979543525 735298135470613496164411)
                    ·
                      rfl

theorem cell22_2147982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2147982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2147982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2147982 prefixEnd_2147982 := by exact prefixLift 2147982
  have htrace : WordTrace (prefixWord ++ tailWord_2147982) baseStart_2147982 baseEnd_2147982 := by
    simpa [prefixWord, tailWord_2147982, baseEnd_2147982] using wordTrace_append hprefix tailTrace_2147982
  have hstable : (prefixWord ++ tailWord_2147982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2147982).length < 2 ^ (prefixWord ++ tailWord_2147982).sum := by decide
  have hdescent : baseEnd_2147982 < baseStart_2147982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2147982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148046 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2148046 : Nat := 118140960795 + 2148046 * 2 ^ 59
def prefixEnd_2148046 : Nat := 4983230072969 + 3 ^ 40 * 2148046 * 2
def baseEnd_2148046 : Nat := 735320043978538662564215

theorem tailTrace_2148046 : CollatzResearch.WordTrace tailWord_2148046 prefixEnd_2148046 735320043978538662564215 := by
  unfold tailWord_2148046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793209247000459236865999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52230449317335782596618661 9793209247000459236865999)
  ·
    refine ⟨14689813870500688855298999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9793209247000459236865999 14689813870500688855298999)
    ·
      refine ⟨22034720805751033282948499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14689813870500688855298999 22034720805751033282948499)
      ·
        refine ⟨33052081208626549924422749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22034720805751033282948499 33052081208626549924422749)
        ·
          refine ⟨12394530453234956221658531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33052081208626549924422749 12394530453234956221658531)
          ·
            refine ⟨18591795679852434332487797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12394530453234956221658531 18591795679852434332487797)
            ·
              refine ⟨1742980844986165718670731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18591795679852434332487797 1742980844986165718670731)
              ·
                refine ⟨2614471267479248578006097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742980844986165718670731 2614471267479248578006097)
                ·
                  refine ⟨1960853450609436433504573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2614471267479248578006097 1960853450609436433504573)
                  ·
                    refine ⟨735320043978538662564215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1960853450609436433504573 735320043978538662564215)
                    ·
                      rfl

theorem cell22_2148046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2148046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148046 prefixEnd_2148046 := by exact prefixLift 2148046
  have htrace : WordTrace (prefixWord ++ tailWord_2148046) baseStart_2148046 baseEnd_2148046 := by
    simpa [prefixWord, tailWord_2148046, baseEnd_2148046] using wordTrace_append hprefix tailTrace_2148046
  have hstable : (prefixWord ++ tailWord_2148046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148046).length < 2 ^ (prefixWord ++ tailWord_2148046).sum := by decide
  have hdescent : baseEnd_2148046 < baseStart_2148046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148142 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2148142 : Nat := 118140960795 + 2148142 * 2 ^ 59
def prefixEnd_2148142 : Nat := 4983230072969 + 3 ^ 40 * 2148142 * 2
def baseEnd_2148142 : Nat := 735352906740426412163921

theorem tailTrace_2148142 : CollatzResearch.WordTrace tailWord_2148142 prefixEnd_2148142 735352906740426412163921 := by
  unfold tailWord_2148142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793646922956985286302835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52232783589103921526948453 9793646922956985286302835)
  ·
    refine ⟨14690470384435477929454253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9793646922956985286302835 14690470384435477929454253)
    ·
      refine ⟨5508926394163304223545345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14690470384435477929454253 5508926394163304223545345)
      ·
        refine ⟨4131694795622478167659009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508926394163304223545345 4131694795622478167659009)
        ·
          refine ⟨3098771096716858625744257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4131694795622478167659009 3098771096716858625744257)
          ·
            refine ⟨2324078322537643969308193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098771096716858625744257 2324078322537643969308193)
            ·
              refine ⟨1743058741903232976981145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324078322537643969308193 1743058741903232976981145)
              ·
                refine ⟨1307294056427424732735859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743058741903232976981145 1307294056427424732735859)
                ·
                  refine ⟨1960941084641137099103789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307294056427424732735859 1960941084641137099103789)
                  ·
                    refine ⟨735352906740426412163921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1960941084641137099103789 735352906740426412163921)
                    ·
                      rfl

theorem cell22_2148142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2148142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148142 prefixEnd_2148142 := by exact prefixLift 2148142
  have htrace : WordTrace (prefixWord ++ tailWord_2148142) baseStart_2148142 baseEnd_2148142 := by
    simpa [prefixWord, tailWord_2148142, baseEnd_2148142] using wordTrace_append hprefix tailTrace_2148142
  have hstable : (prefixWord ++ tailWord_2148142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148142).length < 2 ^ (prefixWord ++ tailWord_2148142).sum := by decide
  have hdescent : baseEnd_2148142 < baseStart_2148142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148166 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2148166 : Nat := 118140960795 + 2148166 * 2 ^ 59
def prefixEnd_2148166 : Nat := 4983230072969 + 3 ^ 40 * 2148166 * 2
def baseEnd_2148166 : Nat := 245120374143632783187949

theorem tailTrace_2148166 : CollatzResearch.WordTrace tailWord_2148166 prefixEnd_2148166 245120374143632783187949 := by
  unfold tailWord_2148166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448439085486529199665511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52233367157045956259530901 2448439085486529199665511)
  ·
    refine ⟨3672658628229793799498267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448439085486529199665511 3672658628229793799498267)
    ·
      refine ⟨5508987942344690699247401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672658628229793799498267 5508987942344690699247401)
      ·
        refine ⟨4131740956758518024435551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508987942344690699247401 4131740956758518024435551)
        ·
          refine ⟨6197611435137777036653327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131740956758518024435551 6197611435137777036653327)
          ·
            refine ⟨9296417152706665554979991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6197611435137777036653327 9296417152706665554979991)
            ·
              refine ⟨13944625729059998332469987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9296417152706665554979991 13944625729059998332469987)
              ·
                refine ⟨20916938593589997498704981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13944625729059998332469987 20916938593589997498704981)
                ·
                  refine ⟨245120374143632783187949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20916938593589997498704981 245120374143632783187949)
                  ·
                    rfl

theorem cell22_2148166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2148166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148166 prefixEnd_2148166 := by exact prefixLift 2148166
  have htrace : WordTrace (prefixWord ++ tailWord_2148166) baseStart_2148166 baseEnd_2148166 := by
    simpa [prefixWord, tailWord_2148166, baseEnd_2148166] using wordTrace_append hprefix tailTrace_2148166
  have hstable : (prefixWord ++ tailWord_2148166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148166).length < 2 ^ (prefixWord ++ tailWord_2148166).sum := by decide
  have hdescent : baseEnd_2148166 < baseStart_2148166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148194 : List Nat := [3, 3, 2, 1, 2, 2, 9]
def baseStart_2148194 : Nat := 118140960795 + 2148194 * 2 ^ 59
def prefixEnd_2148194 : Nat := 4983230072969 + 3 ^ 40 * 2148194 * 2
def baseEnd_2148194 : Nat := 27235952126041318883843

theorem tailTrace_2148194 : CollatzResearch.WordTrace tailWord_2148194 prefixEnd_2148194 27235952126041318883843 := by
  unfold tailWord_2148194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19587767994866873792828909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52234047986311663447543757 19587767994866873792828909)
  ·
    refine ⟨7345412998075077672310841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19587767994866873792828909 7345412998075077672310841)
    ·
      refine ⟨5509059748556308254233131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7345412998075077672310841 5509059748556308254233131)
      ·
        refine ⟨8263589622834462381349697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509059748556308254233131 8263589622834462381349697)
        ·
          refine ⟨6197692217125846786012273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8263589622834462381349697 6197692217125846786012273)
          ·
            refine ⟨4648269162844385089509205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197692217125846786012273 4648269162844385089509205)
            ·
              refine ⟨27235952126041318883843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4648269162844385089509205 27235952126041318883843)
              ·
                rfl

theorem cell22_2148194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 9].length) (baseStart_2148194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148194 prefixEnd_2148194 := by exact prefixLift 2148194
  have htrace : WordTrace (prefixWord ++ tailWord_2148194) baseStart_2148194 baseEnd_2148194 := by
    simpa [prefixWord, tailWord_2148194, baseEnd_2148194] using wordTrace_append hprefix tailTrace_2148194
  have hstable : (prefixWord ++ tailWord_2148194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148194).length < 2 ^ (prefixWord ++ tailWord_2148194).sum := by decide
  have hdescent : baseEnd_2148194 < baseStart_2148194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148260 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_2148260 : Nat := 118140960795 + 2148260 * 2 ^ 59
def prefixEnd_2148260 : Nat := 4983230072969 + 3 ^ 40 * 2148260 * 2
def baseEnd_2148260 : Nat := 735393300551913437713559

theorem tailTrace_2148260 : CollatzResearch.WordTrace tailWord_2148260 prefixEnd_2148260 735393300551913437713559 := by
  unfold tailWord_2148260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39176739598614194221609117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52235652798152258962145489 39176739598614194221609117)
  ·
    refine ⟨14691277349480322833103419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39176739598614194221609117 14691277349480322833103419)
    ·
      refine ⟨22036916024220484249655129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14691277349480322833103419 22036916024220484249655129)
      ·
        refine ⟨16527687018165363187241347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22036916024220484249655129 16527687018165363187241347)
        ·
          refine ⟨24791530527248044780862021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16527687018165363187241347 24791530527248044780862021)
          ·
            refine ⟨4648411973859008396411629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24791530527248044780862021 4648411973859008396411629)
            ·
              refine ⟨1743154490197128148654361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4648411973859008396411629 1743154490197128148654361)
              ·
                refine ⟨1307365867647846111490771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743154490197128148654361 1307365867647846111490771)
                ·
                  refine ⟨1961048801471769167236157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1307365867647846111490771 1961048801471769167236157)
                  ·
                    refine ⟨735393300551913437713559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961048801471769167236157 735393300551913437713559)
                    ·
                      rfl

theorem cell22_2148260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_2148260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148260 prefixEnd_2148260 := by exact prefixLift 2148260
  have htrace : WordTrace (prefixWord ++ tailWord_2148260) baseStart_2148260 baseEnd_2148260 := by
    simpa [prefixWord, tailWord_2148260, baseEnd_2148260] using wordTrace_append hprefix tailTrace_2148260
  have hstable : (prefixWord ++ tailWord_2148260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148260).length < 2 ^ (prefixWord ++ tailWord_2148260).sum := by decide
  have hdescent : baseEnd_2148260 < baseStart_2148260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148273 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 5]
def baseStart_2148273 : Nat := 118140960795 + 2148273 * 2 ^ 59
def prefixEnd_2148273 : Nat := 4983230072969 + 3 ^ 40 * 2148273 * 2
def baseEnd_2148273 : Nat := 245132583572528579046173

theorem tailTrace_2148273 : CollatzResearch.WordTrace tailWord_2148273 prefixEnd_2148273 245132583572528579046173 := by
  unfold tailWord_2148273
  simp only [CollatzResearch.WordTrace]
  refine ⟨78353953346181291663441473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52235968897454194442294315 78353953346181291663441473)
  ·
    refine ⟨58765465009635968747581105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78353953346181291663441473 58765465009635968747581105)
    ·
      refine ⟨44074098757226976560685829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58765465009635968747581105 44074098757226976560685829)
      ·
        refine ⟨8263893516980058105128593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44074098757226976560685829 8263893516980058105128593)
        ·
          refine ⟨6197920137735043578846445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8263893516980058105128593 6197920137735043578846445)
          ·
            refine ⟨2324220051650641342067417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6197920137735043578846445 2324220051650641342067417)
            ·
              refine ⟨1743165038737981006550563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324220051650641342067417 1743165038737981006550563)
              ·
                refine ⟨2614747558106971509825845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1743165038737981006550563 2614747558106971509825845)
                ·
                  refine ⟨245132583572528579046173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614747558106971509825845 245132583572528579046173)
                  ·
                    rfl

theorem cell22_2148273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_2148273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148273 prefixEnd_2148273 := by exact prefixLift 2148273
  have htrace : WordTrace (prefixWord ++ tailWord_2148273) baseStart_2148273 baseEnd_2148273 := by
    simpa [prefixWord, tailWord_2148273, baseEnd_2148273] using wordTrace_append hprefix tailTrace_2148273
  have hstable : (prefixWord ++ tailWord_2148273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148273).length < 2 ^ (prefixWord ++ tailWord_2148273).sum := by decide
  have hdescent : baseEnd_2148273 < baseStart_2148273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148286 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2148286 : Nat := 118140960795 + 2148286 * 2 ^ 59
def prefixEnd_2148286 : Nat := 4983230072969 + 3 ^ 40 * 2148286 * 2
def baseEnd_2148286 : Nat := 735402200883258036563479

theorem tailTrace_2148286 : CollatzResearch.WordTrace tailWord_2148286 prefixEnd_2148286 735402200883258036563479 := by
  unfold tailWord_2148286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794303436891774360458089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52236284996756129922443141 9794303436891774360458089)
  ·
    refine ⟨7345727577668830770343567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9794303436891774360458089 7345727577668830770343567)
    ·
      refine ⟨11018591366503246155515351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7345727577668830770343567 11018591366503246155515351)
      ·
        refine ⟨16527887049754869233273027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11018591366503246155515351 16527887049754869233273027)
        ·
          refine ⟨24791830574632303849909541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16527887049754869233273027 24791830574632303849909541)
          ·
            refine ⟨4648468232743556971858039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24791830574632303849909541 4648468232743556971858039)
            ·
              refine ⟨6972702349115335457787059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648468232743556971858039 6972702349115335457787059)
              ·
                refine ⟨10459053523673003186680589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6972702349115335457787059 10459053523673003186680589)
                ·
                  refine ⟨3922145071377376195005221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10459053523673003186680589 3922145071377376195005221)
                  ·
                    refine ⟨735402200883258036563479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3922145071377376195005221 735402200883258036563479)
                    ·
                      rfl

theorem cell22_2148286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2148286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148286 prefixEnd_2148286 := by exact prefixLift 2148286
  have htrace : WordTrace (prefixWord ++ tailWord_2148286) baseStart_2148286 baseEnd_2148286 := by
    simpa [prefixWord, tailWord_2148286, baseEnd_2148286] using wordTrace_append hprefix tailTrace_2148286
  have hstable : (prefixWord ++ tailWord_2148286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148286).length < 2 ^ (prefixWord ++ tailWord_2148286).sum := by decide
  have hdescent : baseEnd_2148286 < baseStart_2148286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148299 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_2148299 : Nat := 118140960795 + 2148299 * 2 ^ 59
def prefixEnd_2148299 : Nat := 4983230072969 + 3 ^ 40 * 2148299 * 2
def baseEnd_2148299 : Nat := 735406651048930335988439

theorem tailTrace_2148299 : CollatzResearch.WordTrace tailWord_2148299 prefixEnd_2148299 735406651048930335988439 := by
  unfold tailWord_2148299
  simp only [CollatzResearch.WordTrace]
  refine ⟨78354901644087098103887951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52236601096058065402591967 78354901644087098103887951)
  ·
    refine ⟨117532352466130647155831927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78354901644087098103887951 117532352466130647155831927)
    ·
      refine ⟨176298528699195970733747891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117532352466130647155831927 176298528699195970733747891)
      ·
        refine ⟨264447793048793956100621837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176298528699195970733747891 264447793048793956100621837)
        ·
          refine ⟨99167922393297733537733189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264447793048793956100621837 99167922393297733537733189)
          ·
            refine ⟨18593985448743325038324973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99167922393297733537733189 18593985448743325038324973)
            ·
              refine ⟨6972744543278746889371865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18593985448743325038324973 6972744543278746889371865)
              ·
                refine ⟨5229558407459060167028899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6972744543278746889371865 5229558407459060167028899)
                ·
                  refine ⟨7844337611188590250543349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5229558407459060167028899 7844337611188590250543349)
                  ·
                    refine ⟨735406651048930335988439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7844337611188590250543349 735406651048930335988439)
                    ·
                      rfl

theorem cell22_2148299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_2148299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148299 prefixEnd_2148299 := by exact prefixLift 2148299
  have htrace : WordTrace (prefixWord ++ tailWord_2148299) baseStart_2148299 baseEnd_2148299 := by
    simpa [prefixWord, tailWord_2148299, baseEnd_2148299] using wordTrace_append hprefix tailTrace_2148299
  have hstable : (prefixWord ++ tailWord_2148299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148299).length < 2 ^ (prefixWord ++ tailWord_2148299).sum := by decide
  have hdescent : baseEnd_2148299 < baseStart_2148299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148378 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_2148378 : Nat := 118140960795 + 2148378 * 2 ^ 59
def prefixEnd_2148378 : Nat := 4983230072969 + 3 ^ 40 * 2148378 * 2
def baseEnd_2148378 : Nat := 735433694363400463263197

theorem tailTrace_2148378 : CollatzResearch.WordTrace tailWord_2148378 prefixEnd_2148378 735433694363400463263197 := by
  unfold tailWord_2148378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589445752700223649003447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52238522007200596397342525 19589445752700223649003447)
  ·
    refine ⟨29384168629050335473505171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19589445752700223649003447 29384168629050335473505171)
    ·
      refine ⟨44076252943575503210257757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29384168629050335473505171 44076252943575503210257757)
      ·
        refine ⟨16528594853840813703846659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44076252943575503210257757 16528594853840813703846659)
        ·
          refine ⟨24792892280761220555769989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16528594853840813703846659 24792892280761220555769989)
          ·
            refine ⟨4648667302642728854206873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24792892280761220555769989 4648667302642728854206873)
            ·
              refine ⟨3486500476982046640655155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648667302642728854206873 3486500476982046640655155)
              ·
                refine ⟨5229750715473069960982733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486500476982046640655155 5229750715473069960982733)
                ·
                  refine ⟨1961156518302401235368525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5229750715473069960982733 1961156518302401235368525)
                  ·
                    refine ⟨735433694363400463263197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961156518302401235368525 735433694363400463263197)
                    ·
                      rfl

theorem cell22_2148378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_2148378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148378 prefixEnd_2148378 := by exact prefixLift 2148378
  have htrace : WordTrace (prefixWord ++ tailWord_2148378) baseStart_2148378 baseEnd_2148378 := by
    simpa [prefixWord, tailWord_2148378, baseEnd_2148378] using wordTrace_append hprefix tailTrace_2148378
  have hstable : (prefixWord ++ tailWord_2148378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148378).length < 2 ^ (prefixWord ++ tailWord_2148378).sum := by decide
  have hdescent : baseEnd_2148378 < baseStart_2148378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148481 : List Nat := [1, 2, 4, 2, 3, 10]
def baseStart_2148481 : Nat := 118140960795 + 2148481 * 2 ^ 59
def prefixEnd_2148481 : Nat := 4983230072969 + 3 ^ 40 * 2148481 * 2
def baseEnd_2148481 : Nat := 9079863621831389233801

theorem tailTrace_2148481 : CollatzResearch.WordTrace tailWord_2148481 prefixEnd_2148481 9079863621831389233801 := by
  unfold tailWord_2148481
  simp only [CollatzResearch.WordTrace]
  refine ⟨78361539729427743187013297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52241026486285162124675531 78361539729427743187013297)
  ·
    refine ⟨58771154797070807390259973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78361539729427743187013297 58771154797070807390259973)
    ·
      refine ⟨11019591524450776385673745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58771154797070807390259973 11019591524450776385673745)
      ·
        refine ⟨8264693643338082289255309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11019591524450776385673745 8264693643338082289255309)
        ·
          refine ⟨3099260116251780858470741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8264693643338082289255309 3099260116251780858470741)
          ·
            refine ⟨9079863621831389233801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3099260116251780858470741 9079863621831389233801)
            ·
              rfl

theorem cell22_2148481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 10].length) (baseStart_2148481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148481 prefixEnd_2148481 := by exact prefixLift 2148481
  have htrace : WordTrace (prefixWord ++ tailWord_2148481) baseStart_2148481 baseEnd_2148481 := by
    simpa [prefixWord, tailWord_2148481, baseEnd_2148481] using wordTrace_append hprefix tailTrace_2148481
  have hstable : (prefixWord ++ tailWord_2148481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148481).length < 2 ^ (prefixWord ++ tailWord_2148481).sum := by decide
  have hdescent : baseEnd_2148481 < baseStart_2148481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148485 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_2148485 : Nat := 118140960795 + 2148485 * 2 ^ 59
def prefixEnd_2148485 : Nat := 4983230072969 + 3 ^ 40 * 2148485 * 2
def baseEnd_2148485 : Nat := 735470322650087850837869

theorem tailTrace_2148485 : CollatzResearch.WordTrace tailWord_2148485 prefixEnd_2148485 735470322650087850837869 := by
  unfold tailWord_2148485
  simp only [CollatzResearch.WordTrace]
  refine ⟨78361685621413251870158909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52241123747608834580105939 78361685621413251870158909)
  ·
    refine ⟨29385632108029969451309591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78361685621413251870158909 29385632108029969451309591)
    ·
      refine ⟨44078448162044954176964387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29385632108029969451309591 44078448162044954176964387)
      ·
        refine ⟨66117672243067431265446581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44078448162044954176964387 66117672243067431265446581)
        ·
          refine ⟨6198531772787571681135617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66117672243067431265446581 6198531772787571681135617)
          ·
            refine ⟨4648898829590678760851713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198531772787571681135617 4648898829590678760851713)
            ·
              refine ⟨3486674122193009070638785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648898829590678760851713 3486674122193009070638785)
              ·
                refine ⟨2615005591644756802979089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486674122193009070638785 2615005591644756802979089)
                ·
                  refine ⟨1961254193733567602234317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615005591644756802979089 1961254193733567602234317)
                  ·
                    refine ⟨735470322650087850837869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961254193733567602234317 735470322650087850837869)
                    ·
                      rfl

theorem cell22_2148485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_2148485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148485 prefixEnd_2148485 := by exact prefixLift 2148485
  have htrace : WordTrace (prefixWord ++ tailWord_2148485) baseStart_2148485 baseEnd_2148485 := by
    simpa [prefixWord, tailWord_2148485, baseEnd_2148485] using wordTrace_append hprefix tailTrace_2148485
  have hstable : (prefixWord ++ tailWord_2148485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148485).length < 2 ^ (prefixWord ++ tailWord_2148485).sum := by decide
  have hdescent : baseEnd_2148485 < baseStart_2148485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148513 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2148513 : Nat := 118140960795 + 2148513 * 2 ^ 59
def prefixEnd_2148513 : Nat := 4983230072969 + 3 ^ 40 * 2148513 * 2
def baseEnd_2148513 : Nat := 735479907622305111137783

theorem tailTrace_2148513 : CollatzResearch.WordTrace tailWord_2148513 prefixEnd_2148513 735479907622305111137783 := by
  unfold tailWord_2148513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78362706865311812652178193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52241804576874541768118795 78362706865311812652178193)
  ·
    refine ⟨58772030148983859489133645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78362706865311812652178193 58772030148983859489133645)
    ·
      refine ⟨22039511305868947308425117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58772030148983859489133645 22039511305868947308425117)
      ·
        refine ⟨8264816739700855240659419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22039511305868947308425117 8264816739700855240659419)
        ·
          refine ⟨12397225109551282860989129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264816739700855240659419 12397225109551282860989129)
          ·
            refine ⟨9297918832163462145741847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12397225109551282860989129 9297918832163462145741847)
            ·
              refine ⟨13946878248245193218612771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9297918832163462145741847 13946878248245193218612771)
              ·
                refine ⟨20920317372367789827919157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13946878248245193218612771 20920317372367789827919157)
                ·
                  refine ⟨1961279753659480296367421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20920317372367789827919157 1961279753659480296367421)
                  ·
                    refine ⟨735479907622305111137783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961279753659480296367421 735479907622305111137783)
                    ·
                      rfl

theorem cell22_2148513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2148513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148513 prefixEnd_2148513 := by exact prefixLift 2148513
  have htrace : WordTrace (prefixWord ++ tailWord_2148513) baseStart_2148513 baseEnd_2148513 := by
    simpa [prefixWord, tailWord_2148513, baseEnd_2148513] using wordTrace_append hprefix tailTrace_2148513
  have hstable : (prefixWord ++ tailWord_2148513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148513).length < 2 ^ (prefixWord ++ tailWord_2148513).sum := by decide
  have hdescent : baseEnd_2148513 < baseStart_2148513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148532 : List Nat := [2, 5, 3, 1, 1, 1, 9]
def baseStart_2148532 : Nat := 118140960795 + 2148532 * 2 ^ 59
def prefixEnd_2148532 : Nat := 4983230072969 + 3 ^ 40 * 2148532 * 2
def baseEnd_2148532 : Nat := 27240237470762792404175

theorem tailTrace_2148532 : CollatzResearch.WordTrace tailWord_2148532 prefixEnd_2148532 27240237470762792404175 := by
  unfold tailWord_2148532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39181699926121489448559925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52242266568161985931413233 39181699926121489448559925)
  ·
    refine ⟨3673284368073889635802493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39181699926121489448559925 3673284368073889635802493)
    ·
      refine ⟨1377481638027708613425935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3673284368073889635802493 1377481638027708613425935)
      ·
        refine ⟨2066222457041562920138903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377481638027708613425935 2066222457041562920138903)
        ·
          refine ⟨3099333685562344380208355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066222457041562920138903 3099333685562344380208355)
          ·
            refine ⟨4649000528343516570312533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099333685562344380208355 4649000528343516570312533)
            ·
              refine ⟨27240237470762792404175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4649000528343516570312533 27240237470762792404175)
              ·
                rfl

theorem cell22_2148532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 9].length) (baseStart_2148532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148532 prefixEnd_2148532 := by exact prefixLift 2148532
  have htrace : WordTrace (prefixWord ++ tailWord_2148532) baseStart_2148532 baseEnd_2148532 := by
    simpa [prefixWord, tailWord_2148532, baseEnd_2148532] using wordTrace_append hprefix tailTrace_2148532
  have hstable : (prefixWord ++ tailWord_2148532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148532).length < 2 ^ (prefixWord ++ tailWord_2148532).sum := by decide
  have hdescent : baseEnd_2148532 < baseStart_2148532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148558 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2148558 : Nat := 118140960795 + 2148558 * 2 ^ 59
def prefixEnd_2148558 : Nat := 4983230072969 + 3 ^ 40 * 2148558 * 2
def baseEnd_2148558 : Nat := 735495312041939993762645

theorem tailTrace_2148558 : CollatzResearch.WordTrace tailWord_2148558 prefixEnd_2148558 735495312041939993762645 := by
  unfold tailWord_2148558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795543518768598167195791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52242898766765856891710885 9795543518768598167195791)
  ·
    refine ⟨14693315278152897250793687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9795543518768598167195791 14693315278152897250793687)
    ·
      refine ⟨22039972917229345876190531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14693315278152897250793687 22039972917229345876190531)
      ·
        refine ⟨33059959375844018814285797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22039972917229345876190531 33059959375844018814285797)
        ·
          refine ⟨6198742382970753527678587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33059959375844018814285797 6198742382970753527678587)
          ·
            refine ⟨9298113574456130291517881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198742382970753527678587 9298113574456130291517881)
            ·
              refine ⟨6973585180842097718638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9298113574456130291517881 6973585180842097718638411)
              ·
                refine ⟨10460377771263146577957617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973585180842097718638411 10460377771263146577957617)
                ·
                  refine ⟨7845283328447359933468213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10460377771263146577957617 7845283328447359933468213)
                  ·
                    refine ⟨735495312041939993762645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7845283328447359933468213 735495312041939993762645)
                    ·
                      rfl

theorem cell22_2148558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2148558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148558 prefixEnd_2148558 := by exact prefixLift 2148558
  have htrace : WordTrace (prefixWord ++ tailWord_2148558) baseStart_2148558 baseEnd_2148558 := by
    simpa [prefixWord, tailWord_2148558, baseEnd_2148558] using wordTrace_append hprefix tailTrace_2148558
  have hstable : (prefixWord ++ tailWord_2148558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148558).length < 2 ^ (prefixWord ++ tailWord_2148558).sum := by decide
  have hdescent : baseEnd_2148558 < baseStart_2148558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148601 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_2148601 : Nat := 118140960795 + 2148601 * 2 ^ 59
def prefixEnd_2148601 : Nat := 4983230072969 + 3 ^ 40 * 2148601 * 2
def baseEnd_2148601 : Nat := 735510031820702214937513

theorem tailTrace_2148601 : CollatzResearch.WordTrace tailWord_2148601 prefixEnd_2148601 735510031820702214937513 := by
  unfold tailWord_2148601
  simp only [CollatzResearch.WordTrace]
  refine ⟨78365916488993003681381657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52243944325995335787587771 78365916488993003681381657)
  ·
    refine ⟨58774437366744752761036243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78365916488993003681381657 58774437366744752761036243)
    ·
      refine ⟨88161656050117129141554365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58774437366744752761036243 88161656050117129141554365)
      ·
        refine ⟨33060621018793923428082887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88161656050117129141554365 33060621018793923428082887)
        ·
          refine ⟨49590931528190885142124331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33060621018793923428082887 49590931528190885142124331)
          ·
            refine ⟨74386397292286327713186497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49590931528190885142124331 74386397292286327713186497)
            ·
              refine ⟨55789797969214745784889873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74386397292286327713186497 55789797969214745784889873)
              ·
                refine ⟨41842348476911059338667405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55789797969214745784889873 41842348476911059338667405)
                ·
                  refine ⟨15690880678841647252000277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41842348476911059338667405 15690880678841647252000277)
                  ·
                    refine ⟨735510031820702214937513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15690880678841647252000277 735510031820702214937513)
                    ·
                      rfl

theorem cell22_2148601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_2148601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148601 prefixEnd_2148601 := by exact prefixLift 2148601
  have htrace : WordTrace (prefixWord ++ tailWord_2148601) baseStart_2148601 baseEnd_2148601 := by
    simpa [prefixWord, tailWord_2148601, baseEnd_2148601] using wordTrace_append hprefix tailTrace_2148601
  have hstable : (prefixWord ++ tailWord_2148601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148601).length < 2 ^ (prefixWord ++ tailWord_2148601).sum := by decide
  have hdescent : baseEnd_2148601 < baseStart_2148601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148620 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_2148620 : Nat := 118140960795 + 2148620 * 2 ^ 59
def prefixEnd_2148620 : Nat := 4983230072969 + 3 ^ 40 * 2148620 * 2
def baseEnd_2148620 : Nat := 735516535908992498712455

theorem tailTrace_2148620 : CollatzResearch.WordTrace tailWord_2148620 prefixEnd_2148620 735516535908992498712455 := by
  unfold tailWord_2148620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39183304737962084963161657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52244406317282779950882209 39183304737962084963161657)
  ·
    refine ⟨29387478553471563722371243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39183304737962084963161657 29387478553471563722371243)
    ·
      refine ⟨44081217830207345583556865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29387478553471563722371243 44081217830207345583556865)
      ·
        refine ⟨33060913372655509187667649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44081217830207345583556865 33060913372655509187667649)
        ·
          refine ⟨24795685029491631890750737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33060913372655509187667649 24795685029491631890750737)
          ·
            refine ⟨18596763772118723918063053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24795685029491631890750737 18596763772118723918063053)
            ·
              refine ⟨6973786414544521469273645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18596763772118723918063053 6973786414544521469273645)
              ·
                refine ⟨2615169905454195550977617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6973786414544521469273645 2615169905454195550977617)
                ·
                  refine ⟨1961377429090646663233213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615169905454195550977617 1961377429090646663233213)
                  ·
                    refine ⟨735516535908992498712455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961377429090646663233213 735516535908992498712455)
                    ·
                      rfl

theorem cell22_2148620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_2148620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148620 prefixEnd_2148620 := by exact prefixLift 2148620
  have htrace : WordTrace (prefixWord ++ tailWord_2148620) baseStart_2148620 baseEnd_2148620 := by
    simpa [prefixWord, tailWord_2148620, baseEnd_2148620] using wordTrace_append hprefix tailTrace_2148620
  have hstable : (prefixWord ++ tailWord_2148620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148620).length < 2 ^ (prefixWord ++ tailWord_2148620).sum := by decide
  have hdescent : baseEnd_2148620 < baseStart_2148620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148650 : List Nat := [3, 1, 4, 2, 3, 9]
def baseStart_2148650 : Nat := 118140960795 + 2148650 * 2 ^ 59
def prefixEnd_2148650 : Nat := 4983230072969 + 3 ^ 40 * 2148650 * 2
def baseEnd_2148650 : Nat := 9080577845951634820523

theorem tailTrace_2148650 : CollatzResearch.WordTrace tailWord_2148650 prefixEnd_2148650 9080577845951634820523 := by
  unfold tailWord_2148650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591925916453871262478851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52245135777210323366610269 19591925916453871262478851)
  ·
    refine ⟨29387888874680806893718277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19591925916453871262478851 29387888874680806893718277)
    ·
      refine ⟨5510229164002651292572177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29387888874680806893718277 5510229164002651292572177)
      ·
        refine ⟨4132671873001988469429133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5510229164002651292572177 4132671873001988469429133)
        ·
          refine ⟨1549751952375745676035925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4132671873001988469429133 1549751952375745676035925)
          ·
            refine ⟨9080577845951634820523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1549751952375745676035925 9080577845951634820523)
            ·
              rfl

theorem cell22_2148650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 9].length) (baseStart_2148650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148650 prefixEnd_2148650 := by exact prefixLift 2148650
  have htrace : WordTrace (prefixWord ++ tailWord_2148650) baseStart_2148650 baseEnd_2148650 := by
    simpa [prefixWord, tailWord_2148650, baseEnd_2148650] using wordTrace_append hprefix tailTrace_2148650
  have hstable : (prefixWord ++ tailWord_2148650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148650).length < 2 ^ (prefixWord ++ tailWord_2148650).sum := by decide
  have hdescent : baseEnd_2148650 < baseStart_2148650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148712 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_2148712 : Nat := 118140960795 + 2148712 * 2 ^ 59
def prefixEnd_2148712 : Nat := 4983230072969 + 3 ^ 40 * 2148712 * 2
def baseEnd_2148712 : Nat := 245182676463044975137391

theorem tailTrace_2148712 : CollatzResearch.WordTrace tailWord_2148712 prefixEnd_2148712 245182676463044975137391 := by
  unfold tailWord_2148712
  simp only [CollatzResearch.WordTrace]
  refine ⟨39184982495795434819336195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52246643327727246425781593 39184982495795434819336195)
  ·
    refine ⟨58777473743693152229004293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39184982495795434819336195 58777473743693152229004293)
    ·
      refine ⟨11020776326942466042938305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58777473743693152229004293 11020776326942466042938305)
      ·
        refine ⟨8265582245206849532203729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11020776326942466042938305 8265582245206849532203729)
        ·
          refine ⟨6199186683905137149152797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8265582245206849532203729 6199186683905137149152797)
          ·
            refine ⟨2324695006464426430932299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6199186683905137149152797 2324695006464426430932299)
            ·
              refine ⟨3487042509696639646398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324695006464426430932299 3487042509696639646398449)
              ·
                refine ⟨2615281882272479734798837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3487042509696639646398449 2615281882272479734798837)
                ·
                  refine ⟨245182676463044975137391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2615281882272479734798837 245182676463044975137391)
                  ·
                    rfl

theorem cell22_2148712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_2148712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148712 prefixEnd_2148712 := by exact prefixLift 2148712
  have htrace : WordTrace (prefixWord ++ tailWord_2148712) baseStart_2148712 baseEnd_2148712 := by
    simpa [prefixWord, tailWord_2148712, baseEnd_2148712] using wordTrace_append hprefix tailTrace_2148712
  have hstable : (prefixWord ++ tailWord_2148712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148712).length < 2 ^ (prefixWord ++ tailWord_2148712).sum := by decide
  have hdescent : baseEnd_2148712 < baseStart_2148712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148768 : List Nat := [2, 1, 1, 4, 1, 3, 10]
def baseStart_2148768 : Nat := 118140960795 + 2148768 * 2 ^ 59
def prefixEnd_2148768 : Nat := 4983230072969 + 3 ^ 40 * 2148768 * 2
def baseEnd_2148768 : Nat := 27243229604947016518963

theorem tailTrace_2148768 : CollatzResearch.WordTrace tailWord_2148768 prefixEnd_2148768 27243229604947016518963 := by
  unfold tailWord_2148768
  simp only [CollatzResearch.WordTrace]
  refine ⟨39186003739693995601355479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52248004986258660801807305 39186003739693995601355479)
  ·
    refine ⟨58779005609540993402033219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39186003739693995601355479 58779005609540993402033219)
    ·
      refine ⟨88168508414311490103049829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58779005609540993402033219 88168508414311490103049829)
      ·
        refine ⟨16531595327683404394321843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88168508414311490103049829 16531595327683404394321843)
        ·
          refine ⟨24797392991525106591482765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16531595327683404394321843 24797392991525106591482765)
          ·
            refine ⟨9299022371821914971806037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24797392991525106591482765 9299022371821914971806037)
            ·
              refine ⟨27243229604947016518963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9299022371821914971806037 27243229604947016518963)
              ·
                rfl

theorem cell22_2148768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 10].length) (baseStart_2148768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148768 prefixEnd_2148768 := by exact prefixLift 2148768
  have htrace : WordTrace (prefixWord ++ tailWord_2148768) baseStart_2148768 baseEnd_2148768 := by
    simpa [prefixWord, tailWord_2148768, baseEnd_2148768] using wordTrace_append hprefix tailTrace_2148768
  have hstable : (prefixWord ++ tailWord_2148768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148768).length < 2 ^ (prefixWord ++ tailWord_2148768).sum := by decide
  have hdescent : baseEnd_2148768 < baseStart_2148768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148785 : List Nat := [1, 2, 2, 4, 1, 3, 2, 7]
def baseStart_2148785 : Nat := 118140960795 + 2148785 * 2 ^ 59
def prefixEnd_2148785 : Nat := 4983230072969 + 3 ^ 40 * 2148785 * 2
def baseEnd_2148785 : Nat := 81730335420109674259661

theorem tailTrace_2148785 : CollatzResearch.WordTrace tailWord_2148785 prefixEnd_2148785 81730335420109674259661 := by
  unfold tailWord_2148785
  simp only [CollatzResearch.WordTrace]
  refine ⟨78372627520326403106079809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52248418346884268737386539 78372627520326403106079809)
  ·
    refine ⟨58779470640244802329559857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78372627520326403106079809 58779470640244802329559857)
    ·
      refine ⟨44084602980183601747169893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58779470640244802329559857 44084602980183601747169893)
      ·
        refine ⟨8265863058784425327594355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44084602980183601747169893 8265863058784425327594355)
        ·
          refine ⟨12398794588176637991391533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265863058784425327594355 12398794588176637991391533)
          ·
            refine ⟨4649547970566239246771825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12398794588176637991391533 4649547970566239246771825)
            ·
              refine ⟨3487160977924679435078869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649547970566239246771825 3487160977924679435078869)
              ·
                refine ⟨81730335420109674259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3487160977924679435078869 81730335420109674259661)
                ·
                  rfl

theorem cell22_2148785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 7].length) (baseStart_2148785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148785 prefixEnd_2148785 := by exact prefixLift 2148785
  have htrace : WordTrace (prefixWord ++ tailWord_2148785) baseStart_2148785 baseEnd_2148785 := by
    simpa [prefixWord, tailWord_2148785, baseEnd_2148785] using wordTrace_append hprefix tailTrace_2148785
  have hstable : (prefixWord ++ tailWord_2148785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148785).length < 2 ^ (prefixWord ++ tailWord_2148785).sum := by decide
  have hdescent : baseEnd_2148785 < baseStart_2148785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148789 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2148789 : Nat := 118140960795 + 2148789 * 2 ^ 59
def prefixEnd_2148789 : Nat := 4983230072969 + 3 ^ 40 * 2148789 * 2
def baseEnd_2148789 : Nat := 735574388062732391236937

theorem tailTrace_2148789 : CollatzResearch.WordTrace tailWord_2148789 prefixEnd_2148789 735574388062732391236937 := by
  unfold tailWord_2148789
  simp only [CollatzResearch.WordTrace]
  refine ⟨78372773412311911789225421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52248515608207941192816947 78372773412311911789225421)
  ·
    refine ⟨29389790029616966920959533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78372773412311911789225421 29389790029616966920959533)
    ·
      refine ⟨11021171261106362595359825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29389790029616966920959533 11021171261106362595359825)
      ·
        refine ⟨8265878445829771946519869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11021171261106362595359825 8265878445829771946519869)
        ·
          refine ⟨3099704417186164479944951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8265878445829771946519869 3099704417186164479944951)
          ·
            refine ⟨4649556625779246719917427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099704417186164479944951 4649556625779246719917427)
            ·
              refine ⟨6974334938668870079876141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649556625779246719917427 6974334938668870079876141)
              ·
                refine ⟨2615375602000826279953553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6974334938668870079876141 2615375602000826279953553)
                ·
                  refine ⟨1961531701500619709965165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615375602000826279953553 1961531701500619709965165)
                  ·
                    refine ⟨735574388062732391236937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961531701500619709965165 735574388062732391236937)
                    ·
                      rfl

theorem cell22_2148789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2148789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148789 prefixEnd_2148789 := by exact prefixLift 2148789
  have htrace : WordTrace (prefixWord ++ tailWord_2148789) baseStart_2148789 baseEnd_2148789 := by
    simpa [prefixWord, tailWord_2148789, baseEnd_2148789] using wordTrace_append hprefix tailTrace_2148789
  have hstable : (prefixWord ++ tailWord_2148789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148789).length < 2 ^ (prefixWord ++ tailWord_2148789).sum := by decide
  have hdescent : baseEnd_2148789 < baseStart_2148789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148800 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_2148800 : Nat := 118140960795 + 2148800 * 2 ^ 59
def prefixEnd_2148800 : Nat := 4983230072969 + 3 ^ 40 * 2148800 * 2
def baseEnd_2148800 : Nat := 735578153587532029211903

theorem tailTrace_2148800 : CollatzResearch.WordTrace tailWord_2148800 prefixEnd_2148800 735578153587532029211903 := by
  unfold tailWord_2148800
  simp only [CollatzResearch.WordTrace]
  refine ⟨39186587307636030333937927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52248783076848040445250569 39186587307636030333937927)
  ·
    refine ⟨58779880961454045500906891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39186587307636030333937927 58779880961454045500906891)
    ·
      refine ⟨88169821442181068251360337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58779880961454045500906891 88169821442181068251360337)
      ·
        refine ⟨66127366081635801188520253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88169821442181068251360337 66127366081635801188520253)
        ·
          refine ⟨24797762280613425445695095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66127366081635801188520253 24797762280613425445695095)
          ·
            refine ⟨37196643420920138168542643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24797762280613425445695095 37196643420920138168542643)
            ·
              refine ⟨55794965131380207252813965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37196643420920138168542643 55794965131380207252813965)
              ·
                refine ⟨20923111924267577719805237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55794965131380207252813965 20923111924267577719805237)
                ·
                  refine ⟨1961541742900085411231741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20923111924267577719805237 1961541742900085411231741)
                  ·
                    refine ⟨735578153587532029211903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961541742900085411231741 735578153587532029211903)
                    ·
                      rfl

theorem cell22_2148800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_2148800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148800 prefixEnd_2148800 := by exact prefixLift 2148800
  have htrace : WordTrace (prefixWord ++ tailWord_2148800) baseStart_2148800 baseEnd_2148800 := by
    simpa [prefixWord, tailWord_2148800, baseEnd_2148800] using wordTrace_append hprefix tailTrace_2148800
  have hstable : (prefixWord ++ tailWord_2148800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148800).length < 2 ^ (prefixWord ++ tailWord_2148800).sum := by decide
  have hdescent : baseEnd_2148800 < baseStart_2148800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148804 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2148804 : Nat := 118140960795 + 2148804 * 2 ^ 59
def prefixEnd_2148804 : Nat := 4983230072969 + 3 ^ 40 * 2148804 * 2
def baseEnd_2148804 : Nat := 735579522869277352111891

theorem tailTrace_2148804 : CollatzResearch.WordTrace tailWord_2148804 prefixEnd_2148804 735579522869277352111891 := by
  unfold tailWord_2148804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39186660253628784675510733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52248880338171712900680977 39186660253628784675510733)
  ·
    refine ⟨14694997595110794253316525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39186660253628784675510733 14694997595110794253316525)
    ·
      refine ⟨5510624098166547844993697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14694997595110794253316525 5510624098166547844993697)
      ·
        refine ⟨4132968073624910883745273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5510624098166547844993697 4132968073624910883745273)
        ·
          refine ⟨3099726055218683162808955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4132968073624910883745273 3099726055218683162808955)
          ·
            refine ⟨4649589082828024744213433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099726055218683162808955 4649589082828024744213433)
            ·
              refine ⟨3487191812121018558160075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649589082828024744213433 3487191812121018558160075)
              ·
                refine ⟨5230787718181527837240113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487191812121018558160075 5230787718181527837240113)
                ·
                  refine ⟨3923090788636145877930085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5230787718181527837240113 3923090788636145877930085)
                  ·
                    refine ⟨735579522869277352111891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3923090788636145877930085 735579522869277352111891)
                    ·
                      rfl

theorem cell22_2148804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2148804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148804 prefixEnd_2148804 := by exact prefixLift 2148804
  have htrace : WordTrace (prefixWord ++ tailWord_2148804) baseStart_2148804 baseEnd_2148804 := by
    simpa [prefixWord, tailWord_2148804, baseEnd_2148804] using wordTrace_append hprefix tailTrace_2148804
  have hstable : (prefixWord ++ tailWord_2148804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148804).length < 2 ^ (prefixWord ++ tailWord_2148804).sum := by decide
  have hdescent : baseEnd_2148804 < baseStart_2148804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148890 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_2148890 : Nat := 118140960795 + 2148890 * 2 ^ 59
def prefixEnd_2148890 : Nat := 4983230072969 + 3 ^ 40 * 2148890 * 2
def baseEnd_2148890 : Nat := 735608962426801794461627

theorem tailTrace_2148890 : CollatzResearch.WordTrace tailWord_2148890 prefixEnd_2148890 735608962426801794461627 := by
  unfold tailWord_2148890
  simp only [CollatzResearch.WordTrace]
  refine ⟨19594114296236501509663031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52250971456630670692434749 19594114296236501509663031)
  ·
    refine ⟨29391171444354752264494547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19594114296236501509663031 29391171444354752264494547)
    ·
      refine ⟨44086757166532128396741821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29391171444354752264494547 44086757166532128396741821)
      ·
        refine ⟨16532533937449548148778183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44086757166532128396741821 16532533937449548148778183)
        ·
          refine ⟨24798800906174322223167275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16532533937449548148778183 24798800906174322223167275)
          ·
            refine ⟨37198201359261483334750913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24798800906174322223167275 37198201359261483334750913)
            ·
              refine ⟨27898651019446112501063185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37198201359261483334750913 27898651019446112501063185)
              ·
                refine ⟨20923988264584584375797389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27898651019446112501063185 20923988264584584375797389)
                ·
                  refine ⟨7846495599219219140924021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20923988264584584375797389 7846495599219219140924021)
                  ·
                    refine ⟨735608962426801794461627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7846495599219219140924021 735608962426801794461627)
                    ·
                      rfl

theorem cell22_2148890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_2148890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148890 prefixEnd_2148890 := by exact prefixLift 2148890
  have htrace : WordTrace (prefixWord ++ tailWord_2148890) baseStart_2148890 baseEnd_2148890 := by
    simpa [prefixWord, tailWord_2148890, baseEnd_2148890] using wordTrace_append hprefix tailTrace_2148890
  have hstable : (prefixWord ++ tailWord_2148890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148890).length < 2 ^ (prefixWord ++ tailWord_2148890).sum := by decide
  have hdescent : baseEnd_2148890 < baseStart_2148890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148892 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_2148892 : Nat := 118140960795 + 2148892 * 2 ^ 59
def prefixEnd_2148892 : Nat := 4983230072969 + 3 ^ 40 * 2148892 * 2
def baseEnd_2148892 : Nat := 245203215689224818637207

theorem tailTrace_2148892 : CollatzResearch.WordTrace tailWord_2148892 prefixEnd_2148892 245203215689224818637207 := by
  unfold tailWord_2148892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39188265065469380190112465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52251020087292506920149953 39188265065469380190112465)
  ·
    refine ⟨29391198799102035142584349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39188265065469380190112465 29391198799102035142584349)
    ·
      refine ⟨11021699549663263178469131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29391198799102035142584349 11021699549663263178469131)
      ·
        refine ⟨16532549324494894767703697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11021699549663263178469131 16532549324494894767703697)
        ·
          refine ⟨12399411993371171075777773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16532549324494894767703697 12399411993371171075777773)
          ·
            refine ⟨4649779497514189153416665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12399411993371171075777773 4649779497514189153416665)
            ·
              refine ⟨3487334623135641865062499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649779497514189153416665 3487334623135641865062499)
              ·
                refine ⟨5231001934703462797593749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487334623135641865062499 5231001934703462797593749)
                ·
                  refine ⟨245203215689224818637207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5231001934703462797593749 245203215689224818637207)
                  ·
                    rfl

theorem cell22_2148892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_2148892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148892 prefixEnd_2148892 := by exact prefixLift 2148892
  have htrace : WordTrace (prefixWord ++ tailWord_2148892) baseStart_2148892 baseEnd_2148892 := by
    simpa [prefixWord, tailWord_2148892, baseEnd_2148892] using wordTrace_append hprefix tailTrace_2148892
  have hstable : (prefixWord ++ tailWord_2148892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148892).length < 2 ^ (prefixWord ++ tailWord_2148892).sum := by decide
  have hdescent : baseEnd_2148892 < baseStart_2148892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148907 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 2, 3]
def baseStart_2148907 : Nat := 118140960795 + 2148907 * 2 ^ 59
def prefixEnd_2148907 : Nat := 4983230072969 + 3 ^ 40 * 2148907 * 2
def baseEnd_2148907 : Nat := 735614781874219416786575

theorem tailTrace_2148907 : CollatzResearch.WordTrace tailWord_2148907 prefixEnd_2148907 735614781874219416786575 := by
  unfold tailWord_2148907
  simp only [CollatzResearch.WordTrace]
  refine ⟨78377077225884417942020975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52251384817256278628013983 78377077225884417942020975)
  ·
    refine ⟨117565615838826626913031463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78377077225884417942020975 117565615838826626913031463)
    ·
      refine ⟨176348423758239940369547195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117565615838826626913031463 176348423758239940369547195)
      ·
        refine ⟨264522635637359910554320793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176348423758239940369547195 264522635637359910554320793)
        ·
          refine ⟨198391976728019932915740595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264522635637359910554320793 198391976728019932915740595)
          ·
            refine ⟨297587965092029899373610893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198391976728019932915740595 297587965092029899373610893)
            ·
              refine ⟨111595486909511212265104085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297587965092029899373610893 111595486909511212265104085)
              ·
                refine ⟨2615519224441669037463377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111595486909511212265104085 2615519224441669037463377)
                ·
                  refine ⟨1961639418331251778097533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615519224441669037463377 1961639418331251778097533)
                  ·
                    refine ⟨735614781874219416786575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961639418331251778097533 735614781874219416786575)
                    ·
                      rfl

theorem cell22_2148907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].length) (baseStart_2148907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148907 prefixEnd_2148907 := by exact prefixLift 2148907
  have htrace : WordTrace (prefixWord ++ tailWord_2148907) baseStart_2148907 baseEnd_2148907 := by
    simpa [prefixWord, tailWord_2148907, baseEnd_2148907] using wordTrace_append hprefix tailTrace_2148907
  have hstable : (prefixWord ++ tailWord_2148907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148907).length < 2 ^ (prefixWord ++ tailWord_2148907).sum := by decide
  have hdescent : baseEnd_2148907 < baseStart_2148907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2148920 : List Nat := [2, 1, 2, 1, 4, 1, 3, 8]
def baseStart_2148920 : Nat := 118140960795 + 2148920 * 2 ^ 59
def prefixEnd_2148920 : Nat := 4983230072969 + 3 ^ 40 * 2148920 * 2
def baseEnd_2148920 : Nat := 81735470226654635134615

theorem tailTrace_2148920 : CollatzResearch.WordTrace tailWord_2148920 prefixEnd_2148920 81735470226654635134615 := by
  unfold tailWord_2148920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39188775687418660581122107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52251700916558214108162809 39188775687418660581122107)
  ·
    refine ⟨58783163531127990871683161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39188775687418660581122107 58783163531127990871683161)
    ·
      refine ⟨44087372648345993153762371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58783163531127990871683161 44087372648345993153762371)
      ·
        refine ⟨66131058972518989730643557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44087372648345993153762371 66131058972518989730643557)
        ·
          refine ⟨12399573557347310574495667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66131058972518989730643557 12399573557347310574495667)
          ·
            refine ⟨18599360336020965861743501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12399573557347310574495667 18599360336020965861743501)
            ·
              refine ⟨6974760126007862198153813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18599360336020965861743501 6974760126007862198153813)
              ·
                refine ⟨81735470226654635134615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6974760126007862198153813 81735470226654635134615)
                ·
                  rfl

theorem cell22_2148920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_2148920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2148920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2148920 prefixEnd_2148920 := by exact prefixLift 2148920
  have htrace : WordTrace (prefixWord ++ tailWord_2148920) baseStart_2148920 baseEnd_2148920 := by
    simpa [prefixWord, tailWord_2148920, baseEnd_2148920] using wordTrace_append hprefix tailTrace_2148920
  have hstable : (prefixWord ++ tailWord_2148920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2148920).length < 2 ^ (prefixWord ++ tailWord_2148920).sum := by decide
  have hdescent : baseEnd_2148920 < baseStart_2148920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2148920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
