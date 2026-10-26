import V185TrunkScan23Chunk1223

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7252909 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7252909 : Nat := 118140960795 + 7252909 * 2 ^ 59
def prefixEnd_7252909 : Nat := 4983230072969 + 3 ^ 40 * 7252909 * 2
def baseEnd_7252909 : Nat := 1241409486773556231293995

theorem tailTrace_7252909 : CollatzResearch.WordTrace tailWord_7252909 prefixEnd_7252909 1241409486773556231293995 := by
  unfold tailWord_7252909
  simp only [CollatzResearch.WordTrace]
  refine ⟨264535323680956866084505781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176356882453971244056337187 264535323680956866084505781)
  ·
    refine ⟨24800186595089706195422417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264535323680956866084505781 24800186595089706195422417)
    ·
      refine ⟨18600139946317279646566813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24800186595089706195422417 18600139946317279646566813)
      ·
        refine ⟨6975052479868979867462555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18600139946317279646566813 6975052479868979867462555)
        ·
          refine ⟨10462578719803469801193833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6975052479868979867462555 10462578719803469801193833)
          ·
            refine ⟨7846934039852602350895375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10462578719803469801193833 7846934039852602350895375)
            ·
              refine ⟨11770401059778903526343063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846934039852602350895375 11770401059778903526343063)
              ·
                refine ⟨17655601589668355289514595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11770401059778903526343063 17655601589668355289514595)
                ·
                  refine ⟨26483402384502532934271893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17655601589668355289514595 26483402384502532934271893)
                  ·
                    refine ⟨1241409486773556231293995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26483402384502532934271893 1241409486773556231293995)
                    ·
                      rfl

theorem cell23_7252909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7252909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252909 prefixEnd_7252909 := by exact prefixLift 7252909
  have htrace : WordTrace (prefixWord ++ tailWord_7252909) baseStart_7252909 baseEnd_7252909 := by
    simpa [prefixWord, tailWord_7252909, baseEnd_7252909] using wordTrace_append hprefix tailTrace_7252909
  have hstable : (prefixWord ++ tailWord_7252909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252909).length < 2 ^ (prefixWord ++ tailWord_7252909).sum := by decide
  have hdescent : baseEnd_7252909 < baseStart_7252909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252916 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7252916 : Nat := 118140960795 + 7252916 * 2 ^ 59
def prefixEnd_7252916 : Nat := 4983230072969 + 3 ^ 40 * 7252916 * 2
def baseEnd_7252916 : Nat := 3724232054685250166494453

theorem tailTrace_7252916 : CollatzResearch.WordTrace tailWord_7252916 prefixEnd_7252916 3724232054685250166494453 := by
  unfold tailWord_7252916
  simp only [CollatzResearch.WordTrace]
  refine ⟨132267789495965753140005301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176357052661287670853340401 132267789495965753140005301)
  ·
    refine ⟨12400105265246789356875497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132267789495965753140005301 12400105265246789356875497)
    ·
      refine ⟨9300078948935092017656623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12400105265246789356875497 9300078948935092017656623)
      ·
        refine ⟨13950118423402638026484935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300078948935092017656623 13950118423402638026484935)
        ·
          refine ⟨20925177635103957039727403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13950118423402638026484935 20925177635103957039727403)
          ·
            refine ⟨31387766452655935559591105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20925177635103957039727403 31387766452655935559591105)
            ·
              refine ⟨23540824839491951669693329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31387766452655935559591105 23540824839491951669693329)
              ·
                refine ⟨17655618629618963752269997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23540824839491951669693329 17655618629618963752269997)
                ·
                  refine ⟨6620856986107111407101249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17655618629618963752269997 6620856986107111407101249)
                  ·
                    refine ⟨4965642739580333555325937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620856986107111407101249 4965642739580333555325937)
                    ·
                      refine ⟨3724232054685250166494453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965642739580333555325937 3724232054685250166494453)
                      ·
                        rfl

theorem cell23_7252916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7252916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252916 prefixEnd_7252916 := by exact prefixLift 7252916
  have htrace : WordTrace (prefixWord ++ tailWord_7252916) baseStart_7252916 baseEnd_7252916 := by
    simpa [prefixWord, tailWord_7252916, baseEnd_7252916] using wordTrace_append hprefix tailTrace_7252916
  have hstable : (prefixWord ++ tailWord_7252916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252916).length < 2 ^ (prefixWord ++ tailWord_7252916).sum := by decide
  have hdescent : baseEnd_7252916 < baseStart_7252916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252928 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_7252928 : Nat := 118140960795 + 7252928 * 2 ^ 59
def prefixEnd_7252928 : Nat := 4983230072969 + 3 ^ 40 * 7252928 * 2
def baseEnd_7252928 : Nat := 3724238216453104119544397

theorem tailTrace_7252928 : CollatzResearch.WordTrace tailWord_7252928 prefixEnd_7252928 3724238216453104119544397 := by
  unfold tailWord_7252928
  simp only [CollatzResearch.WordTrace]
  refine ⟨132268008333944016164723719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176357344445258688219631625 132268008333944016164723719)
  ·
    refine ⟨198402012500916024247085579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132268008333944016164723719 198402012500916024247085579)
    ·
      refine ⟨297603018751374036370628369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198402012500916024247085579 297603018751374036370628369)
      ·
        refine ⟨223202264063530527277971277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297603018751374036370628369 223202264063530527277971277)
        ·
          refine ⟨83700849023823947729239229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223202264063530527277971277 83700849023823947729239229)
          ·
            refine ⟨31387818383933980398464711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83700849023823947729239229 31387818383933980398464711)
            ·
              refine ⟨47081727575900970597697067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31387818383933980398464711 47081727575900970597697067)
              ·
                refine ⟨70622591363851455896545601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47081727575900970597697067 70622591363851455896545601)
                ·
                  refine ⟨52966943522888591922409201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70622591363851455896545601 52966943522888591922409201)
                  ·
                    refine ⟨39725207642166443941806901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52966943522888591922409201 39725207642166443941806901)
                    ·
                      refine ⟨3724238216453104119544397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39725207642166443941806901 3724238216453104119544397)
                      ·
                        rfl

theorem cell23_7252928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_7252928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252928 prefixEnd_7252928 := by exact prefixLift 7252928
  have htrace : WordTrace (prefixWord ++ tailWord_7252928) baseStart_7252928 baseEnd_7252928 := by
    simpa [prefixWord, tailWord_7252928, baseEnd_7252928] using wordTrace_append hprefix tailTrace_7252928
  have hstable : (prefixWord ++ tailWord_7252928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252928).length < 2 ^ (prefixWord ++ tailWord_7252928).sum := by decide
  have hdescent : baseEnd_7252928 < baseStart_7252928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252938 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_7252938 : Nat := 118140960795 + 7252938 * 2 ^ 59
def prefixEnd_7252938 : Nat := 4983230072969 + 3 ^ 40 * 7252938 * 2
def baseEnd_7252938 : Nat := 3724243351259649080419351

theorem tailTrace_7252938 : CollatzResearch.WordTrace tailWord_7252938 prefixEnd_7252938 3724243351259649080419351 := by
  unfold tailWord_7252938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66134095349462951009327867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176357587598567869358207645 66134095349462951009327867)
  ·
    refine ⟨99201143024194426513991801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66134095349462951009327867 99201143024194426513991801)
    ·
      refine ⟨74400857268145819885493851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99201143024194426513991801 74400857268145819885493851)
      ·
        refine ⟨111601285902218729828240777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74400857268145819885493851 111601285902218729828240777)
        ·
          refine ⟨83700964426664047371180583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111601285902218729828240777 83700964426664047371180583)
          ·
            refine ⟨125551446639996071056770875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83700964426664047371180583 125551446639996071056770875)
            ·
              refine ⟨188327169959994106585156313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125551446639996071056770875 188327169959994106585156313)
              ·
                refine ⟨141245377469995579938867235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188327169959994106585156313 141245377469995579938867235)
                ·
                  refine ⟨211868066204993369908300853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141245377469995579938867235 211868066204993369908300853)
                  ·
                    refine ⟨19862631206718128428903205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 211868066204993369908300853 19862631206718128428903205)
                    ·
                      refine ⟨3724243351259649080419351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19862631206718128428903205 3724243351259649080419351)
                      ·
                        rfl

theorem cell23_7252938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_7252938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252938 prefixEnd_7252938 := by exact prefixLift 7252938
  have htrace : WordTrace (prefixWord ++ tailWord_7252938) baseStart_7252938 baseEnd_7252938 := by
    simpa [prefixWord, tailWord_7252938, baseEnd_7252938] using wordTrace_append hprefix tailTrace_7252938
  have hstable : (prefixWord ++ tailWord_7252938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252938).length < 2 ^ (prefixWord ++ tailWord_7252938).sum := by decide
  have hdescent : baseEnd_7252938 < baseStart_7252938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252950 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7252950 : Nat := 118140960795 + 7252950 * 2 ^ 59
def prefixEnd_7252950 : Nat := 4983230072969 + 3 ^ 40 * 7252950 * 2
def baseEnd_7252950 : Nat := 3724249513027503033469297

theorem tailTrace_7252950 : CollatzResearch.WordTrace tailWord_7252950 prefixEnd_7252950 3724249513027503033469297 := by
  unfold tailWord_7252950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533551192113020630421769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176357879382538886724498869 16533551192113020630421769)
  ·
    refine ⟨12400163394084765472816327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16533551192113020630421769 12400163394084765472816327)
    ·
      refine ⟨18600245091127148209224491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12400163394084765472816327 18600245091127148209224491)
      ·
        refine ⟨27900367636690722313836737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18600245091127148209224491 27900367636690722313836737)
        ·
          refine ⟨20925275727518041735377553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27900367636690722313836737 20925275727518041735377553)
          ·
            refine ⟨15693956795638531301533165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20925275727518041735377553 15693956795638531301533165)
            ·
              refine ⟨5885233798364449238074937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15693956795638531301533165 5885233798364449238074937)
              ·
                refine ⟨4413925348773336928556203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885233798364449238074937 4413925348773336928556203)
                ·
                  refine ⟨6620888023160005392834305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413925348773336928556203 6620888023160005392834305)
                  ·
                    refine ⟨4965666017370004044625729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620888023160005392834305 4965666017370004044625729)
                    ·
                      refine ⟨3724249513027503033469297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965666017370004044625729 3724249513027503033469297)
                      ·
                        rfl

theorem cell23_7252950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7252950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252950 prefixEnd_7252950 := by exact prefixLift 7252950
  have htrace : WordTrace (prefixWord ++ tailWord_7252950) baseStart_7252950 baseEnd_7252950 := by
    simpa [prefixWord, tailWord_7252950, baseEnd_7252950] using wordTrace_append hprefix tailTrace_7252950
  have hstable : (prefixWord ++ tailWord_7252950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252950).length < 2 ^ (prefixWord ++ tailWord_7252950).sum := by decide
  have hdescent : baseEnd_7252950 < baseStart_7252950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253006 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7253006 : Nat := 118140960795 + 7253006 * 2 ^ 59
def prefixEnd_7253006 : Nat := 4983230072969 + 3 ^ 40 * 7253006 * 2
def baseEnd_7253006 : Nat := 3724278267944154814369039

theorem tailTrace_7253006 : CollatzResearch.WordTrace tailWord_7253006 prefixEnd_7253006 3724278267944154814369039 := by
  unfold tailWord_7253006
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067357695200681456348359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176359241041070301100524581 33067357695200681456348359)
  ·
    refine ⟨49601036542801022184522539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33067357695200681456348359 49601036542801022184522539)
    ·
      refine ⟨74401554814201533276783809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49601036542801022184522539 74401554814201533276783809)
      ·
        refine ⟨55801166110651149957587857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74401554814201533276783809 55801166110651149957587857)
        ·
          refine ⟨41850874582988362468190893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55801166110651149957587857 41850874582988362468190893)
          ·
            refine ⟨15694077968620635925571585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41850874582988362468190893 15694077968620635925571585)
            ·
              refine ⟨11770558476465476944178689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15694077968620635925571585 11770558476465476944178689)
              ·
                refine ⟨8827918857349107708134017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11770558476465476944178689 8827918857349107708134017)
                ·
                  refine ⟨6620939143011830781100513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8827918857349107708134017 6620939143011830781100513)
                  ·
                    refine ⟨4965704357258873085825385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620939143011830781100513 4965704357258873085825385)
                    ·
                      refine ⟨3724278267944154814369039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965704357258873085825385 3724278267944154814369039)
                      ·
                        rfl

theorem cell23_7253006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7253006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253006 prefixEnd_7253006 := by exact prefixLift 7253006
  have htrace : WordTrace (prefixWord ++ tailWord_7253006) baseStart_7253006 baseEnd_7253006 := by
    simpa [prefixWord, tailWord_7253006, baseEnd_7253006] using wordTrace_append hprefix tailTrace_7253006
  have hstable : (prefixWord ++ tailWord_7253006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253006).length < 2 ^ (prefixWord ++ tailWord_7253006).sum := by decide
  have hdescent : baseEnd_7253006 < baseStart_7253006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253055 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 7, 4]
def baseStart_7253055 : Nat := 118140960795 + 7253055 * 2 ^ 59
def prefixEnd_7253055 : Nat := 4983230072969 + 3 ^ 40 * 7253055 * 2
def baseEnd_7253055 : Nat := 1241434476165408374218771

theorem tailTrace_7253055 : CollatzResearch.WordTrace tailWord_7253055 prefixEnd_7253055 1241434476165408374218771 := by
  unfold tailWord_7253055
  simp only [CollatzResearch.WordTrace]
  refine ⟨264540648738427933019320619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176360432492285288679547079 264540648738427933019320619)
  ·
    refine ⟨396810973107641899528980929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264540648738427933019320619 396810973107641899528980929)
    ·
      refine ⟨297608229830731424646735697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396810973107641899528980929 297608229830731424646735697)
      ·
        refine ⟨223206172373048568485051773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297608229830731424646735697 223206172373048568485051773)
        ·
          refine ⟨83702314639893213181894415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223206172373048568485051773 83702314639893213181894415)
          ·
            refine ⟨125553471959839819772841623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83702314639893213181894415 125553471959839819772841623)
            ·
              refine ⟨188330207939759729659262435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125553471959839819772841623 188330207939759729659262435)
              ·
                refine ⟨282495311909639594488893653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188330207939759729659262435 282495311909639594488893653)
                ·
                  refine ⟨6620983872882177995833445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 282495311909639594488893653 6620983872882177995833445)
                  ·
                    refine ⟨1241434476165408374218771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620983872882177995833445 1241434476165408374218771)
                    ·
                      rfl

theorem cell23_7253055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_7253055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253055 prefixEnd_7253055 := by exact prefixLift 7253055
  have htrace : WordTrace (prefixWord ++ tailWord_7253055) baseStart_7253055 baseEnd_7253055 := by
    simpa [prefixWord, tailWord_7253055, baseEnd_7253055] using wordTrace_append hprefix tailTrace_7253055
  have hstable : (prefixWord ++ tailWord_7253055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253055).length < 2 ^ (prefixWord ++ tailWord_7253055).sum := by decide
  have hdescent : baseEnd_7253055 < baseStart_7253055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253112 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_7253112 : Nat := 118140960795 + 7253112 * 2 ^ 59
def prefixEnd_7253112 : Nat := 4983230072969 + 3 ^ 40 * 7253112 * 2
def baseEnd_7253112 : Nat := 3724332696893531399643551

theorem tailTrace_7253112 : CollatzResearch.WordTrace tailWord_7253112 prefixEnd_7253112 3724332696893531399643551 := by
  unfold tailWord_7253112
  simp only [CollatzResearch.WordTrace]
  refine ⟨132271363849610715877072795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176361818466147621169430393 132271363849610715877072795)
  ·
    refine ⟨198407045774416073815609193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132271363849610715877072795 198407045774416073815609193)
    ·
      refine ⟨148805284330812055361706895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198407045774416073815609193 148805284330812055361706895)
      ·
        refine ⟨223207926496218083042560343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148805284330812055361706895 223207926496218083042560343)
        ·
          refine ⟨334811889744327124563840515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223207926496218083042560343 334811889744327124563840515)
          ·
            refine ⟨502217834616490686845760773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334811889744327124563840515 502217834616490686845760773)
            ·
              refine ⟨94165843990592003783580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502217834616490686845760773 94165843990592003783580145)
              ·
                refine ⟨70624382992944002837685109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94165843990592003783580145 70624382992944002837685109)
                ·
                  refine ⟨6621035905588500266032979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70624382992944002837685109 6621035905588500266032979)
                  ·
                    refine ⟨9931553858382750399049469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621035905588500266032979 9931553858382750399049469)
                    ·
                      refine ⟨3724332696893531399643551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9931553858382750399049469 3724332696893531399643551)
                      ·
                        rfl

theorem cell23_7253112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_7253112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253112 prefixEnd_7253112 := by exact prefixLift 7253112
  have htrace : WordTrace (prefixWord ++ tailWord_7253112) baseStart_7253112 baseEnd_7253112 := by
    simpa [prefixWord, tailWord_7253112, baseEnd_7253112] using wordTrace_append hprefix tailTrace_7253112
  have hstable : (prefixWord ++ tailWord_7253112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253112).length < 2 ^ (prefixWord ++ tailWord_7253112).sum := by decide
  have hdescent : baseEnd_7253112 < baseStart_7253112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253129 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_7253129 : Nat := 118140960795 + 7253129 * 2 ^ 59
def prefixEnd_7253129 : Nat := 4983230072969 + 3 ^ 40 * 7253129 * 2
def baseEnd_7253129 : Nat := 3724341426064657833130973

theorem tailTrace_7253129 : CollatzResearch.WordTrace tailWord_7253129 prefixEnd_7253129 3724341426064657833130973 := by
  unfold tailWord_7253129
  simp only [CollatzResearch.WordTrace]
  refine ⟨264543347740159843657514441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176362231826773229105009627 264543347740159843657514441)
  ·
    refine ⟨198407510805119882743135831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264543347740159843657514441 198407510805119882743135831)
    ·
      refine ⟨297611266207679824114703747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198407510805119882743135831 297611266207679824114703747)
      ·
        refine ⟨446416899311519736172055621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297611266207679824114703747 446416899311519736172055621)
        ·
          refine ⟨83703168620909950532260429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446416899311519736172055621 83703168620909950532260429)
          ·
            refine ⟨31388688232841231449597661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83703168620909950532260429 31388688232841231449597661)
            ·
              refine ⟨11770758087315461793599123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31388688232841231449597661 11770758087315461793599123)
              ·
                refine ⟨17656137130973192690398685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11770758087315461793599123 17656137130973192690398685)
                ·
                  refine ⟨6621051424114947258899507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17656137130973192690398685 6621051424114947258899507)
                  ·
                    refine ⟨9931577136172420888349261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621051424114947258899507 9931577136172420888349261)
                    ·
                      refine ⟨3724341426064657833130973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9931577136172420888349261 3724341426064657833130973)
                      ·
                        rfl

theorem cell23_7253129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_7253129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253129 prefixEnd_7253129 := by exact prefixLift 7253129
  have htrace : WordTrace (prefixWord ++ tailWord_7253129) baseStart_7253129 baseEnd_7253129 := by
    simpa [prefixWord, tailWord_7253129, baseEnd_7253129] using wordTrace_append hprefix tailTrace_7253129
  have hstable : (prefixWord ++ tailWord_7253129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253129).length < 2 ^ (prefixWord ++ tailWord_7253129).sum := by decide
  have hdescent : baseEnd_7253129 < baseStart_7253129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253152 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7253152 : Nat := 118140960795 + 7253152 * 2 ^ 59
def prefixEnd_7253152 : Nat := 4983230072969 + 3 ^ 40 * 7253152 * 2
def baseEnd_7253152 : Nat := 3724353236119711243143367

theorem tailTrace_7253152 : CollatzResearch.WordTrace tailWord_7253152 prefixEnd_7253152 3724353236119711243143367 := by
  unfold tailWord_7253152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132272093309538259292800855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176362791079384345723734473 132272093309538259292800855)
  ·
    refine ⟨198408139964307388939201283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132272093309538259292800855 198408139964307388939201283)
    ·
      refine ⟨297612209946461083408801925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198408139964307388939201283 297612209946461083408801925)
      ·
        refine ⟨55802289364961453139150361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297612209946461083408801925 55802289364961453139150361)
        ·
          refine ⟨41851717023721089854362771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55802289364961453139150361 41851717023721089854362771)
          ·
            refine ⟨62777575535581634781544157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41851717023721089854362771 62777575535581634781544157)
            ·
              refine ⟨23541590825843113043079059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62777575535581634781544157 23541590825843113043079059)
              ·
                refine ⟨35312386238764669564618589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23541590825843113043079059 35312386238764669564618589)
                ·
                  refine ⟨13242144839536751086731971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35312386238764669564618589 13242144839536751086731971)
                  ·
                    refine ⟨19863217259305126630097957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13242144839536751086731971 19863217259305126630097957)
                    ·
                      refine ⟨3724353236119711243143367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19863217259305126630097957 3724353236119711243143367)
                      ·
                        rfl

theorem cell23_7253152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7253152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253152 prefixEnd_7253152 := by exact prefixLift 7253152
  have htrace : WordTrace (prefixWord ++ tailWord_7253152) baseStart_7253152 baseEnd_7253152 := by
    simpa [prefixWord, tailWord_7253152, baseEnd_7253152] using wordTrace_append hprefix tailTrace_7253152
  have hstable : (prefixWord ++ tailWord_7253152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253152).length < 2 ^ (prefixWord ++ tailWord_7253152).sum := by decide
  have hdescent : baseEnd_7253152 < baseStart_7253152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253155 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_7253155 : Nat := 118140960795 + 7253155 * 2 ^ 59
def prefixEnd_7253155 : Nat := 4983230072969 + 3 ^ 40 * 7253155 * 2
def baseEnd_7253155 : Nat := 3724354776561674731405853

theorem tailTrace_7253155 : CollatzResearch.WordTrace tailWord_7253155 prefixEnd_7253155 3724354776561674731405853 := by
  unfold tailWord_7253155
  simp only [CollatzResearch.WordTrace]
  refine ⟨264544296038065650097960919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176362864025377100065307279 264544296038065650097960919)
  ·
    refine ⟨396816444057098475146941379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264544296038065650097960919 396816444057098475146941379)
    ·
      refine ⟨595224666085647712720412069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396816444057098475146941379 595224666085647712720412069)
      ·
        refine ⟨111604624891058946135077263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595224666085647712720412069 111604624891058946135077263)
        ·
          refine ⟨167406937336588419202615895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111604624891058946135077263 167406937336588419202615895)
          ·
            refine ⟨251110406004882628803923843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167406937336588419202615895 251110406004882628803923843)
            ·
              refine ⟨376665609007323943205885765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251110406004882628803923843 376665609007323943205885765)
              ·
                refine ⟨70624801688873239351103581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376665609007323943205885765 70624801688873239351103581)
                ·
                  refine ⟨26484300633327464756663843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70624801688873239351103581 26484300633327464756663843)
                  ·
                    refine ⟨39726450949991197134995765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26484300633327464756663843 39726450949991197134995765)
                    ·
                      refine ⟨3724354776561674731405853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39726450949991197134995765 3724354776561674731405853)
                      ·
                        rfl

theorem cell23_7253155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_7253155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253155 prefixEnd_7253155 := by exact prefixLift 7253155
  have htrace : WordTrace (prefixWord ++ tailWord_7253155) baseStart_7253155 baseEnd_7253155 := by
    simpa [prefixWord, tailWord_7253155, baseEnd_7253155] using wordTrace_append hprefix tailTrace_7253155
  have hstable : (prefixWord ++ tailWord_7253155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253155).length < 2 ^ (prefixWord ++ tailWord_7253155).sum := by decide
  have hdescent : baseEnd_7253155 < baseStart_7253155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253156 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_7253156 : Nat := 118140960795 + 7253156 * 2 ^ 59
def prefixEnd_7253156 : Nat := 4983230072969 + 3 ^ 40 * 7253156 * 2
def baseEnd_7253156 : Nat := 3724355290042329227493349

theorem tailTrace_7253156 : CollatzResearch.WordTrace tailWord_7253156 prefixEnd_7253156 3724355290042329227493349 := by
  unfold tailWord_7253156
  simp only [CollatzResearch.WordTrace]
  refine ⟨132272166255531013634373661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176362888340708018179164881 132272166255531013634373661)
  ·
    refine ⟨49602062345824130112890123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132272166255531013634373661 49602062345824130112890123)
    ·
      refine ⟨74403093518736195169335185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49602062345824130112890123 74403093518736195169335185)
      ·
        refine ⟨55802320139052146377001389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74403093518736195169335185 55802320139052146377001389)
        ·
          refine ⟨20925870052144554891375521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55802320139052146377001389 20925870052144554891375521)
          ·
            refine ⟨15694402539108416168531641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20925870052144554891375521 15694402539108416168531641)
            ·
              refine ⟨11770801904331312126398731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15694402539108416168531641 11770801904331312126398731)
              ·
                refine ⟨17656202856496968189598097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11770801904331312126398731 17656202856496968189598097)
                ·
                  refine ⟨13242152142372726142198573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17656202856496968189598097 13242152142372726142198573)
                  ·
                    refine ⟨4965807053389772303324465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242152142372726142198573 4965807053389772303324465)
                    ·
                      refine ⟨3724355290042329227493349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965807053389772303324465 3724355290042329227493349)
                      ·
                        rfl

theorem cell23_7253156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_7253156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253156 prefixEnd_7253156 := by exact prefixLift 7253156
  have htrace : WordTrace (prefixWord ++ tailWord_7253156) baseStart_7253156 baseEnd_7253156 := by
    simpa [prefixWord, tailWord_7253156, baseEnd_7253156] using wordTrace_append hprefix tailTrace_7253156
  have hstable : (prefixWord ++ tailWord_7253156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253156).length < 2 ^ (prefixWord ++ tailWord_7253156).sum := by decide
  have hdescent : baseEnd_7253156 < baseStart_7253156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253174 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7253174 : Nat := 118140960795 + 7253174 * 2 ^ 59
def prefixEnd_7253174 : Nat := 4983230072969 + 3 ^ 40 * 7253174 * 2
def baseEnd_7253174 : Nat := 1241454844231370052356089

theorem tailTrace_7253174 : CollatzResearch.WordTrace tailWord_7253174 prefixEnd_7253174 1241454844231370052356089 := by
  unfold tailWord_7253174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534061814062301021431411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176363326016664544228601717 16534061814062301021431411)
  ·
    refine ⟨24801092721093451532147117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16534061814062301021431411 24801092721093451532147117)
    ·
      refine ⟨9300409770410044324555169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24801092721093451532147117 9300409770410044324555169)
      ·
        refine ⟨6975307327807533243416377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9300409770410044324555169 6975307327807533243416377)
        ·
          refine ⟨5231480495855649932562283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6975307327807533243416377 5231480495855649932562283)
          ·
            refine ⟨7847220743783474898843425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231480495855649932562283 7847220743783474898843425)
            ·
              refine ⟨5885415557837606174132569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847220743783474898843425 5885415557837606174132569)
              ·
                refine ⟨4414061668378204630599427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885415557837606174132569 4414061668378204630599427)
                ·
                  refine ⟨6621092502567306945899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414061668378204630599427 6621092502567306945899141)
                  ·
                    refine ⟨1241454844231370052356089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621092502567306945899141 1241454844231370052356089)
                    ·
                      rfl

theorem cell23_7253174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7253174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253174 prefixEnd_7253174 := by exact prefixLift 7253174
  have htrace : WordTrace (prefixWord ++ tailWord_7253174) baseStart_7253174 baseEnd_7253174 := by
    simpa [prefixWord, tailWord_7253174, baseEnd_7253174] using wordTrace_append hprefix tailTrace_7253174
  have hstable : (prefixWord ++ tailWord_7253174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253174).length < 2 ^ (prefixWord ++ tailWord_7253174).sum := by decide
  have hdescent : baseEnd_7253174 < baseStart_7253174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253180 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_7253180 : Nat := 118140960795 + 7253180 * 2 ^ 59
def prefixEnd_7253180 : Nat := 4983230072969 + 3 ^ 40 * 7253180 * 2
def baseEnd_7253180 : Nat := 3724367613578037133593239

theorem tailTrace_7253180 : CollatzResearch.WordTrace tailWord_7253180 prefixEnd_7253180 3724367613578037133593239 := by
  unfold tailWord_7253180
  simp only [CollatzResearch.WordTrace]
  refine ⟨132272603931487539683810497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176363471908650052911747329 132272603931487539683810497)
  ·
    refine ⟨99204452948615654762857873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132272603931487539683810497 99204452948615654762857873)
    ·
      refine ⟨74403339711461741072143405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99204452948615654762857873 74403339711461741072143405)
      ·
        refine ⟨27901252391798152902053777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74403339711461741072143405 27901252391798152902053777)
        ·
          refine ⟨20925939293848614676540333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27901252391798152902053777 20925939293848614676540333)
          ·
            refine ⟨7847227235193230503702625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20925939293848614676540333 7847227235193230503702625)
            ·
              refine ⟨5885420426394922877776969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847227235193230503702625 5885420426394922877776969)
              ·
                refine ⟨4414065319796192158332727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885420426394922877776969 4414065319796192158332727)
                ·
                  refine ⟨6621097979694288237499091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414065319796192158332727 6621097979694288237499091)
                  ·
                    refine ⟨9931646969541432356248637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621097979694288237499091 9931646969541432356248637)
                    ·
                      refine ⟨3724367613578037133593239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9931646969541432356248637 3724367613578037133593239)
                      ·
                        rfl

theorem cell23_7253180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_7253180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253180 prefixEnd_7253180 := by exact prefixLift 7253180
  have htrace : WordTrace (prefixWord ++ tailWord_7253180) baseStart_7253180 baseEnd_7253180 := by
    simpa [prefixWord, tailWord_7253180, baseEnd_7253180] using wordTrace_append hprefix tailTrace_7253180
  have hstable : (prefixWord ++ tailWord_7253180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253180).length < 2 ^ (prefixWord ++ tailWord_7253180).sum := by decide
  have hdescent : baseEnd_7253180 < baseStart_7253180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253276 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7253276 : Nat := 118140960795 + 7253276 * 2 ^ 59
def prefixEnd_7253276 : Nat := 4983230072969 + 3 ^ 40 * 7253276 * 2
def baseEnd_7253276 : Nat := 3724416907720868757992797

theorem tailTrace_7253276 : CollatzResearch.WordTrace tailWord_7253276 prefixEnd_7253276 3724416907720868757992797 := by
  unfold tailWord_7253276
  simp only [CollatzResearch.WordTrace]
  refine ⟨132274354635313643881557841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176365806180418191842077121 132274354635313643881557841)
  ·
    refine ⟨99205765976485232911168381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132274354635313643881557841 99205765976485232911168381)
    ·
      refine ⟨37202162241181962341688143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99205765976485232911168381 37202162241181962341688143)
      ·
        refine ⟨55803243361772943512532215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37202162241181962341688143 55803243361772943512532215)
        ·
          refine ⟨83704865042659415268798323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55803243361772943512532215 83704865042659415268798323)
          ·
            refine ⟨125557297563989122903197485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83704865042659415268798323 125557297563989122903197485)
            ·
              refine ⟨47083986586495921088699057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125557297563989122903197485 47083986586495921088699057)
              ·
                refine ⟨35312989939871940816524293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47083986586495921088699057 35312989939871940816524293)
                ·
                  refine ⟨6621185613725988903098305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35312989939871940816524293 6621185613725988903098305)
                  ·
                    refine ⟨4965889210294491677323729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621185613725988903098305 4965889210294491677323729)
                    ·
                      refine ⟨3724416907720868757992797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965889210294491677323729 3724416907720868757992797)
                      ·
                        rfl

theorem cell23_7253276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7253276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253276 prefixEnd_7253276 := by exact prefixLift 7253276
  have htrace : WordTrace (prefixWord ++ tailWord_7253276) baseStart_7253276 baseEnd_7253276 := by
    simpa [prefixWord, tailWord_7253276, baseEnd_7253276] using wordTrace_append hprefix tailTrace_7253276
  have hstable : (prefixWord ++ tailWord_7253276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253276).length < 2 ^ (prefixWord ++ tailWord_7253276).sum := by decide
  have hdescent : baseEnd_7253276 < baseStart_7253276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253279 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_7253279 : Nat := 118140960795 + 7253279 * 2 ^ 59
def prefixEnd_7253279 : Nat := 4983230072969 + 3 ^ 40 * 7253279 * 2
def baseEnd_7253279 : Nat := 3724418448162832246255283

theorem tailTrace_7253279 : CollatzResearch.WordTrace tailWord_7253279 prefixEnd_7253279 3724418448162832246255283 := by
  unfold tailWord_7253279
  simp only [CollatzResearch.WordTrace]
  refine ⟨264548818689616419275474891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176365879126410946183649927 264548818689616419275474891)
  ·
    refine ⟨396823228034424628913212337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264548818689616419275474891 396823228034424628913212337)
    ·
      refine ⟨297617421025818471684909253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396823228034424628913212337 297617421025818471684909253)
      ·
        refine ⟨55803266442340963440920485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297617421025818471684909253 55803266442340963440920485)
        ·
          refine ⟨10463112457938930645172591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55803266442340963440920485 10463112457938930645172591)
          ·
            refine ⟨15694668686908395967758887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10463112457938930645172591 15694668686908395967758887)
            ·
              refine ⟨23542003030362593951638331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15694668686908395967758887 23542003030362593951638331)
              ·
                refine ⟨35313004545543890927457497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23542003030362593951638331 35313004545543890927457497)
                ·
                  refine ⟨26484753409157918195593123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35313004545543890927457497 26484753409157918195593123)
                  ·
                    refine ⟨39727130113736877293389685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26484753409157918195593123 39727130113736877293389685)
                    ·
                      refine ⟨3724418448162832246255283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39727130113736877293389685 3724418448162832246255283)
                      ·
                        rfl

theorem cell23_7253279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_7253279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253279 prefixEnd_7253279 := by exact prefixLift 7253279
  have htrace : WordTrace (prefixWord ++ tailWord_7253279) baseStart_7253279 baseEnd_7253279 := by
    simpa [prefixWord, tailWord_7253279, baseEnd_7253279] using wordTrace_append hprefix tailTrace_7253279
  have hstable : (prefixWord ++ tailWord_7253279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253279).length < 2 ^ (prefixWord ++ tailWord_7253279).sum := by decide
  have hdescent : baseEnd_7253279 < baseStart_7253279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253299 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 7]
def baseStart_7253299 : Nat := 118140960795 + 7253299 * 2 ^ 59
def prefixEnd_7253299 : Nat := 4983230072969 + 3 ^ 40 * 7253299 * 2
def baseEnd_7253299 : Nat := 413825413086213574222799

theorem tailTrace_7253299 : CollatzResearch.WordTrace tailWord_7253299 prefixEnd_7253299 413825413086213574222799 := by
  unfold tailWord_7253299
  simp only [CollatzResearch.WordTrace]
  refine ⟨264549548149543962691202951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176366365433029308460801967 264549548149543962691202951)
  ·
    refine ⟨396824322224315944036804427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264549548149543962691202951 396824322224315944036804427)
    ·
      refine ⟨595236483336473916055206641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396824322224315944036804427 595236483336473916055206641)
      ·
        refine ⟨446427362502355437041404981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595236483336473916055206641 446427362502355437041404981)
        ·
          refine ⟨41852565234595822222631717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446427362502355437041404981 41852565234595822222631717)
          ·
            refine ⟨7847355981486716666743447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41852565234595822222631717 7847355981486716666743447)
            ·
              refine ⟨11771033972230075000115171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847355981486716666743447 11771033972230075000115171)
              ·
                refine ⟨17656550958345112500172757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11771033972230075000115171 17656550958345112500172757)
                ·
                  refine ⟨413825413086213574222799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17656550958345112500172757 413825413086213574222799)
                  ·
                    rfl

theorem cell23_7253299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 7].length) (baseStart_7253299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253299 prefixEnd_7253299 := by exact prefixLift 7253299
  have htrace : WordTrace (prefixWord ++ tailWord_7253299) baseStart_7253299 baseEnd_7253299 := by
    simpa [prefixWord, tailWord_7253299, baseEnd_7253299] using wordTrace_append hprefix tailTrace_7253299
  have hstable : (prefixWord ++ tailWord_7253299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253299).length < 2 ^ (prefixWord ++ tailWord_7253299).sum := by decide
  have hdescent : baseEnd_7253299 < baseStart_7253299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253312 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_7253312 : Nat := 118140960795 + 7253312 * 2 ^ 59
def prefixEnd_7253312 : Nat := 4983230072969 + 3 ^ 40 * 7253312 * 2
def baseEnd_7253312 : Nat := 1241478464341476872380877

theorem tailTrace_7253312 : CollatzResearch.WordTrace tailWord_7253312 prefixEnd_7253312 1241478464341476872380877 := by
  unfold tailWord_7253312
  simp only [CollatzResearch.WordTrace]
  refine ⟨132275011149248432955713095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176366681532331243940950793 132275011149248432955713095)
  ·
    refine ⟨198412516723872649433569643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132275011149248432955713095 198412516723872649433569643)
    ·
      refine ⟨297618775085808974150354465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198412516723872649433569643 297618775085808974150354465)
      ·
        refine ⟨223214081314356730612765849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297618775085808974150354465 223214081314356730612765849)
        ·
          refine ⟨167410560985767547959574387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223214081314356730612765849 167410560985767547959574387)
          ·
            refine ⟨251115841478651321939361581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167410560985767547959574387 251115841478651321939361581)
            ·
              refine ⟨94168440554494245727260593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251115841478651321939361581 94168440554494245727260593)
              ·
                refine ⟨70626330415870684295445445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94168440554494245727260593 70626330415870684295445445)
                ·
                  refine ⟨13242436952975753305396021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70626330415870684295445445 13242436952975753305396021)
                  ·
                    refine ⟨1241478464341476872380877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13242436952975753305396021 1241478464341476872380877)
                    ·
                      rfl

theorem cell23_7253312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_7253312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253312 prefixEnd_7253312 := by exact prefixLift 7253312
  have htrace : WordTrace (prefixWord ++ tailWord_7253312) baseStart_7253312 baseEnd_7253312 := by
    simpa [prefixWord, tailWord_7253312, baseEnd_7253312] using wordTrace_append hprefix tailTrace_7253312
  have hstable : (prefixWord ++ tailWord_7253312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253312).length < 2 ^ (prefixWord ++ tailWord_7253312).sum := by decide
  have hdescent : baseEnd_7253312 < baseStart_7253312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253329 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_7253329 : Nat := 118140960795 + 7253329 * 2 ^ 59
def prefixEnd_7253329 : Nat := 4983230072969 + 3 ^ 40 * 7253329 * 2
def baseEnd_7253329 : Nat := 1241481374065185683543351

theorem tailTrace_7253329 : CollatzResearch.WordTrace tailWord_7253329 prefixEnd_7253329 1241481374065185683543351 := by
  unfold tailWord_7253329
  simp only [CollatzResearch.WordTrace]
  refine ⟨264550642339435277814795041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176367094892956851876530027 264550642339435277814795041)
  ·
    refine ⟨198412981754576458361096281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264550642339435277814795041 198412981754576458361096281)
    ·
      refine ⟨148809736315932343770822211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198412981754576458361096281 148809736315932343770822211)
      ·
        refine ⟨223214604473898515656233317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148809736315932343770822211 223214604473898515656233317)
        ·
          refine ⟨41852738338855971685543747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223214604473898515656233317 41852738338855971685543747)
          ·
            refine ⟨62779107508283957528315621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41852738338855971685543747 62779107508283957528315621)
            ·
              refine ⟨11771082657803242036559179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62779107508283957528315621 11771082657803242036559179)
              ·
                refine ⟨17656623986704863054838769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11771082657803242036559179 17656623986704863054838769)
                ·
                  refine ⟨13242467990028647291129077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17656623986704863054838769 13242467990028647291129077)
                  ·
                    refine ⟨1241481374065185683543351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13242467990028647291129077 1241481374065185683543351)
                    ·
                      rfl

theorem cell23_7253329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_7253329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253329 prefixEnd_7253329 := by exact prefixLift 7253329
  have htrace : WordTrace (prefixWord ++ tailWord_7253329) baseStart_7253329 baseEnd_7253329 := by
    simpa [prefixWord, tailWord_7253329, baseEnd_7253329] using wordTrace_append hprefix tailTrace_7253329
  have hstable : (prefixWord ++ tailWord_7253329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253329).length < 2 ^ (prefixWord ++ tailWord_7253329).sum := by decide
  have hdescent : baseEnd_7253329 < baseStart_7253329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253349 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7253349 : Nat := 118140960795 + 7253349 * 2 ^ 59
def prefixEnd_7253349 : Nat := 4983230072969 + 3 ^ 40 * 7253349 * 2
def baseEnd_7253349 : Nat := 3724454391808646972379961

theorem tailTrace_7253349 : CollatzResearch.WordTrace tailWord_7253349 prefixEnd_7253349 3724454391808646972379961 := by
  unfold tailWord_7253349
  simp only [CollatzResearch.WordTrace]
  refine ⟨264551371799362821230523101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176367581199575214153682067 264551371799362821230523101)
  ·
    refine ⟨99206764424761057961446163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264551371799362821230523101 99206764424761057961446163)
    ·
      refine ⟨148810146637141586942169245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99206764424761057961446163 148810146637141586942169245)
      ·
        refine ⟨55803804988928095103313467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148810146637141586942169245 55803804988928095103313467)
        ·
          refine ⟨83705707483392142654970201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55803804988928095103313467 83705707483392142654970201)
          ·
            refine ⟨62779280612544106991227651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83705707483392142654970201 62779280612544106991227651)
            ·
              refine ⟨94168920918816160486841477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62779280612544106991227651 94168920918816160486841477)
              ·
                refine ⟨17656672672278030091282777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94168920918816160486841477 17656672672278030091282777)
                ·
                  refine ⟨13242504504208522568462083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17656672672278030091282777 13242504504208522568462083)
                  ·
                    refine ⟨19863756756312783852693125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13242504504208522568462083 19863756756312783852693125)
                    ·
                      refine ⟨3724454391808646972379961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19863756756312783852693125 3724454391808646972379961)
                      ·
                        rfl

theorem cell23_7253349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7253349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253349 prefixEnd_7253349 := by exact prefixLift 7253349
  have htrace : WordTrace (prefixWord ++ tailWord_7253349) baseStart_7253349 baseEnd_7253349 := by
    simpa [prefixWord, tailWord_7253349, baseEnd_7253349] using wordTrace_append hprefix tailTrace_7253349
  have hstable : (prefixWord ++ tailWord_7253349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253349).length < 2 ^ (prefixWord ++ tailWord_7253349).sum := by decide
  have hdescent : baseEnd_7253349 < baseStart_7253349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253359 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 3, 4]
def baseStart_7253359 : Nat := 118140960795 + 7253359 * 2 ^ 59
def prefixEnd_7253359 : Nat := 4983230072969 + 3 ^ 40 * 7253359 * 2
def baseEnd_7253359 : Nat := 1241486508871730644418305

theorem tailTrace_7253359 : CollatzResearch.WordTrace tailWord_7253359 prefixEnd_7253359 1241486508871730644418305 := by
  unfold tailWord_7253359
  simp only [CollatzResearch.WordTrace]
  refine ⟨264551736529326592938387131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176367824352884395292258087 264551736529326592938387131)
  ·
    refine ⟨396827604793989889407580697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264551736529326592938387131 396827604793989889407580697)
    ·
      refine ⟨297620703595492417055685523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396827604793989889407580697 297620703595492417055685523)
      ·
        refine ⟨446431055393238625583528285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297620703595492417055685523 446431055393238625583528285)
        ·
          refine ⟨167411645772464484593823107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446431055393238625583528285 167411645772464484593823107)
          ·
            refine ⟨251117468658696726890734661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167411645772464484593823107 251117468658696726890734661)
            ·
              refine ⟨47084525373505636292012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251117468658696726890734661 47084525373505636292012749)
              ·
                refine ⟨17656697015064613609504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47084525373505636292012749 17656697015064613609504781)
                ·
                  refine ⟨6621261380649230103564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17656697015064613609504781 6621261380649230103564293)
                  ·
                    refine ⟨1241486508871730644418305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621261380649230103564293 1241486508871730644418305)
                    ·
                      rfl

theorem cell23_7253359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_7253359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253359 prefixEnd_7253359 := by exact prefixLift 7253359
  have htrace : WordTrace (prefixWord ++ tailWord_7253359) baseStart_7253359 baseEnd_7253359 := by
    simpa [prefixWord, tailWord_7253359, baseEnd_7253359] using wordTrace_append hprefix tailTrace_7253359
  have hstable : (prefixWord ++ tailWord_7253359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253359).length < 2 ^ (prefixWord ++ tailWord_7253359).sum := by decide
  have hdescent : baseEnd_7253359 < baseStart_7253359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253369 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_7253369 : Nat := 118140960795 + 7253369 * 2 ^ 59
def prefixEnd_7253369 : Nat := 4983230072969 + 3 ^ 40 * 7253369 * 2
def baseEnd_7253369 : Nat := 3724464661421736894129869

theorem tailTrace_7253369 : CollatzResearch.WordTrace tailWord_7253369 prefixEnd_7253369 3724464661421736894129869 := by
  unfold tailWord_7253369
  simp only [CollatzResearch.WordTrace]
  refine ⟨264552101259290364646251161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176368067506193576430834107 264552101259290364646251161)
  ·
    refine ⟨198414075944467773484688371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264552101259290364646251161 198414075944467773484688371)
    ·
      refine ⟨297621113916701660227032557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198414075944467773484688371 297621113916701660227032557)
      ·
        refine ⟨111607917718763122585137209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297621113916701660227032557 111607917718763122585137209)
        ·
          refine ⟨83705938289072341938852907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111607917718763122585137209 83705938289072341938852907)
          ·
            refine ⟨125558907433608512908279361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83705938289072341938852907 125558907433608512908279361)
            ·
              refine ⟨94169180575206384681209521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125558907433608512908279361 94169180575206384681209521)
              ·
                refine ⟨70626885431404788510907141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94169180575206384681209521 70626885431404788510907141)
                ·
                  refine ⟨13242541018388397845795089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70626885431404788510907141 13242541018388397845795089)
                  ·
                    refine ⟨9931905763791298384346317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13242541018388397845795089 9931905763791298384346317)
                    ·
                      refine ⟨3724464661421736894129869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9931905763791298384346317 3724464661421736894129869)
                      ·
                        rfl

theorem cell23_7253369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_7253369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253369 prefixEnd_7253369 := by exact prefixLift 7253369
  have htrace : WordTrace (prefixWord ++ tailWord_7253369) baseStart_7253369 baseEnd_7253369 := by
    simpa [prefixWord, tailWord_7253369, baseEnd_7253369] using wordTrace_append hprefix tailTrace_7253369
  have hstable : (prefixWord ++ tailWord_7253369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253369).length < 2 ^ (prefixWord ++ tailWord_7253369).sum := by decide
  have hdescent : baseEnd_7253369 < baseStart_7253369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253426 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_7253426 : Nat := 118140960795 + 7253426 * 2 ^ 59
def prefixEnd_7253426 : Nat := 4983230072969 + 3 ^ 40 * 7253426 * 2
def baseEnd_7253426 : Nat := 3724493929819043171117107

theorem tailTrace_7253426 : CollatzResearch.WordTrace tailWord_7253426 prefixEnd_7253426 3724493929819043171117107 := by
  unfold tailWord_7253426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66138545055020965845269033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176369453480055908920717421 66138545055020965845269033)
  ·
    refine ⟨49603908791265724383951775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66138545055020965845269033 49603908791265724383951775)
    ·
      refine ⟨74405863186898586575927663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49603908791265724383951775 74405863186898586575927663)
      ·
        refine ⟨111608794780347879863891495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74405863186898586575927663 111608794780347879863891495)
        ·
          refine ⟨167413192170521819795837243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111608794780347879863891495 167413192170521819795837243)
          ·
            refine ⟨251119788255782729693755865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167413192170521819795837243 251119788255782729693755865)
            ·
              refine ⟨188339841191837047270316899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251119788255782729693755865 188339841191837047270316899)
              ·
                refine ⟨282509761787755570905475349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188339841191837047270316899 282509761787755570905475349)
                ·
                  refine ⟨13242645083801042386194157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282509761787755570905475349 13242645083801042386194157)
                  ·
                    refine ⟨4965991906425390894822809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242645083801042386194157 4965991906425390894822809)
                    ·
                      refine ⟨3724493929819043171117107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965991906425390894822809 3724493929819043171117107)
                      ·
                        rfl

theorem cell23_7253426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_7253426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253426 prefixEnd_7253426 := by exact prefixLift 7253426
  have htrace : WordTrace (prefixWord ++ tailWord_7253426) baseStart_7253426 baseEnd_7253426 := by
    simpa [prefixWord, tailWord_7253426, baseEnd_7253426] using wordTrace_append hprefix tailTrace_7253426
  have hstable : (prefixWord ++ tailWord_7253426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253426).length < 2 ^ (prefixWord ++ tailWord_7253426).sum := by decide
  have hdescent : baseEnd_7253426 < baseStart_7253426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253439 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_7253439 : Nat := 118140960795 + 7253439 * 2 ^ 59
def prefixEnd_7253439 : Nat := 4983230072969 + 3 ^ 40 * 7253439 * 2
def baseEnd_7253439 : Nat := 3724500605067551620254547

theorem tailTrace_7253439 : CollatzResearch.WordTrace tailWord_7253439 prefixEnd_7253439 3724500605067551620254547 := by
  unfold tailWord_7253439
  simp only [CollatzResearch.WordTrace]
  refine ⟨264554654369036766601299371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176369769579357844400866247 264554654369036766601299371)
  ·
    refine ⟨396831981553555149901949057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264554654369036766601299371 396831981553555149901949057)
    ·
      refine ⟨297623986165166362426461793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396831981553555149901949057 297623986165166362426461793)
      ·
        refine ⟨223217989623874771819846345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297623986165166362426461793 223217989623874771819846345)
        ·
          refine ⟨167413492217906078864884759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223217989623874771819846345 167413492217906078864884759)
          ·
            refine ⟨251120238326859118297327139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167413492217906078864884759 251120238326859118297327139)
            ·
              refine ⟨376680357490288677445990709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251120238326859118297327139 376680357490288677445990709)
              ·
                refine ⟨35313783514714563510561629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376680357490288677445990709 35313783514714563510561629)
                ·
                  refine ⟨13242668818017961316460611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35313783514714563510561629 13242668818017961316460611)
                  ·
                    refine ⟨19864003227026941974690917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13242668818017961316460611 19864003227026941974690917)
                    ·
                      refine ⟨3724500605067551620254547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19864003227026941974690917 3724500605067551620254547)
                      ·
                        rfl

theorem cell23_7253439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_7253439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253439 prefixEnd_7253439 := by exact prefixLift 7253439
  have htrace : WordTrace (prefixWord ++ tailWord_7253439) baseStart_7253439 baseEnd_7253439 := by
    simpa [prefixWord, tailWord_7253439, baseEnd_7253439] using wordTrace_append hprefix tailTrace_7253439
  have hstable : (prefixWord ++ tailWord_7253439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253439).length < 2 ^ (prefixWord ++ tailWord_7253439).sum := by decide
  have hdescent : baseEnd_7253439 < baseStart_7253439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253450 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_7253450 : Nat := 118140960795 + 7253450 * 2 ^ 59
def prefixEnd_7253450 : Nat := 4983230072969 + 3 ^ 40 * 7253450 * 2
def baseEnd_7253450 : Nat := 3724506253354751077216997

theorem tailTrace_7253450 : CollatzResearch.WordTrace tailWord_7253450 prefixEnd_7253450 3724506253354751077216997 := by
  unfold tailWord_7253450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66138763892999228869987451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176370037047997943653299869 66138763892999228869987451)
  ·
    refine ⟨99208145839498843304981177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66138763892999228869987451 99208145839498843304981177)
    ·
      refine ⟨74406109379624132478735883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99208145839498843304981177 74406109379624132478735883)
      ·
        refine ⟨111609164069436198718103825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74406109379624132478735883 111609164069436198718103825)
        ·
          refine ⟨83706873052077149038577869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111609164069436198718103825 83706873052077149038577869)
          ·
            refine ⟨31390077394528930889466701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83706873052077149038577869 31390077394528930889466701)
            ·
              refine ⟨11771279022948349083550013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31390077394528930889466701 11771279022948349083550013)
              ·
                refine ⟨4414229633605630906331255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771279022948349083550013 4414229633605630906331255)
                ·
                  refine ⟨6621344450408446359496883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414229633605630906331255 6621344450408446359496883)
                  ·
                    refine ⟨9932016675612669539245325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621344450408446359496883 9932016675612669539245325)
                    ·
                      refine ⟨3724506253354751077216997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932016675612669539245325 3724506253354751077216997)
                      ·
                        rfl

theorem cell23_7253450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_7253450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253450 prefixEnd_7253450 := by exact prefixLift 7253450
  have htrace : WordTrace (prefixWord ++ tailWord_7253450) baseStart_7253450 baseEnd_7253450 := by
    simpa [prefixWord, tailWord_7253450, baseEnd_7253450] using wordTrace_append hprefix tailTrace_7253450
  have hstable : (prefixWord ++ tailWord_7253450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253450).length < 2 ^ (prefixWord ++ tailWord_7253450).sum := by decide
  have hdescent : baseEnd_7253450 < baseStart_7253450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253460 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7253460 : Nat := 118140960795 + 7253460 * 2 ^ 59
def prefixEnd_7253460 : Nat := 4983230072969 + 3 ^ 40 * 7253460 * 2
def baseEnd_7253460 : Nat := 3724511388161296038091951

theorem tailTrace_7253460 : CollatzResearch.WordTrace tailWord_7253460 prefixEnd_7253460 3724511388161296038091951 := by
  unfold tailWord_7253460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132277710150980343593906917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176370280201307124791875889 132277710150980343593906917)
  ·
    refine ⟨24802070653308814423857547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132277710150980343593906917 24802070653308814423857547)
    ·
      refine ⟨37203105979963221635786321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24802070653308814423857547 37203105979963221635786321)
      ·
        refine ⟨27902329484972416226839741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37203105979963221635786321 27902329484972416226839741)
        ·
          refine ⟨10463373556864656085064903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27902329484972416226839741 10463373556864656085064903)
          ·
            refine ⟨15695060335296984127597355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10463373556864656085064903 15695060335296984127597355)
            ·
              refine ⟨23542590502945476191396033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695060335296984127597355 23542590502945476191396033)
              ·
                refine ⟨17656942877209107143547025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23542590502945476191396033 17656942877209107143547025)
                ·
                  refine ⟨13242707157906830357660269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17656942877209107143547025 13242707157906830357660269)
                  ·
                    refine ⟨4966015184215061384122601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242707157906830357660269 4966015184215061384122601)
                    ·
                      refine ⟨3724511388161296038091951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966015184215061384122601 3724511388161296038091951)
                      ·
                        rfl

theorem cell23_7253460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7253460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253460 prefixEnd_7253460 := by exact prefixLift 7253460
  have htrace : WordTrace (prefixWord ++ tailWord_7253460) baseStart_7253460 baseEnd_7253460 := by
    simpa [prefixWord, tailWord_7253460, baseEnd_7253460] using wordTrace_append hprefix tailTrace_7253460
  have hstable : (prefixWord ++ tailWord_7253460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253460).length < 2 ^ (prefixWord ++ tailWord_7253460).sum := by decide
  have hdescent : baseEnd_7253460 < baseStart_7253460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253466 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_7253466 : Nat := 118140960795 + 7253466 * 2 ^ 59
def prefixEnd_7253466 : Nat := 4983230072969 + 3 ^ 40 * 7253466 * 2
def baseEnd_7253466 : Nat := 1241504823015074338205641

theorem tailTrace_7253466 : CollatzResearch.WordTrace tailWord_7253466 prefixEnd_7253466 1241504823015074338205641 := by
  unfold tailWord_7253466
  simp only [CollatzResearch.WordTrace]
  refine ⟨66138909784984737553133063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176370426093292633475021501 66138909784984737553133063)
  ·
    refine ⟨99208364677477106329699595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66138909784984737553133063 99208364677477106329699595)
    ·
      refine ⟨148812547016215659494549393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99208364677477106329699595 148812547016215659494549393)
      ·
        refine ⟨111609410262161744620912045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148812547016215659494549393 111609410262161744620912045)
        ·
          refine ⟨41853528848310654232842017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111609410262161744620912045 41853528848310654232842017)
          ·
            refine ⟨31390146636232990674631513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41853528848310654232842017 31390146636232990674631513)
            ·
              refine ⟨23542609977174743005973635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31390146636232990674631513 23542609977174743005973635)
              ·
                refine ⟨35313914965762114508960453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23542609977174743005973635 35313914965762114508960453)
                ·
                  refine ⟨6621359056080396470430085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35313914965762114508960453 6621359056080396470430085)
                  ·
                    refine ⟨1241504823015074338205641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6621359056080396470430085 1241504823015074338205641)
                    ·
                      rfl

theorem cell23_7253466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_7253466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253466 prefixEnd_7253466 := by exact prefixLift 7253466
  have htrace : WordTrace (prefixWord ++ tailWord_7253466) baseStart_7253466 baseEnd_7253466 := by
    simpa [prefixWord, tailWord_7253466, baseEnd_7253466] using wordTrace_append hprefix tailTrace_7253466
  have hstable : (prefixWord ++ tailWord_7253466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253466).length < 2 ^ (prefixWord ++ tailWord_7253466).sum := by decide
  have hdescent : baseEnd_7253466 < baseStart_7253466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253479 : List Nat := [1, 1, 5, 2, 1, 2, 1, 10]
def baseStart_7253479 : Nat := 118140960795 + 7253479 * 2 ^ 59
def prefixEnd_7253479 : Nat := 4983230072969 + 3 ^ 40 * 7253479 * 2
def baseEnd_7253479 : Nat := 137945227566434498657569

theorem tailTrace_7253479 : CollatzResearch.WordTrace tailWord_7253479 prefixEnd_7253479 137945227566434498657569 := by
  unfold tailWord_7253479
  simp only [CollatzResearch.WordTrace]
  refine ⟨264556113288891853432755491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176370742192594568955170327 264556113288891853432755491)
  ·
    refine ⟨396834169933337780149133237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264556113288891853432755491 396834169933337780149133237)
    ·
      refine ⟨37203203431250416888981241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396834169933337780149133237 37203203431250416888981241)
      ·
        refine ⟨27902402573437812666735931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37203203431250416888981241 27902402573437812666735931)
        ·
          refine ⟨41853603860156719000103897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902402573437812666735931 41853603860156719000103897)
          ·
            refine ⟨31390202895117539250077923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41853603860156719000103897 31390202895117539250077923)
            ·
              refine ⟨47085304342676308875116885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31390202895117539250077923 47085304342676308875116885)
              ·
                refine ⟨137945227566434498657569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47085304342676308875116885 137945227566434498657569)
                ·
                  rfl

theorem cell23_7253479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 10].length) (baseStart_7253479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253479 prefixEnd_7253479 := by exact prefixLift 7253479
  have htrace : WordTrace (prefixWord ++ tailWord_7253479) baseStart_7253479 baseEnd_7253479 := by
    simpa [prefixWord, tailWord_7253479, baseEnd_7253479] using wordTrace_append hprefix tailTrace_7253479
  have hstable : (prefixWord ++ tailWord_7253479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253479).length < 2 ^ (prefixWord ++ tailWord_7253479).sum := by decide
  have hdescent : baseEnd_7253479 < baseStart_7253479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253486 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7253486 : Nat := 118140960795 + 7253486 * 2 ^ 59
def prefixEnd_7253486 : Nat := 4983230072969 + 3 ^ 40 * 7253486 * 2
def baseEnd_7253486 : Nat := 3724524738658312936366831

theorem tailTrace_7253486 : CollatzResearch.WordTrace tailWord_7253486 prefixEnd_7253486 3724524738658312936366831 := by
  unfold tailWord_7253486
  simp only [CollatzResearch.WordTrace]
  refine ⟨33069546074983311703532539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176370912399910995752173541 33069546074983311703532539)
  ·
    refine ⟨49604319112474967555298809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33069546074983311703532539 49604319112474967555298809)
    ·
      refine ⟨37203239334356225666474107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49604319112474967555298809 37203239334356225666474107)
      ·
        refine ⟨55804859001534338499711161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203239334356225666474107 55804859001534338499711161)
        ·
          refine ⟨41853644251150753874783371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55804859001534338499711161 41853644251150753874783371)
          ·
            refine ⟨62780466376726130812175057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41853644251150753874783371 62780466376726130812175057)
            ·
              refine ⟨47085349782544598109131293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62780466376726130812175057 47085349782544598109131293)
              ·
                refine ⟨17657006168454224290924235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47085349782544598109131293 17657006168454224290924235)
                ·
                  refine ⟨26485509252681336436386353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17657006168454224290924235 26485509252681336436386353)
                  ·
                    refine ⟨19864131939511002327289765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26485509252681336436386353 19864131939511002327289765)
                    ·
                      refine ⟨3724524738658312936366831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19864131939511002327289765 3724524738658312936366831)
                      ·
                        rfl

theorem cell23_7253486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7253486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253486 prefixEnd_7253486 := by exact prefixLift 7253486
  have htrace : WordTrace (prefixWord ++ tailWord_7253486) baseStart_7253486 baseEnd_7253486 := by
    simpa [prefixWord, tailWord_7253486, baseEnd_7253486] using wordTrace_append hprefix tailTrace_7253486
  have hstable : (prefixWord ++ tailWord_7253486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253486).length < 2 ^ (prefixWord ++ tailWord_7253486).sum := by decide
  have hdescent : baseEnd_7253486 < baseStart_7253486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253490 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7253490 : Nat := 118140960795 + 7253490 * 2 ^ 59
def prefixEnd_7253490 : Nat := 4983230072969 + 3 ^ 40 * 7253490 * 2
def baseEnd_7253490 : Nat := 3724526792580930920716813

theorem tailTrace_7253490 : CollatzResearch.WordTrace tailWord_7253490 prefixEnd_7253490 3724526792580930920716813 := by
  unfold tailWord_7253490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139128622963000577851481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176371009661234668207603949 66139128622963000577851481)
  ·
    refine ⟨49604346467222250433388611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66139128622963000577851481 49604346467222250433388611)
    ·
      refine ⟨74406519700833375650082917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49604346467222250433388611 74406519700833375650082917)
      ·
        refine ⟨13951222443906257934390547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74406519700833375650082917 13951222443906257934390547)
        ·
          refine ⟨20926833665859386901585821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13951222443906257934390547 20926833665859386901585821)
          ·
            refine ⟨7847562624697270088094683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20926833665859386901585821 7847562624697270088094683)
            ·
              refine ⟨11771343937045905132142025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847562624697270088094683 11771343937045905132142025)
              ·
                refine ⟨8828507952784428849106519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11771343937045905132142025 8828507952784428849106519)
                ·
                  refine ⟨13242761929176643273659779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8828507952784428849106519 13242761929176643273659779)
                  ·
                    refine ⟨19864142893764964910489669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13242761929176643273659779 19864142893764964910489669)
                    ·
                      refine ⟨3724526792580930920716813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19864142893764964910489669 3724526792580930920716813)
                      ·
                        rfl

theorem cell23_7253490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7253490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253490 prefixEnd_7253490 := by exact prefixLift 7253490
  have htrace : WordTrace (prefixWord ++ tailWord_7253490) baseStart_7253490 baseEnd_7253490 := by
    simpa [prefixWord, tailWord_7253490, baseEnd_7253490] using wordTrace_append hprefix tailTrace_7253490
  have hstable : (prefixWord ++ tailWord_7253490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253490).length < 2 ^ (prefixWord ++ tailWord_7253490).sum := by decide
  have hdescent : baseEnd_7253490 < baseStart_7253490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253523 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 3]
def baseStart_7253523 : Nat := 118140960795 + 7253523 * 2 ^ 59
def prefixEnd_7253523 : Nat := 4983230072969 + 3 ^ 40 * 7253523 * 2
def baseEnd_7253523 : Nat := 3724543737442529291604161

theorem tailTrace_7253523 : CollatzResearch.WordTrace tailWord_7253523 prefixEnd_7253523 3724543737442529291604161 := by
  unfold tailWord_7253523
  simp only [CollatzResearch.WordTrace]
  refine ⟨264557718100732448947357223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176371812067154965964904815 264557718100732448947357223)
  ·
    refine ⟨396836577151098673421035835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264557718100732448947357223 396836577151098673421035835)
    ·
      refine ⟨595254865726648010131553753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396836577151098673421035835 595254865726648010131553753)
      ·
        refine ⟨446441149294986007598665315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595254865726648010131553753 446441149294986007598665315)
        ·
          refine ⟨669661723942479011397997973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446441149294986007598665315 669661723942479011397997973)
          ·
            refine ⟨31390393309803703659281155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 669661723942479011397997973 31390393309803703659281155)
            ·
              refine ⟨47085589964705555488921733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31390393309803703659281155 47085589964705555488921733)
              ·
                refine ⟨8828548118382291654172825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47085589964705555488921733 8828548118382291654172825)
                ·
                  refine ⟨6621411088786718740629619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828548118382291654172825 6621411088786718740629619)
                  ·
                    refine ⟨9932116633180078110944429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621411088786718740629619 9932116633180078110944429)
                    ·
                      refine ⟨3724543737442529291604161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932116633180078110944429 3724543737442529291604161)
                      ·
                        rfl

theorem cell23_7253523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_7253523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253523 prefixEnd_7253523 := by exact prefixLift 7253523
  have htrace : WordTrace (prefixWord ++ tailWord_7253523) baseStart_7253523 baseEnd_7253523 := by
    simpa [prefixWord, tailWord_7253523, baseEnd_7253523] using wordTrace_append hprefix tailTrace_7253523
  have hstable : (prefixWord ++ tailWord_7253523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253523).length < 2 ^ (prefixWord ++ tailWord_7253523).sum := by decide
  have hdescent : baseEnd_7253523 < baseStart_7253523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253533 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7253533 : Nat := 118140960795 + 7253533 * 2 ^ 59
def prefixEnd_7253533 : Nat := 4983230072969 + 3 ^ 40 * 7253533 * 2
def baseEnd_7253533 : Nat := 3724548872249074252479115

theorem tailTrace_7253533 : CollatzResearch.WordTrace tailWord_7253533 prefixEnd_7253533 3724548872249074252479115 := by
  unfold tailWord_7253533
  simp only [CollatzResearch.WordTrace]
  refine ⟨264558082830696220655221253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176372055220464147103480835 264558082830696220655221253)
  ·
    refine ⟨49604640530755541372853985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264558082830696220655221253 49604640530755541372853985)
    ·
      refine ⟨37203480398066656029640489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49604640530755541372853985 37203480398066656029640489)
      ·
        refine ⟨27902610298549992022230367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37203480398066656029640489 27902610298549992022230367)
        ·
          refine ⟨41853915447824988033345551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902610298549992022230367 41853915447824988033345551)
          ·
            refine ⟨62780873171737482050018327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41853915447824988033345551 62780873171737482050018327)
            ·
              refine ⟨94171309757606223075027491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62780873171737482050018327 94171309757606223075027491)
              ·
                refine ⟨141256964636409334612541237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94171309757606223075027491 141256964636409334612541237)
                ·
                  refine ⟨13242840434663375119925741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141256964636409334612541237 13242840434663375119925741)
                  ·
                    refine ⟨4966065162998765669972153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242840434663375119925741 4966065162998765669972153)
                    ·
                      refine ⟨3724548872249074252479115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966065162998765669972153 3724548872249074252479115)
                      ·
                        rfl

theorem cell23_7253533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7253533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253533 prefixEnd_7253533 := by exact prefixLift 7253533
  have htrace : WordTrace (prefixWord ++ tailWord_7253533) baseStart_7253533 baseEnd_7253533 := by
    simpa [prefixWord, tailWord_7253533, baseEnd_7253533] using wordTrace_append hprefix tailTrace_7253533
  have hstable : (prefixWord ++ tailWord_7253533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253533).length < 2 ^ (prefixWord ++ tailWord_7253533).sum := by decide
  have hdescent : baseEnd_7253533 < baseStart_7253533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253546 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7253546 : Nat := 118140960795 + 7253546 * 2 ^ 59
def prefixEnd_7253546 : Nat := 4983230072969 + 3 ^ 40 * 7253546 * 2
def baseEnd_7253546 : Nat := 3724555547497582701616555

theorem tailTrace_7253546 : CollatzResearch.WordTrace tailWord_7253546 prefixEnd_7253546 3724555547497582701616555 := by
  unfold tailWord_7253546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139639244912280968861123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176372371319766082583629661 66139639244912280968861123)
  ·
    refine ⟨99209458867368421453291685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66139639244912280968861123 99209458867368421453291685)
    ·
      refine ⟨18601773537631579022492191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99209458867368421453291685 18601773537631579022492191)
      ·
        refine ⟨27902660306447368533738287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18601773537631579022492191 27902660306447368533738287)
        ·
          refine ⟨41853990459671052800607431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902660306447368533738287 41853990459671052800607431)
          ·
            refine ⟨62780985689506579200911147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41853990459671052800607431 62780985689506579200911147)
            ·
              refine ⟨94171478534259868801366721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62780985689506579200911147 94171478534259868801366721)
              ·
                refine ⟨70628608900694901601025041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94171478534259868801366721 70628608900694901601025041)
                ·
                  refine ⟨52971456675521176200768781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70628608900694901601025041 52971456675521176200768781)
                  ·
                    refine ⟨19864296253320441075288293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52971456675521176200768781 19864296253320441075288293)
                    ·
                      refine ⟨3724555547497582701616555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19864296253320441075288293 3724555547497582701616555)
                      ·
                        rfl

theorem cell23_7253546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7253546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253546 prefixEnd_7253546 := by exact prefixLift 7253546
  have htrace : WordTrace (prefixWord ++ tailWord_7253546) baseStart_7253546 baseEnd_7253546 := by
    simpa [prefixWord, tailWord_7253546, baseEnd_7253546] using wordTrace_append hprefix tailTrace_7253546
  have hstable : (prefixWord ++ tailWord_7253546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253546).length < 2 ^ (prefixWord ++ tailWord_7253546).sum := by decide
  have hdescent : baseEnd_7253546 < baseStart_7253546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253550 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7253550 : Nat := 118140960795 + 7253550 * 2 ^ 59
def prefixEnd_7253550 : Nat := 4983230072969 + 3 ^ 40 * 7253550 * 2
def baseEnd_7253550 : Nat := 3724557601420200685966537

theorem tailTrace_7253550 : CollatzResearch.WordTrace tailWord_7253550 prefixEnd_7253550 3724557601420200685966537 := by
  unfold tailWord_7253550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33069837858954329069823763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176372468581089755039060069 33069837858954329069823763)
  ·
    refine ⟨49604756788431493604735645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33069837858954329069823763 49604756788431493604735645)
    ·
      refine ⟨18601783795661810101775867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49604756788431493604735645 18601783795661810101775867)
      ·
        refine ⟨27902675693492715152663801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18601783795661810101775867 27902675693492715152663801)
        ·
          refine ⟨20927006770119536364497851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27902675693492715152663801 20927006770119536364497851)
          ·
            refine ⟨31390510155179304546746777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20927006770119536364497851 31390510155179304546746777)
            ·
              refine ⟨23542882616384478410060083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31390510155179304546746777 23542882616384478410060083)
              ·
                refine ⟨35314323924576717615090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23542882616384478410060083 35314323924576717615090125)
                ·
                  refine ⟨13242871471716269105658797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35314323924576717615090125 13242871471716269105658797)
                  ·
                    refine ⟨4966076801893600914622049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242871471716269105658797 4966076801893600914622049)
                    ·
                      refine ⟨3724557601420200685966537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966076801893600914622049 3724557601420200685966537)
                      ·
                        rfl

theorem cell23_7253550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7253550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253550 prefixEnd_7253550 := by exact prefixLift 7253550
  have htrace : WordTrace (prefixWord ++ tailWord_7253550) baseStart_7253550 baseEnd_7253550 := by
    simpa [prefixWord, tailWord_7253550, baseEnd_7253550] using wordTrace_append hprefix tailTrace_7253550
  have hstable : (prefixWord ++ tailWord_7253550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253550).length < 2 ^ (prefixWord ++ tailWord_7253550).sum := by decide
  have hdescent : baseEnd_7253550 < baseStart_7253550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253567 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 1, 3, 2]
def baseStart_7253567 : Nat := 118140960795 + 7253567 * 2 ^ 59
def prefixEnd_7253567 : Nat := 4983230072969 + 3 ^ 40 * 7253567 * 2
def baseEnd_7253567 : Nat := 3724566330591327119453959

theorem tailTrace_7253567 : CollatzResearch.WordTrace tailWord_7253567 prefixEnd_7253567 3724566330591327119453959 := by
  unfold tailWord_7253567
  simp only [CollatzResearch.WordTrace]
  refine ⟨264559322912573044461958955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176372881941715362974639303 264559322912573044461958955)
  ·
    refine ⟨396838984368859566692938433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264559322912573044461958955 396838984368859566692938433)
    ·
      refine ⟨297629238276644675019703825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396838984368859566692938433 297629238276644675019703825)
      ·
        refine ⟨223221928707483506264777869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297629238276644675019703825 223221928707483506264777869)
        ·
          refine ⟨83708223265306314849291701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223221928707483506264777869 83708223265306314849291701)
          ·
            refine ⟨7847645931122467017121097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83708223265306314849291701 7847645931122467017121097)
            ·
              refine ⟨5885734448341850262840823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847645931122467017121097 5885734448341850262840823)
              ·
                refine ⟨8828601672512775394261235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885734448341850262840823 8828601672512775394261235)
                ·
                  refine ⟨13242902508769163091391853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8828601672512775394261235 13242902508769163091391853)
                  ·
                    refine ⟨4966088440788436159271945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242902508769163091391853 4966088440788436159271945)
                    ·
                      refine ⟨3724566330591327119453959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966088440788436159271945 3724566330591327119453959)
                      ·
                        rfl

theorem cell23_7253567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_7253567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253567 prefixEnd_7253567 := by exact prefixLift 7253567
  have htrace : WordTrace (prefixWord ++ tailWord_7253567) baseStart_7253567 baseEnd_7253567 := by
    simpa [prefixWord, tailWord_7253567, baseEnd_7253567] using wordTrace_append hprefix tailTrace_7253567
  have hstable : (prefixWord ++ tailWord_7253567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253567).length < 2 ^ (prefixWord ++ tailWord_7253567).sum := by decide
  have hdescent : baseEnd_7253567 < baseStart_7253567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253580 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7253580 : Nat := 118140960795 + 7253580 * 2 ^ 59
def prefixEnd_7253580 : Nat := 4983230072969 + 3 ^ 40 * 7253580 * 2
def baseEnd_7253580 : Nat := 3724573005839835568591399

theorem tailTrace_7253580 : CollatzResearch.WordTrace tailWord_7253580 prefixEnd_7253580 3724573005839835568591399 := by
  unfold tailWord_7253580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132279898530762973841091097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176373198041017298454788129 132279898530762973841091097)
  ·
    refine ⟨99209923898072230380818323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132279898530762973841091097 99209923898072230380818323)
    ·
      refine ⟨148814885847108345571227485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99209923898072230380818323 148814885847108345571227485)
      ·
        refine ⟨55805582192665629589210307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148814885847108345571227485 55805582192665629589210307)
        ·
          refine ⟨83708373288998444383815461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55805582192665629589210307 83708373288998444383815461)
          ·
            refine ⟨15695319991687208321965399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83708373288998444383815461 15695319991687208321965399)
            ·
              refine ⟨23542979987530812482948099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695319991687208321965399 23542979987530812482948099)
              ·
                refine ⟨35314469981296218724422149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23542979987530812482948099 35314469981296218724422149)
                ·
                  refine ⟨6621463121493041010829153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35314469981296218724422149 6621463121493041010829153)
                  ·
                    refine ⟨4966097341119780758121865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621463121493041010829153 4966097341119780758121865)
                    ·
                      refine ⟨3724573005839835568591399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966097341119780758121865 3724573005839835568591399)
                      ·
                        rfl

theorem cell23_7253580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7253580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253580 prefixEnd_7253580 := by exact prefixLift 7253580
  have htrace : WordTrace (prefixWord ++ tailWord_7253580) baseStart_7253580 baseEnd_7253580 := by
    simpa [prefixWord, tailWord_7253580, baseEnd_7253580] using wordTrace_append hprefix tailTrace_7253580
  have hstable : (prefixWord ++ tailWord_7253580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253580).length < 2 ^ (prefixWord ++ tailWord_7253580).sum := by decide
  have hdescent : baseEnd_7253580 < baseStart_7253580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253586 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_7253586 : Nat := 118140960795 + 7253586 * 2 ^ 59
def prefixEnd_7253586 : Nat := 4983230072969 + 3 ^ 40 * 7253586 * 2
def baseEnd_7253586 : Nat := 413841787413751393901819

theorem tailTrace_7253586 : CollatzResearch.WordTrace tailWord_7253586 prefixEnd_7253586 413841787413751393901819 := by
  unfold tailWord_7253586
  simp only [CollatzResearch.WordTrace]
  refine ⟨66140003974876052676725153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176373343933002807137933741 66140003974876052676725153)
  ·
    refine ⟨49605002981157039507543865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66140003974876052676725153 49605002981157039507543865)
    ·
      refine ⟨37203752235867779630657899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49605002981157039507543865 37203752235867779630657899)
      ·
        refine ⟨55805628353801669445986849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203752235867779630657899 55805628353801669445986849)
        ·
          refine ⟨41854221265351252084490137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55805628353801669445986849 41854221265351252084490137)
          ·
            refine ⟨31390665949013439063367603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41854221265351252084490137 31390665949013439063367603)
            ·
              refine ⟨47085998923520158595051405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31390665949013439063367603 47085998923520158595051405)
              ·
                refine ⟨17657249596320059473144277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47085998923520158595051405 17657249596320059473144277)
                ·
                  refine ⟨413841787413751393901819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17657249596320059473144277 413841787413751393901819)
                  ·
                    rfl

theorem cell23_7253586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_7253586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253586 prefixEnd_7253586 := by exact prefixLift 7253586
  have htrace : WordTrace (prefixWord ++ tailWord_7253586) baseStart_7253586 baseEnd_7253586 := by
    simpa [prefixWord, tailWord_7253586, baseEnd_7253586] using wordTrace_append hprefix tailTrace_7253586
  have hstable : (prefixWord ++ tailWord_7253586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253586).length < 2 ^ (prefixWord ++ tailWord_7253586).sum := by decide
  have hdescent : baseEnd_7253586 < baseStart_7253586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253616 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_7253616 : Nat := 118140960795 + 7253616 * 2 ^ 59
def prefixEnd_7253616 : Nat := 4983230072969 + 3 ^ 40 * 7253616 * 2
def baseEnd_7253616 : Nat := 1241530497047799142580411

theorem tailTrace_7253616 : CollatzResearch.WordTrace tailWord_7253616 prefixEnd_7253616 1241530497047799142580411 := by
  unfold tailWord_7253616
  simp only [CollatzResearch.WordTrace]
  refine ⟨132280555044697762915246351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176374073392930350553661801 132280555044697762915246351)
  ·
    refine ⟨198420832567046644372869527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132280555044697762915246351 198420832567046644372869527)
    ·
      refine ⟨297631248850569966559304291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198420832567046644372869527 297631248850569966559304291)
      ·
        refine ⟨446446873275854949838956437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297631248850569966559304291 446446873275854949838956437)
        ·
          refine ⟨20927197184805700773701083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446446873275854949838956437 20927197184805700773701083)
          ·
            refine ⟨31390795777208551160551625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20927197184805700773701083 31390795777208551160551625)
            ·
              refine ⟨23543096832906413370413719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31390795777208551160551625 23543096832906413370413719)
              ·
                refine ⟨35314645249359620055620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23543096832906413370413719 35314645249359620055620579)
                ·
                  refine ⟨52971967874039430083430869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35314645249359620055620579 52971967874039430083430869)
                  ·
                    refine ⟨1241530497047799142580411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52971967874039430083430869 1241530497047799142580411)
                    ·
                      rfl

theorem cell23_7253616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_7253616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253616 prefixEnd_7253616 := by exact prefixLift 7253616
  have htrace : WordTrace (prefixWord ++ tailWord_7253616) baseStart_7253616 baseEnd_7253616 := by
    simpa [prefixWord, tailWord_7253616, baseEnd_7253616] using wordTrace_append hprefix tailTrace_7253616
  have hstable : (prefixWord ++ tailWord_7253616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253616).length < 2 ^ (prefixWord ++ tailWord_7253616).sum := by decide
  have hdescent : baseEnd_7253616 < baseStart_7253616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253619 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8]
def baseStart_7253619 : Nat := 118140960795 + 7253619 * 2 ^ 59
def prefixEnd_7253619 : Nat := 4983230072969 + 3 ^ 40 * 7253619 * 2
def baseEnd_7253619 : Nat := 3724593031585360916003719

theorem tailTrace_7253619 : CollatzResearch.WordTrace tailWord_7253619 prefixEnd_7253619 3724593031585360916003719 := by
  unfold tailWord_7253619
  simp only [CollatzResearch.WordTrace]
  refine ⟨264561219508384657342851911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176374146338923104895234607 264561219508384657342851911)
  ·
    refine ⟨396841829262576986014277867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264561219508384657342851911 396841829262576986014277867)
    ·
      refine ⟨595262743893865479021416801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396841829262576986014277867 595262743893865479021416801)
      ·
        refine ⟨446447057920399109266062601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595262743893865479021416801 446447057920399109266062601)
        ·
          refine ⟨334835293440299331949546951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446447057920399109266062601 334835293440299331949546951)
          ·
            refine ⟨502252940160448997924320427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334835293440299331949546951 502252940160448997924320427)
            ·
              refine ⟨753379410240673496886480641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502252940160448997924320427 753379410240673496886480641)
              ·
                refine ⟨565034557680505122664860481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753379410240673496886480641 565034557680505122664860481)
                ·
                  refine ⟨423775918260378841998645361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565034557680505122664860481 423775918260378841998645361)
                  ·
                    refine ⟨317831938695284131498984021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423775918260378841998645361 317831938695284131498984021)
                    ·
                      refine ⟨3724593031585360916003719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317831938695284131498984021 3724593031585360916003719)
                      ·
                        rfl

theorem cell23_7253619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_7253619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253619 prefixEnd_7253619 := by exact prefixLift 7253619
  have htrace : WordTrace (prefixWord ++ tailWord_7253619) baseStart_7253619 baseEnd_7253619 := by
    simpa [prefixWord, tailWord_7253619, baseEnd_7253619] using wordTrace_append hprefix tailTrace_7253619
  have hstable : (prefixWord ++ tailWord_7253619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253619).length < 2 ^ (prefixWord ++ tailWord_7253619).sum := by decide
  have hdescent : baseEnd_7253619 < baseStart_7253619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253633 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7253633 : Nat := 118140960795 + 7253633 * 2 ^ 59
def prefixEnd_7253633 : Nat := 4983230072969 + 3 ^ 40 * 7253633 * 2
def baseEnd_7253633 : Nat := 1241533406771507953742885

theorem tailTrace_7253633 : CollatzResearch.WordTrace tailWord_7253633 prefixEnd_7253633 1241533406771507953742885 := by
  unfold tailWord_7253633
  simp only [CollatzResearch.WordTrace]
  refine ⟨264561730130333937733861553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176374486753555958489241035 264561730130333937733861553)
  ·
    refine ⟨198421297597750453300396165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264561730130333937733861553 198421297597750453300396165)
    ·
      refine ⟨37203993299578209993824281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198421297597750453300396165 37203993299578209993824281)
      ·
        refine ⟨27902994974683657495368211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37203993299578209993824281 27902994974683657495368211)
        ·
          refine ⟨41854492462025486243052317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902994974683657495368211 41854492462025486243052317)
          ·
            refine ⟨15695434673259557341144619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41854492462025486243052317 15695434673259557341144619)
            ·
              refine ⟨23543152009889336011716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695434673259557341144619 23543152009889336011716929)
              ·
                refine ⟨17657364007417002008787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23543152009889336011716929 17657364007417002008787697)
                ·
                  refine ⟨13243023005562751506590773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17657364007417002008787697 13243023005562751506590773)
                  ·
                    refine ⟨1241533406771507953742885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13243023005562751506590773 1241533406771507953742885)
                    ·
                      rfl

theorem cell23_7253633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7253633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253633 prefixEnd_7253633 := by exact prefixLift 7253633
  have htrace : WordTrace (prefixWord ++ tailWord_7253633) baseStart_7253633 baseEnd_7253633 := by
    simpa [prefixWord, tailWord_7253633, baseEnd_7253633] using wordTrace_append hprefix tailTrace_7253633
  have hstable : (prefixWord ++ tailWord_7253633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253633).length < 2 ^ (prefixWord ++ tailWord_7253633).sum := by decide
  have hdescent : baseEnd_7253633 < baseStart_7253633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253653 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_7253653 : Nat := 118140960795 + 7253653 * 2 ^ 59
def prefixEnd_7253653 : Nat := 4983230072969 + 3 ^ 40 * 7253653 * 2
def baseEnd_7253653 : Nat := 3724610489927613782978563

theorem tailTrace_7253653 : CollatzResearch.WordTrace tailWord_7253653 prefixEnd_7253653 3724610489927613782978563 := by
  unfold tailWord_7253653
  simp only [CollatzResearch.WordTrace]
  refine ⟨264562459590261481149589613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176374973060174320766393075 264562459590261481149589613)
  ·
    refine ⟨99210922346348055431096105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264562459590261481149589613 99210922346348055431096105)
    ·
      refine ⟨74408191759761041573322079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99210922346348055431096105 74408191759761041573322079)
      ·
        refine ⟨111612287639641562359983119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74408191759761041573322079 111612287639641562359983119)
        ·
          refine ⟨167418431459462343539974679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111612287639641562359983119 167418431459462343539974679)
          ·
            refine ⟨251127647189193515309962019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167418431459462343539974679 251127647189193515309962019)
            ·
              refine ⟨376691470783790272964943029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251127647189193515309962019 376691470783790272964943029)
              ·
                refine ⟨35314825385980338090463409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376691470783790272964943029 35314825385980338090463409)
                ·
                  refine ⟨26486119039485253567847557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35314825385980338090463409 26486119039485253567847557)
                  ·
                    refine ⟨4966147319903485043971417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26486119039485253567847557 4966147319903485043971417)
                    ·
                      refine ⟨3724610489927613782978563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966147319903485043971417 3724610489927613782978563)
                      ·
                        rfl

theorem cell23_7253653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_7253653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253653 prefixEnd_7253653 := by exact prefixLift 7253653
  have htrace : WordTrace (prefixWord ++ tailWord_7253653) baseStart_7253653 baseEnd_7253653 := by
    simpa [prefixWord, tailWord_7253653, baseEnd_7253653] using wordTrace_append hprefix tailTrace_7253653
  have hstable : (prefixWord ++ tailWord_7253653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253653).length < 2 ^ (prefixWord ++ tailWord_7253653).sum := by decide
  have hdescent : baseEnd_7253653 < baseStart_7253653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253693 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 6]
def baseStart_7253693 : Nat := 118140960795 + 7253693 * 2 ^ 59
def prefixEnd_7253693 : Nat := 4983230072969 + 3 ^ 40 * 7253693 * 2
def baseEnd_7253693 : Nat := 413847892128199291830931

theorem tailTrace_7253693 : CollatzResearch.WordTrace tailWord_7253693 prefixEnd_7253693 413847892128199291830931 := by
  unfold tailWord_7253693
  simp only [CollatzResearch.WordTrace]
  refine ⟨264563918510116567981045733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176375945673411045320697155 264563918510116567981045733)
  ·
    refine ⟨49605734720646856496446075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264563918510116567981045733 49605734720646856496446075)
    ·
      refine ⟨74408602080970284744669113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49605734720646856496446075 74408602080970284744669113)
      ·
        refine ⟨55806451560727713558501835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74408602080970284744669113 55806451560727713558501835)
        ·
          refine ⟨83709677341091570337752753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55806451560727713558501835 83709677341091570337752753)
          ·
            refine ⟨62782258005818677753314565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83709677341091570337752753 62782258005818677753314565)
            ·
              refine ⟨11771673376091002078746481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62782258005818677753314565 11771673376091002078746481)
              ·
                refine ⟨8828755032068251559059861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11771673376091002078746481 8828755032068251559059861)
                ·
                  refine ⟨413847892128199291830931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8828755032068251559059861 413847892128199291830931)
                  ·
                    rfl

theorem cell23_7253693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_7253693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253693 prefixEnd_7253693 := by exact prefixLift 7253693
  have htrace : WordTrace (prefixWord ++ tailWord_7253693) baseStart_7253693 baseEnd_7253693 := by
    simpa [prefixWord, tailWord_7253693, baseEnd_7253693] using wordTrace_append hprefix tailTrace_7253693
  have hstable : (prefixWord ++ tailWord_7253693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253693).length < 2 ^ (prefixWord ++ tailWord_7253693).sum := by decide
  have hdescent : baseEnd_7253693 < baseStart_7253693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253696 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_7253696 : Nat := 118140960795 + 7253696 * 2 ^ 59
def prefixEnd_7253696 : Nat := 4983230072969 + 3 ^ 40 * 7253696 * 2
def baseEnd_7253696 : Nat := 3724632569595757114740865

theorem tailTrace_7253696 : CollatzResearch.WordTrace tailWord_7253696 prefixEnd_7253696 3724632569595757114740865 := by
  unfold tailWord_7253696
  simp only [CollatzResearch.WordTrace]
  refine ⟨132282013964552849746702471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176376018619403799662269961 132282013964552849746702471)
  ·
    refine ⟨198423020946829274620053707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132282013964552849746702471 198423020946829274620053707)
    ·
      refine ⟨297634531420243911930080561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198423020946829274620053707 297634531420243911930080561)
      ·
        refine ⟨223225898565182933947560421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297634531420243911930080561 223225898565182933947560421)
        ·
          refine ⟨41854855980971800115167579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223225898565182933947560421 41854855980971800115167579)
          ·
            refine ⟨62782283971457700172751369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41854855980971800115167579 62782283971457700172751369)
            ·
              refine ⟨47086712978593275129563527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62782283971457700172751369 47086712978593275129563527)
              ·
                refine ⟨70630069467889912694345291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47086712978593275129563527 70630069467889912694345291)
                ·
                  refine ⟨105945104201834869041517937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70630069467889912694345291 105945104201834869041517937)
                  ·
                    refine ⟨79458828151376151781138453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105945104201834869041517937 79458828151376151781138453)
                    ·
                      refine ⟨3724632569595757114740865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79458828151376151781138453 3724632569595757114740865)
                      ·
                        rfl

theorem cell23_7253696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_7253696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253696 prefixEnd_7253696 := by exact prefixLift 7253696
  have htrace : WordTrace (prefixWord ++ tailWord_7253696) baseStart_7253696 baseEnd_7253696 := by
    simpa [prefixWord, tailWord_7253696, baseEnd_7253696] using wordTrace_append hprefix tailTrace_7253696
  have hstable : (prefixWord ++ tailWord_7253696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253696).length < 2 ^ (prefixWord ++ tailWord_7253696).sum := by decide
  have hdescent : baseEnd_7253696 < baseStart_7253696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253720 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_7253720 : Nat := 118140960795 + 7253720 * 2 ^ 59
def prefixEnd_7253720 : Nat := 4983230072969 + 3 ^ 40 * 7253720 * 2
def baseEnd_7253720 : Nat := 3724644893131465020840755

theorem tailTrace_7253720 : CollatzResearch.WordTrace tailWord_7253720 prefixEnd_7253720 3724644893131465020840755 := by
  unfold tailWord_7253720
  simp only [CollatzResearch.WordTrace]
  refine ⟨132282451640509375796139307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176376602187345834394852409 132282451640509375796139307)
  ·
    refine ⟨198423677460764063694208961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132282451640509375796139307 198423677460764063694208961)
    ·
      refine ⟨148817758095573047770656721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198423677460764063694208961 148817758095573047770656721)
      ·
        refine ⟨111613318571679785827992541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148817758095573047770656721 111613318571679785827992541)
        ·
          refine ⟨41854994464379919685497203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111613318571679785827992541 41854994464379919685497203)
          ·
            refine ⟨62782491696569879528245805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41854994464379919685497203 62782491696569879528245805)
            ·
              refine ⟨23543434386213704823092177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62782491696569879528245805 23543434386213704823092177)
              ·
                refine ⟨17657575789660278617319133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23543434386213704823092177 17657575789660278617319133)
                ·
                  refine ⟨6621590921122604481494675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17657575789660278617319133 6621590921122604481494675)
                  ·
                    refine ⟨9932386381683906722242013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621590921122604481494675 9932386381683906722242013)
                    ·
                      refine ⟨3724644893131465020840755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932386381683906722242013 3724644893131465020840755)
                      ·
                        rfl

theorem cell23_7253720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_7253720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253720 prefixEnd_7253720 := by exact prefixLift 7253720
  have htrace : WordTrace (prefixWord ++ tailWord_7253720) baseStart_7253720 baseEnd_7253720 := by
    simpa [prefixWord, tailWord_7253720, baseEnd_7253720] using wordTrace_append hprefix tailTrace_7253720
  have hstable : (prefixWord ++ tailWord_7253720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253720).length < 2 ^ (prefixWord ++ tailWord_7253720).sum := by decide
  have hdescent : baseEnd_7253720 < baseStart_7253720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253724 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7253724 : Nat := 118140960795 + 7253724 * 2 ^ 59
def prefixEnd_7253724 : Nat := 4983230072969 + 3 ^ 40 * 7253724 * 2
def baseEnd_7253724 : Nat := 3724646947054083005190737

theorem tailTrace_7253724 : CollatzResearch.WordTrace tailWord_7253724 prefixEnd_7253724 3724646947054083005190737 := by
  unfold tailWord_7253724
  simp only [CollatzResearch.WordTrace]
  refine ⟨132282524586502130137712113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176376699448669506850282817 132282524586502130137712113)
  ·
    refine ⟨99211893439876597603284085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132282524586502130137712113 99211893439876597603284085)
    ·
      refine ⟨9301115009988431025307883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99211893439876597603284085 9301115009988431025307883)
      ·
        refine ⟨13951672514982646537961825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301115009988431025307883 13951672514982646537961825)
        ·
          refine ⟨10463754386236984903471369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13951672514982646537961825 10463754386236984903471369)
          ·
            refine ⟨7847815789677738677603527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10463754386236984903471369 7847815789677738677603527)
            ·
              refine ⟨11771723684516608016405291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847815789677738677603527 11771723684516608016405291)
              ·
                refine ⟨17657585526774912024607937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11771723684516608016405291 17657585526774912024607937)
                ·
                  refine ⟨13243189145081184018455953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17657585526774912024607937 13243189145081184018455953)
                  ·
                    refine ⟨9932391858810888013841965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13243189145081184018455953 9932391858810888013841965)
                    ·
                      refine ⟨3724646947054083005190737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932391858810888013841965 3724646947054083005190737)
                      ·
                        rfl

theorem cell23_7253724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7253724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253724 prefixEnd_7253724 := by exact prefixLift 7253724
  have htrace : WordTrace (prefixWord ++ tailWord_7253724) baseStart_7253724 baseEnd_7253724 := by
    simpa [prefixWord, tailWord_7253724, baseEnd_7253724] using wordTrace_append hprefix tailTrace_7253724
  have hstable : (prefixWord ++ tailWord_7253724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253724).length < 2 ^ (prefixWord ++ tailWord_7253724).sum := by decide
  have hdescent : baseEnd_7253724 < baseStart_7253724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253740 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_7253740 : Nat := 118140960795 + 7253740 * 2 ^ 59
def prefixEnd_7253740 : Nat := 4983230072969 + 3 ^ 40 * 7253740 * 2
def baseEnd_7253740 : Nat := 1241551720914851647530221

theorem tailTrace_7253740 : CollatzResearch.WordTrace tailWord_7253740 prefixEnd_7253740 1241551720914851647530221 := by
  unfold tailWord_7253740
  simp only [CollatzResearch.WordTrace]
  refine ⟨132282816370473147504003337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176377088493964196672004449 132282816370473147504003337)
  ·
    refine ⟨99212112277854860628002503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132282816370473147504003337 99212112277854860628002503)
    ·
      refine ⟨148818168416782290942003755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99212112277854860628002503 148818168416782290942003755)
      ·
        refine ⟨223227252625173436413005633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148818168416782290942003755 223227252625173436413005633)
        ·
          refine ⟨167420439468880077309754225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223227252625173436413005633 167420439468880077309754225)
          ·
            refine ⟨125565329601660057982315669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167420439468880077309754225 125565329601660057982315669)
            ·
              refine ⟨5885874825077815217921047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125565329601660057982315669 5885874825077815217921047)
              ·
                refine ⟨8828812237616722826881571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885874825077815217921047 8828812237616722826881571)
                ·
                  refine ⟨13243218356425084240322357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8828812237616722826881571 13243218356425084240322357)
                  ·
                    refine ⟨1241551720914851647530221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13243218356425084240322357 1241551720914851647530221)
                    ·
                      rfl

theorem cell23_7253740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_7253740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253740 prefixEnd_7253740 := by exact prefixLift 7253740
  have htrace : WordTrace (prefixWord ++ tailWord_7253740) baseStart_7253740 baseEnd_7253740 := by
    simpa [prefixWord, tailWord_7253740, baseEnd_7253740] using wordTrace_append hprefix tailTrace_7253740
  have hstable : (prefixWord ++ tailWord_7253740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253740).length < 2 ^ (prefixWord ++ tailWord_7253740).sum := by decide
  have hdescent : baseEnd_7253740 < baseStart_7253740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2]
def baseStart_7253760 : Nat := 118140960795 + 7253760 * 2 ^ 59
def prefixEnd_7253760 : Nat := 4983230072969 + 3 ^ 40 * 7253760 * 2
def baseEnd_7253760 : Nat := 3724665432357644864340571

theorem tailTrace_7253760 : CollatzResearch.WordTrace tailWord_7253760 prefixEnd_7253760 3724665432357644864340571 := by
  unfold tailWord_7253760
  simp only [CollatzResearch.WordTrace]
  refine ⟨132283181100436919211867367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176377574800582558949156489 132283181100436919211867367)
  ·
    refine ⟨198424771650655378817801051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132283181100436919211867367 198424771650655378817801051)
    ·
      refine ⟨297637157475983068226701577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198424771650655378817801051 297637157475983068226701577)
      ·
        refine ⟨223227868106987301170026183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297637157475983068226701577 223227868106987301170026183)
        ·
          refine ⟨334841802160480951755039275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223227868106987301170026183 334841802160480951755039275)
          ·
            refine ⟨502262703240721427632558913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334841802160480951755039275 502262703240721427632558913)
            ·
              refine ⟨376697027430541070724419185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502262703240721427632558913 376697027430541070724419185)
              ·
                refine ⟨282522770572905803043314389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376697027430541070724419185 282522770572905803043314389)
                ·
                  refine ⟨6621627435302479758827681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 282522770572905803043314389 6621627435302479758827681)
                  ·
                    refine ⟨4966220576476859819120761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621627435302479758827681 4966220576476859819120761)
                    ·
                      refine ⟨3724665432357644864340571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966220576476859819120761 3724665432357644864340571)
                      ·
                        rfl

theorem cell23_7253760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_7253760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253760 prefixEnd_7253760 := by exact prefixLift 7253760
  have htrace : WordTrace (prefixWord ++ tailWord_7253760) baseStart_7253760 baseEnd_7253760 := by
    simpa [prefixWord, tailWord_7253760, baseEnd_7253760] using wordTrace_append hprefix tailTrace_7253760
  have hstable : (prefixWord ++ tailWord_7253760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253760).length < 2 ^ (prefixWord ++ tailWord_7253760).sum := by decide
  have hdescent : baseEnd_7253760 < baseStart_7253760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253763 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3]
def baseStart_7253763 : Nat := 118140960795 + 7253763 * 2 ^ 59
def prefixEnd_7253763 : Nat := 4983230072969 + 3 ^ 40 * 7253763 * 2
def baseEnd_7253763 : Nat := 3724666972799608352603057

theorem tailTrace_7253763 : CollatzResearch.WordTrace tailWord_7253763 prefixEnd_7253763 3724666972799608352603057 := by
  unfold tailWord_7253763
  simp only [CollatzResearch.WordTrace]
  refine ⟨264566471619862969936093943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176377647746575313290729295 264566471619862969936093943)
  ·
    refine ⟨396849707429794454904140915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264566471619862969936093943 396849707429794454904140915)
    ·
      refine ⟨595274561144691682356211373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396849707429794454904140915 595274561144691682356211373)
      ·
        refine ⟨223227960429259380883579265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595274561144691682356211373 223227960429259380883579265)
        ·
          refine ⟨167420970321944535662684449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223227960429259380883579265 167420970321944535662684449)
          ·
            refine ⟨125565727741458401747013337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167420970321944535662684449 125565727741458401747013337)
            ·
              refine ⟨94174295806093801310260003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125565727741458401747013337 94174295806093801310260003)
              ·
                refine ⟨141261443709140701965390005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94174295806093801310260003 141261443709140701965390005)
                ·
                  refine ⟨13243260347731940809255313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141261443709140701965390005 13243260347731940809255313)
                  ·
                    refine ⟨9932445260798955606941485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13243260347731940809255313 9932445260798955606941485)
                    ·
                      refine ⟨3724666972799608352603057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932445260798955606941485 3724666972799608352603057)
                      ·
                        rfl

theorem cell23_7253763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_7253763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253763 prefixEnd_7253763 := by exact prefixLift 7253763
  have htrace : WordTrace (prefixWord ++ tailWord_7253763) baseStart_7253763 baseEnd_7253763 := by
    simpa [prefixWord, tailWord_7253763, baseEnd_7253763] using wordTrace_append hprefix tailTrace_7253763
  have hstable : (prefixWord ++ tailWord_7253763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253763).length < 2 ^ (prefixWord ++ tailWord_7253763).sum := by decide
  have hdescent : baseEnd_7253763 < baseStart_7253763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253770 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_7253770 : Nat := 118140960795 + 7253770 * 2 ^ 59
def prefixEnd_7253770 : Nat := 4983230072969 + 3 ^ 40 * 7253770 * 2
def baseEnd_7253770 : Nat := 1241556855721396608405175

theorem tailTrace_7253770 : CollatzResearch.WordTrace tailWord_7253770 prefixEnd_7253770 1241556855721396608405175 := by
  unfold tailWord_7253770
  simp only [CollatzResearch.WordTrace]
  refine ⟨66141681732709402532899691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176377817953891740087732509 66141681732709402532899691)
  ·
    refine ⟨99212522599064103799349537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66141681732709402532899691 99212522599064103799349537)
    ·
      refine ⟨74409391949298077849512153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99212522599064103799349537 74409391949298077849512153)
      ·
        refine ⟨55807043961973558387134115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74409391949298077849512153 55807043961973558387134115)
        ·
          refine ⟨83710565942960337580701173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55807043961973558387134115 83710565942960337580701173)
          ·
            refine ⟨7847865557152531648190735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83710565942960337580701173 7847865557152531648190735)
            ·
              refine ⟨11771798335728797472286103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847865557152531648190735 11771798335728797472286103)
              ·
                refine ⟨17657697503593196208429155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11771798335728797472286103 17657697503593196208429155)
                ·
                  refine ⟨26486546255389794312643733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17657697503593196208429155 26486546255389794312643733)
                  ·
                    refine ⟨1241556855721396608405175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26486546255389794312643733 1241556855721396608405175)
                    ·
                      rfl

theorem cell23_7253770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_7253770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253770 prefixEnd_7253770 := by exact prefixLift 7253770
  have htrace : WordTrace (prefixWord ++ tailWord_7253770) baseStart_7253770 baseEnd_7253770 := by
    simpa [prefixWord, tailWord_7253770, baseEnd_7253770] using wordTrace_append hprefix tailTrace_7253770
  have hstable : (prefixWord ++ tailWord_7253770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253770).length < 2 ^ (prefixWord ++ tailWord_7253770).sum := by decide
  have hdescent : baseEnd_7253770 < baseStart_7253770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253783 : List Nat := [1, 1, 3, 4, 2, 2, 1, 9]
def baseStart_7253783 : Nat := 118140960795 + 7253783 * 2 ^ 59
def prefixEnd_7253783 : Nat := 4983230072969 + 3 ^ 40 * 7253783 * 2
def baseEnd_7253783 : Nat := 137951008978248084235295

theorem tailTrace_7253783 : CollatzResearch.WordTrace tailWord_7253783 prefixEnd_7253783 137951008978248084235295 := by
  unfold tailWord_7253783
  simp only [CollatzResearch.WordTrace]
  refine ⟨264567201079790513351822003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176378134053193675567881335 264567201079790513351822003)
  ·
    refine ⟨396850801619685770027733005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264567201079790513351822003 396850801619685770027733005)
    ·
      refine ⟨148819050607382163760399877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396850801619685770027733005 148819050607382163760399877)
      ·
        refine ⟨27903571988884155705074977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148819050607382163760399877 27903571988884155705074977)
        ·
          refine ⟨20927678991663116778806233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27903571988884155705074977 20927678991663116778806233)
          ·
            refine ⟨15695759243747337584104675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20927678991663116778806233 15695759243747337584104675)
            ·
              refine ⟨23543638865621006376157013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695759243747337584104675 23543638865621006376157013)
              ·
                refine ⟨137951008978248084235295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23543638865621006376157013 137951008978248084235295)
                ·
                  rfl

theorem cell23_7253783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 9].length) (baseStart_7253783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253783 prefixEnd_7253783 := by exact prefixLift 7253783
  have htrace : WordTrace (prefixWord ++ tailWord_7253783) baseStart_7253783 baseEnd_7253783 := by
    simpa [prefixWord, tailWord_7253783, baseEnd_7253783] using wordTrace_append hprefix tailTrace_7253783
  have hstable : (prefixWord ++ tailWord_7253783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253783).length < 2 ^ (prefixWord ++ tailWord_7253783).sum := by decide
  have hdescent : baseEnd_7253783 < baseStart_7253783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253811 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 3, 2, 2]
def baseStart_7253811 : Nat := 118140960795 + 7253811 * 2 ^ 59
def prefixEnd_7253811 : Nat := 4983230072969 + 3 ^ 40 * 7253811 * 2
def baseEnd_7253811 : Nat := 3724691619871024164802837

theorem tailTrace_7253811 : CollatzResearch.WordTrace tailWord_7253811 prefixEnd_7253811 3724691619871024164802837 := by
  unfold tailWord_7253811
  simp only [CollatzResearch.WordTrace]
  refine ⟨264568222323689074133841287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176378814882459382755894191 264568222323689074133841287)
  ·
    refine ⟨396852333485533611200761931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264568222323689074133841287 396852333485533611200761931)
    ·
      refine ⟨595278500228300416801142897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396852333485533611200761931 595278500228300416801142897)
      ·
        refine ⟨446458875171225312600857173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595278500228300416801142897 446458875171225312600857173)
        ·
          refine ⟨5231939943412796632041295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 446458875171225312600857173 5231939943412796632041295)
          ·
            refine ⟨7847909915119194948061943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231939943412796632041295 7847909915119194948061943)
            ·
              refine ⟨11771864872678792422092915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847909915119194948061943 11771864872678792422092915)
              ·
                refine ⟨17657797309018188633139373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11771864872678792422092915 17657797309018188633139373)
                ·
                  refine ⟨6621673990881820737427265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17657797309018188633139373 6621673990881820737427265)
                  ·
                    refine ⟨4966255493161365553070449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621673990881820737427265 4966255493161365553070449)
                    ·
                      refine ⟨3724691619871024164802837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966255493161365553070449 3724691619871024164802837)
                      ·
                        rfl

theorem cell23_7253811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 3, 2, 2].length) (baseStart_7253811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253811 prefixEnd_7253811 := by exact prefixLift 7253811
  have htrace : WordTrace (prefixWord ++ tailWord_7253811) baseStart_7253811 baseEnd_7253811 := by
    simpa [prefixWord, tailWord_7253811, baseEnd_7253811] using wordTrace_append hprefix tailTrace_7253811
  have hstable : (prefixWord ++ tailWord_7253811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253811).length < 2 ^ (prefixWord ++ tailWord_7253811).sum := by decide
  have hdescent : baseEnd_7253811 < baseStart_7253811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253827 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 3]
def baseStart_7253827 : Nat := 118140960795 + 7253827 * 2 ^ 59
def prefixEnd_7253827 : Nat := 4983230072969 + 3 ^ 40 * 7253827 * 2
def baseEnd_7253827 : Nat := 3724699835561496102202763

theorem tailTrace_7253827 : CollatzResearch.WordTrace tailWord_7253827 prefixEnd_7253827 3724699835561496102202763 := by
  unfold tailWord_7253827
  simp only [CollatzResearch.WordTrace]
  refine ⟨264568805891631108866423735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176379203927754072577615823 264568805891631108866423735)
  ·
    refine ⟨396853208837446663299635603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264568805891631108866423735 396853208837446663299635603)
    ·
      refine ⟨595279813256169994949453405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396853208837446663299635603 595279813256169994949453405)
      ·
        refine ⟨223229929971063748106045027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595279813256169994949453405 223229929971063748106045027)
        ·
          refine ⟨334844894956595622159067541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223229929971063748106045027 334844894956595622159067541)
          ·
            refine ⟨15695854451090419788706291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334844894956595622159067541 15695854451090419788706291)
            ·
              refine ⟨23543781676635629683059437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695854451090419788706291 23543781676635629683059437)
              ·
                refine ⟨8828918128738361131147289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23543781676635629683059437 8828918128738361131147289)
                ·
                  refine ⟨6621688596553770848360467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828918128738361131147289 6621688596553770848360467)
                  ·
                    refine ⟨9932532894830656272540701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621688596553770848360467 9932532894830656272540701)
                    ·
                      refine ⟨3724699835561496102202763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932532894830656272540701 3724699835561496102202763)
                      ·
                        rfl

theorem cell23_7253827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_7253827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253827 prefixEnd_7253827 := by exact prefixLift 7253827
  have htrace : WordTrace (prefixWord ++ tailWord_7253827) baseStart_7253827 baseEnd_7253827 := by
    simpa [prefixWord, tailWord_7253827, baseEnd_7253827] using wordTrace_append hprefix tailTrace_7253827
  have hstable : (prefixWord ++ tailWord_7253827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253827).length < 2 ^ (prefixWord ++ tailWord_7253827).sum := by decide
  have hdescent : baseEnd_7253827 < baseStart_7253827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253873 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 7]
def baseStart_7253873 : Nat := 118140960795 + 7253873 * 2 ^ 59
def prefixEnd_7253873 : Nat := 4983230072969 + 3 ^ 40 * 7253873 * 2
def baseEnd_7253873 : Nat := 413858161741289213580839

theorem tailTrace_7253873 : CollatzResearch.WordTrace tailWord_7253873 prefixEnd_7253873 413858161741289213580839 := by
  unfold tailWord_7253873
  simp only [CollatzResearch.WordTrace]
  refine ⟨264570483649464458722598273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176380322432976305815065515 264570483649464458722598273)
  ·
    refine ⟨198427862737098344041948705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264570483649464458722598273 198427862737098344041948705)
    ·
      refine ⟨148820897052823758031461529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198427862737098344041948705 148820897052823758031461529)
      ·
        refine ⟨111615672789617818523596147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148820897052823758031461529 111615672789617818523596147)
        ·
          refine ⟨167423509184426727785394221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111615672789617818523596147 167423509184426727785394221)
          ·
            refine ⟨62783815944160022919522833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167423509184426727785394221 62783815944160022919522833)
            ·
              refine ⟨47087861958120017189642125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62783815944160022919522833 47087861958120017189642125)
              ·
                refine ⟨17657948234295006446115797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47087861958120017189642125 17657948234295006446115797)
                ·
                  refine ⟨413858161741289213580839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17657948234295006446115797 413858161741289213580839)
                  ·
                    rfl

theorem cell23_7253873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_7253873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253873 prefixEnd_7253873 := by exact prefixLift 7253873
  have htrace : WordTrace (prefixWord ++ tailWord_7253873) baseStart_7253873 baseEnd_7253873 := by
    simpa [prefixWord, tailWord_7253873, baseEnd_7253873] using wordTrace_append hprefix tailTrace_7253873
  have hstable : (prefixWord ++ tailWord_7253873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253873).length < 2 ^ (prefixWord ++ tailWord_7253873).sum := by decide
  have hdescent : baseEnd_7253873 < baseStart_7253873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253913 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7253913 : Nat := 118140960795 + 7253913 * 2 ^ 59
def prefixEnd_7253913 : Nat := 4983230072969 + 3 ^ 40 * 7253913 * 2
def baseEnd_7253913 : Nat := 3724743994897782765727367

theorem tailTrace_7253913 : CollatzResearch.WordTrace tailWord_7253913 prefixEnd_7253913 3724743994897782765727367 := by
  unfold tailWord_7253913
  simp only [CollatzResearch.WordTrace]
  refine ⟨264571942569319545554054393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176381295046213030369369595 264571942569319545554054393)
  ·
    refine ⟨198428956926989659165540795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264571942569319545554054393 198428956926989659165540795)
    ·
      refine ⟨297643435390484488748311193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198428956926989659165540795 297643435390484488748311193)
      ·
        refine ⟨223232576542863366561233395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297643435390484488748311193 223232576542863366561233395)
        ·
          refine ⟨334848864814295049841850093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223232576542863366561233395 334848864814295049841850093)
          ·
            refine ⟨125568324305360643690693785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334848864814295049841850093 125568324305360643690693785)
            ·
              refine ⟨94176243229020482768020339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125568324305360643690693785 94176243229020482768020339)
              ·
                refine ⟨141264364843530724152030509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94176243229020482768020339 141264364843530724152030509)
                ·
                  refine ⟨52974136816324021557011441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141264364843530724152030509 52974136816324021557011441)
                  ·
                    refine ⟨39730602612243016167758581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52974136816324021557011441 39730602612243016167758581)
                    ·
                      refine ⟨3724743994897782765727367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39730602612243016167758581 3724743994897782765727367)
                      ·
                        rfl

theorem cell23_7253913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7253913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253913 prefixEnd_7253913 := by exact prefixLift 7253913
  have htrace : WordTrace (prefixWord ++ tailWord_7253913) baseStart_7253913 baseEnd_7253913 := by
    simpa [prefixWord, tailWord_7253913, baseEnd_7253913] using wordTrace_append hprefix tailTrace_7253913
  have hstable : (prefixWord ++ tailWord_7253913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253913).length < 2 ^ (prefixWord ++ tailWord_7253913).sum := by decide
  have hdescent : baseEnd_7253913 < baseStart_7253913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253918 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7253918 : Nat := 118140960795 + 7253918 * 2 ^ 59
def prefixEnd_7253918 : Nat := 4983230072969 + 3 ^ 40 * 7253918 * 2
def baseEnd_7253918 : Nat := 3724746562301055246164845

theorem tailTrace_7253918 : CollatzResearch.WordTrace tailWord_7253918 prefixEnd_7253918 3724746562301055246164845 := by
  unfold tailWord_7253918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33071515616787678925998301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176381416622867620938657605 33071515616787678925998301)
  ·
    refine ⟨12401818356295379597249363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33071515616787678925998301 12401818356295379597249363)
    ·
      refine ⟨18602727534443069395874045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12401818356295379597249363 18602727534443069395874045)
      ·
        refine ⟨6976022825416151023452767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18602727534443069395874045 6976022825416151023452767)
        ·
          refine ⟨10464034238124226535179151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976022825416151023452767 10464034238124226535179151)
          ·
            refine ⟨15696051357186339802768727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464034238124226535179151 15696051357186339802768727)
            ·
              refine ⟨23544077035779509704153091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15696051357186339802768727 23544077035779509704153091)
              ·
                refine ⟨35316115553669264556229637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23544077035779509704153091 35316115553669264556229637)
                ·
                  refine ⟨6621771666312987104293057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35316115553669264556229637 6621771666312987104293057)
                  ·
                    refine ⟨4966328749734740328219793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621771666312987104293057 4966328749734740328219793)
                    ·
                      refine ⟨3724746562301055246164845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966328749734740328219793 3724746562301055246164845)
                      ·
                        rfl

theorem cell23_7253918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7253918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253918 prefixEnd_7253918 := by exact prefixLift 7253918
  have htrace : WordTrace (prefixWord ++ tailWord_7253918) baseStart_7253918 baseEnd_7253918 := by
    simpa [prefixWord, tailWord_7253918, baseEnd_7253918] using wordTrace_append hprefix tailTrace_7253918
  have hstable : (prefixWord ++ tailWord_7253918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253918).length < 2 ^ (prefixWord ++ tailWord_7253918).sum := by decide
  have hdescent : baseEnd_7253918 < baseStart_7253918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7253963 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 10]
def baseStart_7253963 : Nat := 118140960795 + 7253963 * 2 ^ 59
def prefixEnd_7253963 : Nat := 4983230072969 + 3 ^ 40 * 7253963 * 2
def baseEnd_7253963 : Nat := 413863296547834174455793

theorem tailTrace_7253963 : CollatzResearch.WordTrace tailWord_7253963 prefixEnd_7253963 413863296547834174455793 := by
  unfold tailWord_7253963
  simp only [CollatzResearch.WordTrace]
  refine ⟨264573766219138404093374543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176382510812758936062249695 264573766219138404093374543)
  ·
    refine ⟨396860649328707606140061815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264573766219138404093374543 396860649328707606140061815)
    ·
      refine ⟨595290973993061409210092723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396860649328707606140061815 595290973993061409210092723)
      ·
        refine ⟨892936460989592113815139085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595290973993061409210092723 892936460989592113815139085)
        ·
          refine ⟨334851172871097042680677157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892936460989592113815139085 334851172871097042680677157)
          ·
            refine ⟨62784594913330695502626967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334851172871097042680677157 62784594913330695502626967)
            ·
              refine ⟨94176892369996043253940451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62784594913330695502626967 94176892369996043253940451)
              ·
                refine ⟨141265338554994064880910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94176892369996043253940451 141265338554994064880910677)
                ·
                  refine ⟨413863296547834174455793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141265338554994064880910677 413863296547834174455793)
                  ·
                    rfl

theorem cell23_7253963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 10].length) (baseStart_7253963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7253963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7253963 prefixEnd_7253963 := by exact prefixLift 7253963
  have htrace : WordTrace (prefixWord ++ tailWord_7253963) baseStart_7253963 baseEnd_7253963 := by
    simpa [prefixWord, tailWord_7253963, baseEnd_7253963] using wordTrace_append hprefix tailTrace_7253963
  have hstable : (prefixWord ++ tailWord_7253963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7253963).length < 2 ^ (prefixWord ++ tailWord_7253963).sum := by decide
  have hdescent : baseEnd_7253963 < baseStart_7253963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7253963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254040 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_7254040 : Nat := 118140960795 + 7254040 * 2 ^ 59
def prefixEnd_7254040 : Nat := 4983230072969 + 3 ^ 40 * 7254040 * 2
def baseEnd_7254040 : Nat := 1241603068980301256279761

theorem tailTrace_7254040 : CollatzResearch.WordTrace tailWord_7254040 prefixEnd_7254040 1241603068980301256279761 := by
  unfold tailWord_7254040
  simp only [CollatzResearch.WordTrace]
  refine ⟨132288287319929723121963787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176384383093239630829285049 132288287319929723121963787)
  ·
    refine ⟨198432430979894584682945681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132288287319929723121963787 198432430979894584682945681)
    ·
      refine ⟨148824323234920938512209261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198432430979894584682945681 148824323234920938512209261)
      ·
        refine ⟨55809121213095351942078473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148824323234920938512209261 55809121213095351942078473)
        ·
          refine ⟨41856840909821513956558855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55809121213095351942078473 41856840909821513956558855)
          ·
            refine ⟨62785261364732270934838283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41856840909821513956558855 62785261364732270934838283)
            ·
              refine ⟨94177892047098406402257425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62785261364732270934838283 94177892047098406402257425)
              ·
                refine ⟨70633419035323804801693069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94177892047098406402257425 70633419035323804801693069)
                ·
                  refine ⟨26487532138246426800634901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70633419035323804801693069 26487532138246426800634901)
                  ·
                    refine ⟨1241603068980301256279761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26487532138246426800634901 1241603068980301256279761)
                    ·
                      rfl

theorem cell23_7254040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_7254040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254040 prefixEnd_7254040 := by exact prefixLift 7254040
  have htrace : WordTrace (prefixWord ++ tailWord_7254040) baseStart_7254040 baseEnd_7254040 := by
    simpa [prefixWord, tailWord_7254040, baseEnd_7254040] using wordTrace_append hprefix tailTrace_7254040
  have hstable : (prefixWord ++ tailWord_7254040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254040).length < 2 ^ (prefixWord ++ tailWord_7254040).sum := by decide
  have hdescent : baseEnd_7254040 < baseStart_7254040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254064 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2]
def baseStart_7254064 : Nat := 118140960795 + 7254064 * 2 ^ 59
def prefixEnd_7254064 : Nat := 4983230072969 + 3 ^ 40 * 7254064 * 2
def baseEnd_7254064 : Nat := 3724821530476611674939173

theorem tailTrace_7254064 : CollatzResearch.WordTrace tailWord_7254064 prefixEnd_7254064 3724821530476611674939173 := by
  unfold tailWord_7254064
  simp only [CollatzResearch.WordTrace]
  refine ⟨132288724995886249171400623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176384966661181665561867497 132288724995886249171400623)
  ·
    refine ⟨198433087493829373757100935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132288724995886249171400623 198433087493829373757100935)
    ·
      refine ⟨297649631240744060635651403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198433087493829373757100935 297649631240744060635651403)
      ·
        refine ⟨446474446861116090953477105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297649631240744060635651403 446474446861116090953477105)
        ·
          refine ⟨334855835145837068215107829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446474446861116090953477105 334855835145837068215107829)
          ·
            refine ⟨31392734544922225145166359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334855835145837068215107829 31392734544922225145166359)
            ·
              refine ⟨47089101817383337717749539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31392734544922225145166359 47089101817383337717749539)
              ·
                refine ⟨70633652726075006576624309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47089101817383337717749539 70633652726075006576624309)
                ·
                  refine ⟨6621904943069531866558529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70633652726075006576624309 6621904943069531866558529)
                  ·
                    refine ⟨4966428707302148899918897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621904943069531866558529 4966428707302148899918897)
                    ·
                      refine ⟨3724821530476611674939173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966428707302148899918897 3724821530476611674939173)
                      ·
                        rfl

theorem cell23_7254064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2].length) (baseStart_7254064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254064 prefixEnd_7254064 := by exact prefixLift 7254064
  have htrace : WordTrace (prefixWord ++ tailWord_7254064) baseStart_7254064 baseEnd_7254064 := by
    simpa [prefixWord, tailWord_7254064, baseEnd_7254064] using wordTrace_append hprefix tailTrace_7254064
  have hstable : (prefixWord ++ tailWord_7254064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254064).length < 2 ^ (prefixWord ++ tailWord_7254064).sum := by decide
  have hdescent : baseEnd_7254064 < baseStart_7254064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254067 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3]
def baseStart_7254067 : Nat := 118140960795 + 7254067 * 2 ^ 59
def prefixEnd_7254067 : Nat := 4983230072969 + 3 ^ 40 * 7254067 * 2
def baseEnd_7254067 : Nat := 3724823070918575163201659

theorem tailTrace_7254067 : CollatzResearch.WordTrace tailWord_7254067 prefixEnd_7254067 3724823070918575163201659 := by
  unfold tailWord_7254067
  simp only [CollatzResearch.WordTrace]
  refine ⟨264577559410761629855160455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176385039607174419903440303 264577559410761629855160455)
  ·
    refine ⟨396866339116142444782740683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264577559410761629855160455 396866339116142444782740683)
    ·
      refine ⟨595299508674213667174111025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396866339116142444782740683 595299508674213667174111025)
      ·
        refine ⟨446474631505660250380583269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595299508674213667174111025 446474631505660250380583269)
        ·
          refine ⟨83713993407311296946359363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446474631505660250380583269 83713993407311296946359363)
          ·
            refine ⟨125570990110966945419539045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83713993407311296946359363 125570990110966945419539045)
            ·
              refine ⟨23544560645806302266163571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125570990110966945419539045 23544560645806302266163571)
              ·
                refine ⟨35316840968709453399245357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23544560645806302266163571 35316840968709453399245357)
                ·
                  refine ⟨13243815363266045024717009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35316840968709453399245357 13243815363266045024717009)
                  ·
                    refine ⟨9932861522449533768537757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13243815363266045024717009 9932861522449533768537757)
                    ·
                      refine ⟨3724823070918575163201659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9932861522449533768537757 3724823070918575163201659)
                      ·
                        rfl

theorem cell23_7254067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_7254067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254067 prefixEnd_7254067 := by exact prefixLift 7254067
  have htrace : WordTrace (prefixWord ++ tailWord_7254067) baseStart_7254067 baseEnd_7254067 := by
    simpa [prefixWord, tailWord_7254067, baseEnd_7254067] using wordTrace_append hprefix tailTrace_7254067
  have hstable : (prefixWord ++ tailWord_7254067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254067).length < 2 ^ (prefixWord ++ tailWord_7254067).sum := by decide
  have hdescent : baseEnd_7254067 < baseStart_7254067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254077 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7254077 : Nat := 118140960795 + 7254077 * 2 ^ 59
def prefixEnd_7254077 : Nat := 4983230072969 + 3 ^ 40 * 7254077 * 2
def baseEnd_7254077 : Nat := 3724828205725120124076613

theorem tailTrace_7254077 : CollatzResearch.WordTrace tailWord_7254077 prefixEnd_7254077 3724828205725120124076613 := by
  unfold tailWord_7254077
  simp only [CollatzResearch.WordTrace]
  refine ⟨264577924140725401563024485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176385282760483601042016323 264577924140725401563024485)
  ·
    refine ⟨49608360776386012793067091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264577924140725401563024485 49608360776386012793067091)
    ·
      refine ⟨74412541164579019189600637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49608360776386012793067091 74412541164579019189600637)
      ·
        refine ⟨27904702936717132196100239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74412541164579019189600637 27904702936717132196100239)
        ·
          refine ⟨41857054405075698294150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27904702936717132196100239 41857054405075698294150359)
          ·
            refine ⟨62785581607613547441225539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41857054405075698294150359 62785581607613547441225539)
            ·
              refine ⟨94178372411420321161838309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62785581607613547441225539 94178372411420321161838309)
              ·
                refine ⟨17658444827141310217844683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94178372411420321161838309 17658444827141310217844683)
                ·
                  refine ⟨26487667240711965326767025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17658444827141310217844683 26487667240711965326767025)
                  ·
                    refine ⟨19865750430533973995075269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26487667240711965326767025 19865750430533973995075269)
                    ·
                      refine ⟨3724828205725120124076613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19865750430533973995075269 3724828205725120124076613)
                      ·
                        rfl

theorem cell23_7254077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7254077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254077 prefixEnd_7254077 := by exact prefixLift 7254077
  have htrace : WordTrace (prefixWord ++ tailWord_7254077) baseStart_7254077 baseEnd_7254077 := by
    simpa [prefixWord, tailWord_7254077, baseEnd_7254077] using wordTrace_append hprefix tailTrace_7254077
  have hstable : (prefixWord ++ tailWord_7254077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254077).length < 2 ^ (prefixWord ++ tailWord_7254077).sum := by decide
  have hdescent : baseEnd_7254077 < baseStart_7254077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254078 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_7254078 : Nat := 118140960795 + 7254078 * 2 ^ 59
def prefixEnd_7254078 : Nat := 4983230072969 + 3 ^ 40 * 7254078 * 2
def baseEnd_7254078 : Nat := 1241609573068591540054703

theorem tailTrace_7254078 : CollatzResearch.WordTrace tailWord_7254078 prefixEnd_7254078 1241609573068591540054703 := by
  unfold tailWord_7254078
  simp only [CollatzResearch.WordTrace]
  refine ⟨33072245076715222341726361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176385307075814519155873925 33072245076715222341726361)
  ·
    refine ⟨24804183807536416756294771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33072245076715222341726361 24804183807536416756294771)
    ·
      refine ⟨37206275711304625134442157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24804183807536416756294771 37206275711304625134442157)
      ·
        refine ⟨13952353391739234425415809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37206275711304625134442157 13952353391739234425415809)
        ·
          refine ⟨10464265043804425819061857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13952353391739234425415809 10464265043804425819061857)
          ·
            refine ⟨7848198782853319364296393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464265043804425819061857 7848198782853319364296393)
            ·
              refine ⟨5886149087139989523222295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7848198782853319364296393 5886149087139989523222295)
              ·
                refine ⟨8829223630709984284833443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886149087139989523222295 8829223630709984284833443)
                ·
                  refine ⟨13243835446064976427250165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829223630709984284833443 13243835446064976427250165)
                  ·
                    refine ⟨1241609573068591540054703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13243835446064976427250165 1241609573068591540054703)
                    ·
                      rfl

theorem cell23_7254078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_7254078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254078 prefixEnd_7254078 := by exact prefixLift 7254078
  have htrace : WordTrace (prefixWord ++ tailWord_7254078) baseStart_7254078 baseEnd_7254078 := by
    simpa [prefixWord, tailWord_7254078, baseEnd_7254078] using wordTrace_append hprefix tailTrace_7254078
  have hstable : (prefixWord ++ tailWord_7254078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254078).length < 2 ^ (prefixWord ++ tailWord_7254078).sum := by decide
  have hdescent : baseEnd_7254078 < baseStart_7254078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254081 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7254081 : Nat := 118140960795 + 7254081 * 2 ^ 59
def prefixEnd_7254081 : Nat := 4983230072969 + 3 ^ 40 * 7254081 * 2
def baseEnd_7254081 : Nat := 3724830259647738108426595

theorem tailTrace_7254081 : CollatzResearch.WordTrace tailWord_7254081 prefixEnd_7254081 3724830259647738108426595 := by
  unfold tailWord_7254081
  simp only [CollatzResearch.WordTrace]
  refine ⟨264578070032710910246170097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176385380021807273497446731 264578070032710910246170097)
  ·
    refine ⟨198433552524533182684627573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264578070032710910246170097 198433552524533182684627573)
    ·
      refine ⟨18603145549174985876683835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198433552524533182684627573 18603145549174985876683835)
      ·
        refine ⟨27904718323762478815025753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603145549174985876683835 27904718323762478815025753)
        ·
          refine ⟨20928538742821859111269315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27904718323762478815025753 20928538742821859111269315)
          ·
            refine ⟨31392808114232788666903973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20928538742821859111269315 31392808114232788666903973)
            ·
              refine ⟨5886151521418647875044495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31392808114232788666903973 5886151521418647875044495)
              ·
                refine ⟨8829227282127971812566743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886151521418647875044495 8829227282127971812566743)
                ·
                  refine ⟨13243840923191957718850115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829227282127971812566743 13243840923191957718850115)
                  ·
                    refine ⟨19865761384787936578275173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13243840923191957718850115 19865761384787936578275173)
                    ·
                      refine ⟨3724830259647738108426595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19865761384787936578275173 3724830259647738108426595)
                      ·
                        rfl

theorem cell23_7254081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7254081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254081 prefixEnd_7254081 := by exact prefixLift 7254081
  have htrace : WordTrace (prefixWord ++ tailWord_7254081) baseStart_7254081 baseEnd_7254081 := by
    simpa [prefixWord, tailWord_7254081, baseEnd_7254081] using wordTrace_append hprefix tailTrace_7254081
  have hstable : (prefixWord ++ tailWord_7254081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254081).length < 2 ^ (prefixWord ++ tailWord_7254081).sum := by decide
  have hdescent : baseEnd_7254081 < baseStart_7254081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254090 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_7254090 : Nat := 118140960795 + 7254090 * 2 ^ 59
def prefixEnd_7254090 : Nat := 4983230072969 + 3 ^ 40 * 7254090 * 2
def baseEnd_7254090 : Nat := 3724834880973628573214053

theorem tailTrace_7254090 : CollatzResearch.WordTrace tailWord_7254090 prefixEnd_7254090 3724834880973628573214053 := by
  unfold tailWord_7254090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144599572419576195811931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176385598859785536522165149 66144599572419576195811931)
  ·
    refine ⟨99216899358629364293717897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66144599572419576195811931 99216899358629364293717897)
    ·
      refine ⟨74412674518972023220288423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99216899358629364293717897 74412674518972023220288423)
      ·
        refine ⟨111619011778458034830432635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74412674518972023220288423 111619011778458034830432635)
        ·
          refine ⟨167428517667687052245648953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111619011778458034830432635 167428517667687052245648953)
          ·
            refine ⟨125571388250765289184236715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167428517667687052245648953 125571388250765289184236715)
            ·
              refine ⟨188357082376147933776355073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125571388250765289184236715 188357082376147933776355073)
              ·
                refine ⟨141267811782110950332266305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188357082376147933776355073 141267811782110950332266305)
                ·
                  refine ⟨105950858836583212749199729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141267811782110950332266305 105950858836583212749199729)
                  ·
                    refine ⟨79463144127437409561899797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105950858836583212749199729 79463144127437409561899797)
                    ·
                      refine ⟨3724834880973628573214053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79463144127437409561899797 3724834880973628573214053)
                      ·
                        rfl

theorem cell23_7254090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_7254090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254090 prefixEnd_7254090 := by exact prefixLift 7254090
  have htrace : WordTrace (prefixWord ++ tailWord_7254090) baseStart_7254090 baseEnd_7254090 := by
    simpa [prefixWord, tailWord_7254090, baseEnd_7254090] using wordTrace_append hprefix tailTrace_7254090
  have hstable : (prefixWord ++ tailWord_7254090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254090).length < 2 ^ (prefixWord ++ tailWord_7254090).sum := by decide
  have hdescent : baseEnd_7254090 < baseStart_7254090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254098 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_7254098 : Nat := 118140960795 + 7254098 * 2 ^ 59
def prefixEnd_7254098 : Nat := 4983230072969 + 3 ^ 40 * 7254098 * 2
def baseEnd_7254098 : Nat := 3724838988818864541914017

theorem tailTrace_7254098 : CollatzResearch.WordTrace tailWord_7254098 prefixEnd_7254098 3724838988818864541914017 := by
  unfold tailWord_7254098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144672518412330537384737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176385793382432881433025965 66144672518412330537384737)
  ·
    refine ⟨49608504388809247903038553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66144672518412330537384737 49608504388809247903038553)
    ·
      refine ⟨37206378291606935927278915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49608504388809247903038553 37206378291606935927278915)
      ·
        refine ⟨55809567437410403890918373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37206378291606935927278915 55809567437410403890918373)
        ·
          refine ⟨10464293894514450729547195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55809567437410403890918373 10464293894514450729547195)
          ·
            refine ⟨15696440841771676094320793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464293894514450729547195 15696440841771676094320793)
            ·
              refine ⟨11772330631328757070740595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15696440841771676094320793 11772330631328757070740595)
              ·
                refine ⟨17658495946993135606110893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11772330631328757070740595 17658495946993135606110893)
                ·
                  refine ⟨6621935980122425852291585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17658495946993135606110893 6621935980122425852291585)
                  ·
                    refine ⟨4966451985091819389218689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6621935980122425852291585 4966451985091819389218689)
                    ·
                      refine ⟨3724838988818864541914017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966451985091819389218689 3724838988818864541914017)
                      ·
                        rfl

theorem cell23_7254098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_7254098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254098 prefixEnd_7254098 := by exact prefixLift 7254098
  have htrace : WordTrace (prefixWord ++ tailWord_7254098) baseStart_7254098 baseEnd_7254098 := by
    simpa [prefixWord, tailWord_7254098, baseEnd_7254098] using wordTrace_append hprefix tailTrace_7254098
  have hstable : (prefixWord ++ tailWord_7254098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254098).length < 2 ^ (prefixWord ++ tailWord_7254098).sum := by decide
  have hdescent : baseEnd_7254098 < baseStart_7254098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254141 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_7254141 : Nat := 118140960795 + 7254141 * 2 ^ 59
def prefixEnd_7254141 : Nat := 4983230072969 + 3 ^ 40 * 7254141 * 2
def baseEnd_7254141 : Nat := 3724861068487007873676319

theorem tailTrace_7254141 : CollatzResearch.WordTrace tailWord_7254141 prefixEnd_7254141 3724861068487007873676319 := by
  unfold tailWord_7254141
  simp only [CollatzResearch.WordTrace]
  refine ⟨264580258412493540493354277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176386838941662360328902851 264580258412493540493354277)
  ·
    refine ⟨49608798452342538842503927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264580258412493540493354277 49608798452342538842503927)
    ·
      refine ⟨74413197678513808263755891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49608798452342538842503927 74413197678513808263755891)
      ·
        refine ⟨111619796517770712395633837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74413197678513808263755891 111619796517770712395633837)
        ·
          refine ⟨41857423694164017148362689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111619796517770712395633837 41857423694164017148362689)
          ·
            refine ⟨31393067770623012861272017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41857423694164017148362689 31393067770623012861272017)
            ·
              refine ⟨23544800827967259645954013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31393067770623012861272017 23544800827967259645954013)
              ·
                refine ⟨8829300310487722367232755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23544800827967259645954013 8829300310487722367232755)
                ·
                  refine ⟨13243950465731583550849133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829300310487722367232755 13243950465731583550849133)
                  ·
                    refine ⟨4966481424649343831568425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13243950465731583550849133 4966481424649343831568425)
                    ·
                      refine ⟨3724861068487007873676319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966481424649343831568425 3724861068487007873676319)
                      ·
                        rfl

theorem cell23_7254141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_7254141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254141 prefixEnd_7254141 := by exact prefixLift 7254141
  have htrace : WordTrace (prefixWord ++ tailWord_7254141) baseStart_7254141 baseEnd_7254141 := by
    simpa [prefixWord, tailWord_7254141, baseEnd_7254141] using wordTrace_append hprefix tailTrace_7254141
  have hstable : (prefixWord ++ tailWord_7254141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254141).length < 2 ^ (prefixWord ++ tailWord_7254141).sum := by decide
  have hdescent : baseEnd_7254141 < baseStart_7254141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254194 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_7254194 : Nat := 118140960795 + 7254194 * 2 ^ 59
def prefixEnd_7254194 : Nat := 4983230072969 + 3 ^ 40 * 7254194 * 2
def baseEnd_7254194 : Nat := 413876475884632907368175

theorem tailTrace_7254194 : CollatzResearch.WordTrace tailWord_7254194 prefixEnd_7254194 413876475884632907368175 := by
  unfold tailWord_7254194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66145547870325382636258409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176388127654201020363355757 66145547870325382636258409)
  ·
    refine ⟨49609160902744036977193807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66145547870325382636258409 49609160902744036977193807)
    ·
      refine ⟨74413741354116055465790711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49609160902744036977193807 74413741354116055465790711)
      ·
        refine ⟨111620612031174083198686067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74413741354116055465790711 111620612031174083198686067)
        ·
          refine ⟨167430918046761124798029101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111620612031174083198686067 167430918046761124798029101)
          ·
            refine ⟨62786594267535421799260913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167430918046761124798029101 62786594267535421799260913)
            ·
              refine ⟨47089945700651566349445685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62786594267535421799260913 47089945700651566349445685)
              ·
                refine ⟨4414682409436084345260533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47089945700651566349445685 4414682409436084345260533)
                ·
                  refine ⟨413876475884632907368175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414682409436084345260533 413876475884632907368175)
                  ·
                    rfl

theorem cell23_7254194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_7254194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254194 prefixEnd_7254194 := by exact prefixLift 7254194
  have htrace : WordTrace (prefixWord ++ tailWord_7254194) baseStart_7254194 baseEnd_7254194 := by
    simpa [prefixWord, tailWord_7254194, baseEnd_7254194] using wordTrace_append hprefix tailTrace_7254194
  have hstable : (prefixWord ++ tailWord_7254194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254194).length < 2 ^ (prefixWord ++ tailWord_7254194).sum := by decide
  have hdescent : baseEnd_7254194 < baseStart_7254194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254244 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_7254244 : Nat := 118140960795 + 7254244 * 2 ^ 59
def prefixEnd_7254244 : Nat := 4983230072969 + 3 ^ 40 * 7254244 * 2
def baseEnd_7254244 : Nat := 3724913956994420970688345

theorem tailTrace_7254244 : CollatzResearch.WordTrace tailWord_7254244 prefixEnd_7254244 3724913956994420970688345 := by
  unfold tailWord_7254244
  simp only [CollatzResearch.WordTrace]
  refine ⟨132292007565560194542176893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176389343420746926056235857 132292007565560194542176893)
  ·
    refine ⟨49609502837085072953316335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132292007565560194542176893 49609502837085072953316335)
    ·
      refine ⟨74414254255627609429974503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49609502837085072953316335 74414254255627609429974503)
      ·
        refine ⟨111621381383441414144961755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74414254255627609429974503 111621381383441414144961755)
        ·
          refine ⟨167432072075162121217442633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111621381383441414144961755 167432072075162121217442633)
          ·
            refine ⟨125574054056371590913081975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167432072075162121217442633 125574054056371590913081975)
            ·
              refine ⟨188361081084557386369622963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125574054056371590913081975 188361081084557386369622963)
              ·
                refine ⟨282541621626836079554434445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188361081084557386369622963 282541621626836079554434445)
                ·
                  refine ⟨105953108110063529832912917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282541621626836079554434445 105953108110063529832912917)
                  ·
                    refine ⟨4966551942659227960917793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105953108110063529832912917 4966551942659227960917793)
                    ·
                      refine ⟨3724913956994420970688345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966551942659227960917793 3724913956994420970688345)
                      ·
                        rfl

theorem cell23_7254244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_7254244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254244 prefixEnd_7254244 := by exact prefixLift 7254244
  have htrace : WordTrace (prefixWord ++ tailWord_7254244) baseStart_7254244 baseEnd_7254244 := by
    simpa [prefixWord, tailWord_7254244, baseEnd_7254244] using wordTrace_append hprefix tailTrace_7254244
  have hstable : (prefixWord ++ tailWord_7254244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254244).length < 2 ^ (prefixWord ++ tailWord_7254244).sum := by decide
  have hdescent : baseEnd_7254244 < baseStart_7254244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254254 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7254254 : Nat := 118140960795 + 7254254 * 2 ^ 59
def prefixEnd_7254254 : Nat := 4983230072969 + 3 ^ 40 * 7254254 * 2
def baseEnd_7254254 : Nat := 1241639697266988643854433

theorem tailTrace_7254254 : CollatzResearch.WordTrace tailWord_7254254 prefixEnd_7254254 1241639697266988643854433 := by
  unfold tailWord_7254254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33073047482635520099027227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176389586574056107194811877 33073047482635520099027227)
  ·
    refine ⟨49609571223953280148540841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33073047482635520099027227 49609571223953280148540841)
    ·
      refine ⟨37207178417964960111405631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49609571223953280148540841 37207178417964960111405631)
      ·
        refine ⟨55810767626947440167108447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37207178417964960111405631 55810767626947440167108447)
        ·
          refine ⟨83716151440421160250662671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55810767626947440167108447 83716151440421160250662671)
          ·
            refine ⟨125574227160631740375994007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83716151440421160250662671 125574227160631740375994007)
            ·
              refine ⟨188361340740947610563991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125574227160631740375994007 188361340740947610563991011)
              ·
                refine ⟨282542011111421415845986517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188361340740947610563991011 282542011111421415845986517)
                ·
                  refine ⟨6622078385423939433890309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 282542011111421415845986517 6622078385423939433890309)
                  ·
                    refine ⟨1241639697266988643854433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622078385423939433890309 1241639697266988643854433)
                    ·
                      rfl

theorem cell23_7254254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7254254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254254 prefixEnd_7254254 := by exact prefixLift 7254254
  have htrace : WordTrace (prefixWord ++ tailWord_7254254) baseStart_7254254 baseEnd_7254254 := by
    simpa [prefixWord, tailWord_7254254, baseEnd_7254254] using wordTrace_append hprefix tailTrace_7254254
  have hstable : (prefixWord ++ tailWord_7254254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254254).length < 2 ^ (prefixWord ++ tailWord_7254254).sum := by decide
  have hdescent : baseEnd_7254254 < baseStart_7254254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254257 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_7254257 : Nat := 118140960795 + 7254257 * 2 ^ 59
def prefixEnd_7254257 : Nat := 4983230072969 + 3 ^ 40 * 7254257 * 2
def baseEnd_7254257 : Nat := 3724920632242929419825785

theorem tailTrace_7254257 : CollatzResearch.WordTrace tailWord_7254257 prefixEnd_7254257 3724920632242929419825785 := by
  unfold tailWord_7254257
  simp only [CollatzResearch.WordTrace]
  refine ⟨264584489280073292304577025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176389659520048861536384683 264584489280073292304577025)
  ·
    refine ⟨198438366960054969228432769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264584489280073292304577025 198438366960054969228432769)
    ·
      refine ⟨148828775220041226921324577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198438366960054969228432769 148828775220041226921324577)
      ·
        refine ⟨111621581415030920190993433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148828775220041226921324577 111621581415030920190993433)
        ·
          refine ⟨83716186061273190143245075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111621581415030920190993433 83716186061273190143245075)
          ·
            refine ⟨125574279091909785214867613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83716186061273190143245075 125574279091909785214867613)
            ·
              refine ⟨47090354659466169455575355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125574279091909785214867613 47090354659466169455575355)
              ·
                refine ⟨70635531989199254183363033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47090354659466169455575355 70635531989199254183363033)
                ·
                  refine ⟨52976648991899440637522275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70635531989199254183363033 52976648991899440637522275)
                  ·
                    refine ⟨79464973487849160956283413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52976648991899440637522275 79464973487849160956283413)
                    ·
                      refine ⟨3724920632242929419825785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79464973487849160956283413 3724920632242929419825785)
                      ·
                        rfl

theorem cell23_7254257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_7254257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254257 prefixEnd_7254257 := by exact prefixLift 7254257
  have htrace : WordTrace (prefixWord ++ tailWord_7254257) baseStart_7254257 baseEnd_7254257 := by
    simpa [prefixWord, tailWord_7254257, baseEnd_7254257] using wordTrace_append hprefix tailTrace_7254257
  have hstable : (prefixWord ++ tailWord_7254257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254257).length < 2 ^ (prefixWord ++ tailWord_7254257).sum := by decide
  have hdescent : baseEnd_7254257 < baseStart_7254257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254264 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_7254264 : Nat := 118140960795 + 7254264 * 2 ^ 59
def prefixEnd_7254264 : Nat := 4983230072969 + 3 ^ 40 * 7254264 * 2
def baseEnd_7254264 : Nat := 3724924226607510892438253

theorem tailTrace_7254264 : CollatzResearch.WordTrace tailWord_7254264 prefixEnd_7254264 3724924226607510892438253 := by
  unfold tailWord_7254264
  simp only [CollatzResearch.WordTrace]
  refine ⟨132292372295523966250040923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176389829727365288333387897 132292372295523966250040923)
  ·
    refine ⟨198438558443285949375061385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132292372295523966250040923 198438558443285949375061385)
    ·
      refine ⟨148828918832464462031296039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198438558443285949375061385 148828918832464462031296039)
      ·
        refine ⟨223243378248696693046944059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148828918832464462031296039 223243378248696693046944059)
        ·
          refine ⟨334865067373045039570416089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223243378248696693046944059 334865067373045039570416089)
          ·
            refine ⟨251148800529783779677812067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334865067373045039570416089 251148800529783779677812067)
            ·
              refine ⟨376723200794675669516718101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251148800529783779677812067 376723200794675669516718101)
              ·
                refine ⟨17658900037250422008596161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376723200794675669516718101 17658900037250422008596161)
                ·
                  refine ⟨13244175027937816506447121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17658900037250422008596161 13244175027937816506447121)
                  ·
                    refine ⟨9933131270953362379835341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13244175027937816506447121 9933131270953362379835341)
                    ·
                      refine ⟨3724924226607510892438253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933131270953362379835341 3724924226607510892438253)
                      ·
                        rfl

theorem cell23_7254264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_7254264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254264 prefixEnd_7254264 := by exact prefixLift 7254264
  have htrace : WordTrace (prefixWord ++ tailWord_7254264) baseStart_7254264 baseEnd_7254264 := by
    simpa [prefixWord, tailWord_7254264, baseEnd_7254264] using wordTrace_append hprefix tailTrace_7254264
  have hstable : (prefixWord ++ tailWord_7254264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254264).length < 2 ^ (prefixWord ++ tailWord_7254264).sum := by decide
  have hdescent : baseEnd_7254264 < baseStart_7254264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254271 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 1, 4]
def baseStart_7254271 : Nat := 118140960795 + 7254271 * 2 ^ 59
def prefixEnd_7254271 : Nat := 4983230072969 + 3 ^ 40 * 7254271 * 2
def baseEnd_7254271 : Nat := 1241642606990697455016907

theorem tailTrace_7254271 : CollatzResearch.WordTrace tailWord_7254271 prefixEnd_7254271 1241642606990697455016907 := by
  unfold tailWord_7254271
  simp only [CollatzResearch.WordTrace]
  refine ⟨264584999902022572695586667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176389999934681715130391111 264584999902022572695586667)
  ·
    refine ⟨396877499853033859043380001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264584999902022572695586667 396877499853033859043380001)
    ·
      refine ⟨297658124889775394282535001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396877499853033859043380001 297658124889775394282535001)
      ·
        refine ⟨223243593667331545711901251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297658124889775394282535001 223243593667331545711901251)
        ·
          refine ⟨334865390500997318567851877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223243593667331545711901251 334865390500997318567851877)
          ·
            refine ⟨62787260718936997231472227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334865390500997318567851877 62787260718936997231472227)
            ·
              refine ⟨94180891078405495847208341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62787260718936997231472227 94180891078405495847208341)
              ·
                refine ⟨4414729269300257617837891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94180891078405495847208341 4414729269300257617837891)
                ·
                  refine ⟨6622093903950386426756837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414729269300257617837891 6622093903950386426756837)
                  ·
                    refine ⟨1241642606990697455016907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622093903950386426756837 1241642606990697455016907)
                    ·
                      rfl

theorem cell23_7254271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_7254271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254271 prefixEnd_7254271 := by exact prefixLift 7254271
  have htrace : WordTrace (prefixWord ++ tailWord_7254271) baseStart_7254271 baseEnd_7254271 := by
    simpa [prefixWord, tailWord_7254271, baseEnd_7254271] using wordTrace_append hprefix tailTrace_7254271
  have hstable : (prefixWord ++ tailWord_7254271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254271).length < 2 ^ (prefixWord ++ tailWord_7254271).sum := by decide
  have hdescent : baseEnd_7254271 < baseStart_7254271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254328 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_7254328 : Nat := 118140960795 + 7254328 * 2 ^ 59
def prefixEnd_7254328 : Nat := 4983230072969 + 3 ^ 40 * 7254328 * 2
def baseEnd_7254328 : Nat := 3724957089369398642037959

theorem tailTrace_7254328 : CollatzResearch.WordTrace tailWord_7254328 prefixEnd_7254328 3724957089369398642037959 := by
  unfold tailWord_7254328
  simp only [CollatzResearch.WordTrace]
  refine ⟨132293539431408035715205819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176391385908544047620274425 132293539431408035715205819)
  ·
    refine ⟨198440309147112053572808729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132293539431408035715205819 198440309147112053572808729)
    ·
      refine ⟨148830231860334040179606547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198440309147112053572808729 148830231860334040179606547)
      ·
        refine ⟨223245347790501060269409821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148830231860334040179606547 223245347790501060269409821)
        ·
          refine ⟨83717005421437897601028683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223245347790501060269409821 83717005421437897601028683)
          ·
            refine ⟨125575508132156846401543025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83717005421437897601028683 125575508132156846401543025)
            ·
              refine ⟨94181631099117634801157269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125575508132156846401543025 94181631099117634801157269)
              ·
                refine ⟨4414763957771139131304247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94181631099117634801157269 4414763957771139131304247)
                ·
                  refine ⟨6622145936656708696956371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414763957771139131304247 6622145936656708696956371)
                  ·
                    refine ⟨9933218904985063045434557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622145936656708696956371 9933218904985063045434557)
                    ·
                      refine ⟨3724957089369398642037959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933218904985063045434557 3724957089369398642037959)
                      ·
                        rfl

theorem cell23_7254328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_7254328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254328 prefixEnd_7254328 := by exact prefixLift 7254328
  have htrace : WordTrace (prefixWord ++ tailWord_7254328) baseStart_7254328 baseEnd_7254328 := by
    simpa [prefixWord, tailWord_7254328, baseEnd_7254328] using wordTrace_append hprefix tailTrace_7254328
  have hstable : (prefixWord ++ tailWord_7254328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254328).length < 2 ^ (prefixWord ++ tailWord_7254328).sum := by decide
  have hdescent : baseEnd_7254328 < baseStart_7254328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254354 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7254354 : Nat := 118140960795 + 7254354 * 2 ^ 59
def prefixEnd_7254354 : Nat := 4983230072969 + 3 ^ 40 * 7254354 * 2
def baseEnd_7254354 : Nat := 3724970439866415540312839

theorem tailTrace_7254354 : CollatzResearch.WordTrace tailWord_7254354 prefixEnd_7254354 3724970439866415540312839 := by
  unfold tailWord_7254354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66147006790180469467714529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176392018107147918580572077 66147006790180469467714529)
  ·
    refine ⟨49610255092635352100785897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66147006790180469467714529 49610255092635352100785897)
    ·
      refine ⟨37207691319476514075589423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49610255092635352100785897 37207691319476514075589423)
      ·
        refine ⟨55811536979214771113384135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37207691319476514075589423 55811536979214771113384135)
        ·
          refine ⟨83717305468822156670076203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55811536979214771113384135 83717305468822156670076203)
          ·
            refine ⟨125575958203233235005114305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83717305468822156670076203 125575958203233235005114305)
            ·
              refine ⟨94181968652424926253835729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125575958203233235005114305 94181968652424926253835729)
              ·
                refine ⟨70636476489318694690376797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94181968652424926253835729 70636476489318694690376797)
                ·
                  refine ⟨26488678683494510508891299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70636476489318694690376797 26488678683494510508891299)
                  ·
                    refine ⟨39733018025241765763336949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26488678683494510508891299 39733018025241765763336949)
                    ·
                      refine ⟨3724970439866415540312839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39733018025241765763336949 3724970439866415540312839)
                      ·
                        rfl

theorem cell23_7254354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7254354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254354 prefixEnd_7254354 := by exact prefixLift 7254354
  have htrace : WordTrace (prefixWord ++ tailWord_7254354) baseStart_7254354 baseEnd_7254354 := by
    simpa [prefixWord, tailWord_7254354, baseEnd_7254354] using wordTrace_append hprefix tailTrace_7254354
  have hstable : (prefixWord ++ tailWord_7254354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254354).length < 2 ^ (prefixWord ++ tailWord_7254354).sum := by decide
  have hdescent : baseEnd_7254354 < baseStart_7254354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254378 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_7254378 : Nat := 118140960795 + 7254378 * 2 ^ 59
def prefixEnd_7254378 : Nat := 4983230072969 + 3 ^ 40 * 7254378 * 2
def baseEnd_7254378 : Nat := 1241660921134041148804243

theorem tailTrace_7254378 : CollatzResearch.WordTrace tailWord_7254378 prefixEnd_7254378 1241660921134041148804243 := by
  unfold tailWord_7254378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66147225628158732492432947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176392601675089953313154525 66147225628158732492432947)
  ·
    refine ⟨99220838442238098738649421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66147225628158732492432947 99220838442238098738649421)
    ·
      refine ⟨37207814415839287026993533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99220838442238098738649421 37207814415839287026993533)
      ·
        refine ⟨13952930405939732635122575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37207814415839287026993533 13952930405939732635122575)
        ·
          refine ⟨20929395608909598952683863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13952930405939732635122575 20929395608909598952683863)
          ·
            refine ⟨31394093413364398429025795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20929395608909598952683863 31394093413364398429025795)
            ·
              refine ⟨47091140120046597643538693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31394093413364398429025795 47091140120046597643538693)
              ·
                refine ⟨8829588772508737058163505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47091140120046597643538693 8829588772508737058163505)
                ·
                  refine ⟨6622191579381552793622629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8829588772508737058163505 6622191579381552793622629)
                  ·
                    refine ⟨1241660921134041148804243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622191579381552793622629 1241660921134041148804243)
                    ·
                      rfl

theorem cell23_7254378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_7254378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254378 prefixEnd_7254378 := by exact prefixLift 7254378
  have htrace : WordTrace (prefixWord ++ tailWord_7254378) baseStart_7254378 baseEnd_7254378 := by
    simpa [prefixWord, tailWord_7254378, baseEnd_7254378] using wordTrace_append hprefix tailTrace_7254378
  have hstable : (prefixWord ++ tailWord_7254378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254378).length < 2 ^ (prefixWord ++ tailWord_7254378).sum := by decide
  have hdescent : baseEnd_7254378 < baseStart_7254378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254404 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7254404 : Nat := 118140960795 + 7254404 * 2 ^ 59
def prefixEnd_7254404 : Nat := 4983230072969 + 3 ^ 40 * 7254404 * 2
def baseEnd_7254404 : Nat := 1241665371299713448229203

theorem tailTrace_7254404 : CollatzResearch.WordTrace tailWord_7254404 prefixEnd_7254404 1241665371299713448229203 := by
  unfold tailWord_7254404
  simp only [CollatzResearch.WordTrace]
  refine ⟨132294925405270368205089133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176393233873693824273452177 132294925405270368205089133)
  ·
    refine ⟨49610597026976388076908425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132294925405270368205089133 49610597026976388076908425)
    ·
      refine ⟨37207947770232291057681319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49610597026976388076908425 37207947770232291057681319)
      ·
        refine ⟨55811921655348436586521979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37207947770232291057681319 55811921655348436586521979)
        ·
          refine ⟨83717882483022654879782969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55811921655348436586521979 83717882483022654879782969)
          ·
            refine ⟨62788411862266991159837227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83717882483022654879782969 62788411862266991159837227)
            ·
              refine ⟨94182617793400486739755841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62788411862266991159837227 94182617793400486739755841)
              ·
                refine ⟨70636963345050365054816881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94182617793400486739755841 70636963345050365054816881)
                ·
                  refine ⟨52977722508787773791112661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70636963345050365054816881 52977722508787773791112661)
                  ·
                    refine ⟨1241665371299713448229203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52977722508787773791112661 1241665371299713448229203)
                    ·
                      rfl

theorem cell23_7254404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7254404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254404 prefixEnd_7254404 := by exact prefixLift 7254404
  have htrace : WordTrace (prefixWord ++ tailWord_7254404) baseStart_7254404 baseEnd_7254404 := by
    simpa [prefixWord, tailWord_7254404, baseEnd_7254404] using wordTrace_append hprefix tailTrace_7254404
  have hstable : (prefixWord ++ tailWord_7254404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254404).length < 2 ^ (prefixWord ++ tailWord_7254404).sum := by decide
  have hdescent : baseEnd_7254404 < baseStart_7254404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254435 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 3]
def baseStart_7254435 : Nat := 118140960795 + 7254435 * 2 ^ 59
def prefixEnd_7254435 : Nat := 4983230072969 + 3 ^ 40 * 7254435 * 2
def baseEnd_7254435 : Nat := 3725012031799429723399967

theorem tailTrace_7254435 : CollatzResearch.WordTrace tailWord_7254435 prefixEnd_7254435 3725012031799429723399967 := by
  unfold tailWord_7254435
  simp only [CollatzResearch.WordTrace]
  refine ⟨264590981473428428704556759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176393987648952285803037839 264590981473428428704556759)
  ·
    refine ⟨396886472210142643056835139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264590981473428428704556759 396886472210142643056835139)
    ·
      refine ⟨595329708315213964585252709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396886472210142643056835139 595329708315213964585252709)
      ·
        refine ⟨111624320309102618359734883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595329708315213964585252709 111624320309102618359734883)
        ·
          refine ⟨167436480463653927539602325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111624320309102618359734883 167436480463653927539602325)
          ·
            refine ⟨7848585021733777853418859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167436480463653927539602325 7848585021733777853418859)
            ·
              refine ⟨11772877532600666780128289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848585021733777853418859 11772877532600666780128289)
              ·
                refine ⟨8829658149450500085096217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11772877532600666780128289 8829658149450500085096217)
                ·
                  refine ⟨6622243612087875063822163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8829658149450500085096217 6622243612087875063822163)
                  ·
                    refine ⟨9933365418131812595733245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622243612087875063822163 9933365418131812595733245)
                    ·
                      refine ⟨3725012031799429723399967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933365418131812595733245 3725012031799429723399967)
                      ·
                        rfl

theorem cell23_7254435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_7254435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254435 prefixEnd_7254435 := by exact prefixLift 7254435
  have htrace : WordTrace (prefixWord ++ tailWord_7254435) baseStart_7254435 baseEnd_7254435 := by
    simpa [prefixWord, tailWord_7254435, baseEnd_7254435] using wordTrace_append hprefix tailTrace_7254435
  have hstable : (prefixWord ++ tailWord_7254435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254435).length < 2 ^ (prefixWord ++ tailWord_7254435).sum := by decide
  have hdescent : baseEnd_7254435 < baseStart_7254435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254441 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 4, 2]
def baseStart_7254441 : Nat := 118140960795 + 7254441 * 2 ^ 59
def prefixEnd_7254441 : Nat := 4983230072969 + 3 ^ 40 * 7254441 * 2
def baseEnd_7254441 : Nat := 3725015112683356699924939

theorem tailTrace_7254441 : CollatzResearch.WordTrace tailWord_7254441 prefixEnd_7254441 3725015112683356699924939 := by
  unfold tailWord_7254441
  simp only [CollatzResearch.WordTrace]
  refine ⟨264591200311406691729275177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176394133540937794486183451 264591200311406691729275177)
  ·
    refine ⟨198443400233555018796956383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264591200311406691729275177 198443400233555018796956383)
    ·
      refine ⟨297665100350332528195434575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198443400233555018796956383 297665100350332528195434575)
      ·
        refine ⟨446497650525498792293151863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297665100350332528195434575 446497650525498792293151863)
        ·
          refine ⟨669746475788248188439727795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446497650525498792293151863 669746475788248188439727795)
          ·
            refine ⟨1004619713682372282659591693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669746475788248188439727795 1004619713682372282659591693)
            ·
              refine ⟨376732392630889605997346885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004619713682372282659591693 376732392630889605997346885)
              ·
                refine ⟨70637323618291801124502541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376732392630889605997346885 70637323618291801124502541)
                ·
                  refine ⟨26488996356859425421688453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70637323618291801124502541 26488996356859425421688453)
                  ·
                    refine ⟨4966686816911142266566585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26488996356859425421688453 4966686816911142266566585)
                    ·
                      refine ⟨3725015112683356699924939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966686816911142266566585 3725015112683356699924939)
                      ·
                        rfl

theorem cell23_7254441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 4, 2].length) (baseStart_7254441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254441 prefixEnd_7254441 := by exact prefixLift 7254441
  have htrace : WordTrace (prefixWord ++ tailWord_7254441) baseStart_7254441 baseEnd_7254441 := by
    simpa [prefixWord, tailWord_7254441, baseEnd_7254441] using wordTrace_append hprefix tailTrace_7254441
  have hstable : (prefixWord ++ tailWord_7254441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254441).length < 2 ^ (prefixWord ++ tailWord_7254441).sum := by decide
  have hdescent : baseEnd_7254441 < baseStart_7254441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254444 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7254444 : Nat := 118140960795 + 7254444 * 2 ^ 59
def prefixEnd_7254444 : Nat := 4983230072969 + 3 ^ 40 * 7254444 * 2
def baseEnd_7254444 : Nat := 3725016653125320188187425

theorem tailTrace_7254444 : CollatzResearch.WordTrace tailWord_7254444 prefixEnd_7254444 3725016653125320188187425 := by
  unfold tailWord_7254444
  simp only [CollatzResearch.WordTrace]
  refine ⟨132295654865197911620817193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176394206486930548827756257 132295654865197911620817193)
  ·
    refine ⟨99221741148898433715612895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132295654865197911620817193 99221741148898433715612895)
    ·
      refine ⟨148832611723347650573419343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99221741148898433715612895 148832611723347650573419343)
      ·
        refine ⟨223248917585021475860129015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148832611723347650573419343 223248917585021475860129015)
        ·
          refine ⟨334873376377532213790193523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223248917585021475860129015 334873376377532213790193523)
          ·
            refine ⟨502310064566298320685290285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334873376377532213790193523 502310064566298320685290285)
            ·
              refine ⟨188366274212361870256983857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502310064566298320685290285 188366274212361870256983857)
              ·
                refine ⟨141274705659271402692737893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188366274212361870256983857 141274705659271402692737893)
                ·
                  refine ⟨26489007311113388004888355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141274705659271402692737893 26489007311113388004888355)
                  ·
                    refine ⟨39733510966670082007332533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26489007311113388004888355 39733510966670082007332533)
                    ·
                      refine ⟨3725016653125320188187425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39733510966670082007332533 3725016653125320188187425)
                      ·
                        rfl

theorem cell23_7254444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7254444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254444 prefixEnd_7254444 := by exact prefixLift 7254444
  have htrace : WordTrace (prefixWord ++ tailWord_7254444) baseStart_7254444 baseEnd_7254444 := by
    simpa [prefixWord, tailWord_7254444, baseEnd_7254444] using wordTrace_append hprefix tailTrace_7254444
  have hstable : (prefixWord ++ tailWord_7254444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254444).length < 2 ^ (prefixWord ++ tailWord_7254444).sum := by decide
  have hdescent : baseEnd_7254444 < baseStart_7254444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254509 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7254509 : Nat := 118140960795 + 7254509 * 2 ^ 59
def prefixEnd_7254509 : Nat := 4983230072969 + 3 ^ 40 * 7254509 * 2
def baseEnd_7254509 : Nat := 3725050029367862433874627

theorem tailTrace_7254509 : CollatzResearch.WordTrace tailWord_7254509 prefixEnd_7254509 3725050029367862433874627 := by
  unfold tailWord_7254509
  simp only [CollatzResearch.WordTrace]
  refine ⟨264593680475160339342750581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176395786983440226228500387 264593680475160339342750581)
  ·
    refine ⟨24805657544546281813382867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264593680475160339342750581 24805657544546281813382867)
    ·
      refine ⟨37208486316819422720074301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805657544546281813382867 37208486316819422720074301)
      ·
        refine ⟨13953182368807283520027863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37208486316819422720074301 13953182368807283520027863)
        ·
          refine ⟨20929773553210925280041795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953182368807283520027863 20929773553210925280041795)
          ·
            refine ⟨31394660329816387920062693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20929773553210925280041795 31394660329816387920062693)
            ·
              refine ⟨5886498811840572735011755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31394660329816387920062693 5886498811840572735011755)
              ·
                refine ⟨8829748217760859102517633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886498811840572735011755 8829748217760859102517633)
                ·
                  refine ⟨6622311163320644326888225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8829748217760859102517633 6622311163320644326888225)
                  ·
                    refine ⟨4966733372490483245166169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622311163320644326888225 4966733372490483245166169)
                    ·
                      refine ⟨3725050029367862433874627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966733372490483245166169 3725050029367862433874627)
                      ·
                        rfl

theorem cell23_7254509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7254509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254509 prefixEnd_7254509 := by exact prefixLift 7254509
  have htrace : WordTrace (prefixWord ++ tailWord_7254509) baseStart_7254509 baseEnd_7254509 := by
    simpa [prefixWord, tailWord_7254509, baseEnd_7254509] using wordTrace_append hprefix tailTrace_7254509
  have hstable : (prefixWord ++ tailWord_7254509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254509).length < 2 ^ (prefixWord ++ tailWord_7254509).sum := by decide
  have hdescent : baseEnd_7254509 < baseStart_7254509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254582 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7254582 : Nat := 118140960795 + 7254582 * 2 ^ 59
def prefixEnd_7254582 : Nat := 4983230072969 + 3 ^ 40 * 7254582 * 2
def baseEnd_7254582 : Nat := 3725087513455640648261791

theorem tailTrace_7254582 : CollatzResearch.WordTrace tailWord_7254582 prefixEnd_7254582 3725087513455640648261791 := by
  unfold tailWord_7254582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537271437743492050634875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176397562002597248540105333 16537271437743492050634875)
  ·
    refine ⟨24805907156615238075952313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537271437743492050634875 24805907156615238075952313)
    ·
      refine ⟨18604430367461428556964235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24805907156615238075952313 18604430367461428556964235)
      ·
        refine ⟨27906645551192142835446353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604430367461428556964235 27906645551192142835446353)
        ·
          refine ⟨20929984163394107126584765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27906645551192142835446353 20929984163394107126584765)
          ·
            refine ⟨7848744061272790172469287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20929984163394107126584765 7848744061272790172469287)
            ·
              refine ⟨11773116091909185258703931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848744061272790172469287 11773116091909185258703931)
              ·
                refine ⟨17659674137863777888055897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11773116091909185258703931 17659674137863777888055897)
                ·
                  refine ⟨13244755603397833416041923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17659674137863777888055897 13244755603397833416041923)
                  ·
                    refine ⟨19867133405096750124062885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13244755603397833416041923 19867133405096750124062885)
                    ·
                      refine ⟨3725087513455640648261791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19867133405096750124062885 3725087513455640648261791)
                      ·
                        rfl

theorem cell23_7254582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7254582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254582 prefixEnd_7254582 := by exact prefixLift 7254582
  have htrace : WordTrace (prefixWord ++ tailWord_7254582) baseStart_7254582 baseEnd_7254582 := by
    simpa [prefixWord, tailWord_7254582, baseEnd_7254582] using wordTrace_append hprefix tailTrace_7254582
  have hstable : (prefixWord ++ tailWord_7254582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254582).length < 2 ^ (prefixWord ++ tailWord_7254582).sum := by decide
  have hdescent : baseEnd_7254582 < baseStart_7254582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254605 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 6]
def baseStart_7254605 : Nat := 118140960795 + 7254605 * 2 ^ 59
def prefixEnd_7254605 : Nat := 4983230072969 + 3 ^ 40 * 7254605 * 2
def baseEnd_7254605 : Nat := 413899924834521562030465

theorem tailTrace_7254605 : CollatzResearch.WordTrace tailWord_7254605 prefixEnd_7254605 413899924834521562030465 := by
  unfold tailWord_7254605
  simp only [CollatzResearch.WordTrace]
  refine ⟨264597181882812547738245269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176398121255208365158830179 264597181882812547738245269)
  ·
    refine ⟨12402992900756838175230247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264597181882812547738245269 12402992900756838175230247)
    ·
      refine ⟨18604489351135257262845371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12402992900756838175230247 18604489351135257262845371)
      ·
        refine ⟨27906734026702885894268057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604489351135257262845371 27906734026702885894268057)
        ·
          refine ⟨20930050520027164420701043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27906734026702885894268057 20930050520027164420701043)
          ·
            refine ⟨31395075780040746631051565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930050520027164420701043 31395075780040746631051565)
            ·
              refine ⟨11773153417515279986644337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31395075780040746631051565 11773153417515279986644337)
              ·
                refine ⟨8829865063136459989983253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11773153417515279986644337 8829865063136459989983253)
                ·
                  refine ⟨413899924834521562030465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8829865063136459989983253 413899924834521562030465)
                  ·
                    rfl

theorem cell23_7254605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_7254605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254605 prefixEnd_7254605 := by exact prefixLift 7254605
  have htrace : WordTrace (prefixWord ++ tailWord_7254605) baseStart_7254605 baseEnd_7254605 := by
    simpa [prefixWord, tailWord_7254605, baseEnd_7254605] using wordTrace_append hprefix tailTrace_7254605
  have hstable : (prefixWord ++ tailWord_7254605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254605).length < 2 ^ (prefixWord ++ tailWord_7254605).sum := by decide
  have hdescent : baseEnd_7254605 < baseStart_7254605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254615 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_7254615 : Nat := 118140960795 + 7254615 * 2 ^ 59
def prefixEnd_7254615 : Nat := 4983230072969 + 3 ^ 40 * 7254615 * 2
def baseEnd_7254615 : Nat := 3725104458317239019149139

theorem tailTrace_7254615 : CollatzResearch.WordTrace tailWord_7254615 prefixEnd_7254615 3725104458317239019149139 := by
  unfold tailWord_7254615
  simp only [CollatzResearch.WordTrace]
  refine ⟨264597546612776319446109299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176398364408517546297406199 264597546612776319446109299)
  ·
    refine ⟨396896319919164479169163949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264597546612776319446109299 396896319919164479169163949)
    ·
      refine ⟨148836119969686679688436481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396896319919164479169163949 148836119969686679688436481)
      ·
        refine ⟨111627089977265009766327361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148836119969686679688436481 111627089977265009766327361)
        ·
          refine ⟨83720317482948757324745521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111627089977265009766327361 83720317482948757324745521)
          ·
            refine ⟨62790238112211567993559141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83720317482948757324745521 62790238112211567993559141)
            ·
              refine ⟨11773169646039668998792339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62790238112211567993559141 11773169646039668998792339)
              ·
                refine ⟨17659754469059503498188509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11773169646039668998792339 17659754469059503498188509)
                ·
                  refine ⟨6622407925897313811820691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17659754469059503498188509 6622407925897313811820691)
                  ·
                    refine ⟨9933611888845970717731037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622407925897313811820691 9933611888845970717731037)
                    ·
                      refine ⟨3725104458317239019149139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933611888845970717731037 3725104458317239019149139)
                      ·
                        rfl

theorem cell23_7254615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_7254615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254615 prefixEnd_7254615 := by exact prefixLift 7254615
  have htrace : WordTrace (prefixWord ++ tailWord_7254615) baseStart_7254615 baseEnd_7254615 := by
    simpa [prefixWord, tailWord_7254615, baseEnd_7254615] using wordTrace_append hprefix tailTrace_7254615
  have hstable : (prefixWord ++ tailWord_7254615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254615).length < 2 ^ (prefixWord ++ tailWord_7254615).sum := by decide
  have hdescent : baseEnd_7254615 < baseStart_7254615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254649 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 1, 1, 3]
def baseStart_7254649 : Nat := 118140960795 + 7254649 * 2 ^ 59
def prefixEnd_7254649 : Nat := 4983230072969 + 3 ^ 40 * 7254649 * 2
def baseEnd_7254649 : Nat := 3725121916659491886123983

theorem tailTrace_7254649 : CollatzResearch.WordTrace tailWord_7254649 prefixEnd_7254649 3725121916659491886123983 := by
  unfold tailWord_7254649
  simp only [CollatzResearch.WordTrace]
  refine ⟨264598786694653143252847001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176399191129768762168564667 264598786694653143252847001)
  ·
    refine ⟨198449090020989857439635251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264598786694653143252847001 198449090020989857439635251)
    ·
      refine ⟨297673635031484786159452877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198449090020989857439635251 297673635031484786159452877)
      ·
        refine ⟨111627613136806794809794829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297673635031484786159452877 111627613136806794809794829)
        ·
          refine ⟨41860354926302548053673061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111627613136806794809794829 41860354926302548053673061)
          ·
            refine ⟨7848816548681727760063699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41860354926302548053673061 7848816548681727760063699)
            ·
              refine ⟨11773224823022591640095549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848816548681727760063699 11773224823022591640095549)
              ·
                refine ⟨4414959308633471865035831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11773224823022591640095549 4414959308633471865035831)
                ·
                  refine ⟨6622438962950207797553747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414959308633471865035831 6622438962950207797553747)
                  ·
                    refine ⟨9933658444425311696330621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622438962950207797553747 9933658444425311696330621)
                    ·
                      refine ⟨3725121916659491886123983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933658444425311696330621 3725121916659491886123983)
                      ·
                        rfl

theorem cell23_7254649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_7254649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254649 prefixEnd_7254649 := by exact prefixLift 7254649
  have htrace : WordTrace (prefixWord ++ tailWord_7254649) baseStart_7254649 baseEnd_7254649 := by
    simpa [prefixWord, tailWord_7254649, baseEnd_7254649] using wordTrace_append hprefix tailTrace_7254649
  have hstable : (prefixWord ++ tailWord_7254649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254649).length < 2 ^ (prefixWord ++ tailWord_7254649).sum := by decide
  have hdescent : baseEnd_7254649 < baseStart_7254649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254661 : List Nat := [1, 3, 1, 1, 4, 2, 11]
def baseStart_7254661 : Nat := 118140960795 + 7254661 * 2 ^ 59
def prefixEnd_7254661 : Nat := 4983230072969 + 3 ^ 40 * 7254661 * 2
def baseEnd_7254661 : Nat := 45989235536140072088567

theorem tailTrace_7254661 : CollatzResearch.WordTrace tailWord_7254661 prefixEnd_7254661 45989235536140072088567 := by
  unfold tailWord_7254661
  simp only [CollatzResearch.WordTrace]
  refine ⟨264599224370609669302283837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176399482913739779534855891 264599224370609669302283837)
  ·
    refine ⟨99224709138978625988356439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264599224370609669302283837 99224709138978625988356439)
    ·
      refine ⟨148837063708467938982534659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99224709138978625988356439 148837063708467938982534659)
      ·
        refine ⟨223255595562701908473801989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148837063708467938982534659 223255595562701908473801989)
        ·
          refine ⟨41860424168006607838837873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223255595562701908473801989 41860424168006607838837873)
          ·
            refine ⟨31395318126004955879128405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41860424168006607838837873 31395318126004955879128405)
            ·
              refine ⟨45989235536140072088567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31395318126004955879128405 45989235536140072088567)
              ·
                rfl

theorem cell23_7254661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 11].length) (baseStart_7254661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254661 prefixEnd_7254661 := by exact prefixLift 7254661
  have htrace : WordTrace (prefixWord ++ tailWord_7254661) baseStart_7254661 baseEnd_7254661 := by
    simpa [prefixWord, tailWord_7254661, baseEnd_7254661] using wordTrace_append hprefix tailTrace_7254661
  have hstable : (prefixWord ++ tailWord_7254661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254661).length < 2 ^ (prefixWord ++ tailWord_7254661).sum := by decide
  have hdescent : baseEnd_7254661 < baseStart_7254661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254666 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7254666 : Nat := 118140960795 + 7254666 * 2 ^ 59
def prefixEnd_7254666 : Nat := 4983230072969 + 3 ^ 40 * 7254666 * 2
def baseEnd_7254666 : Nat := 3725130645830618319611405

theorem tailTrace_7254666 : CollatzResearch.WordTrace tailWord_7254666 prefixEnd_7254666 3725130645830618319611405 := by
  unfold tailWord_7254666
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149851683897888789053963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176399604490394370104143901 66149851683897888789053963)
  ·
    refine ⟨99224777525846833183580945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66149851683897888789053963 99224777525846833183580945)
    ·
      refine ⟨74418583144385124887685709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99224777525846833183580945 74418583144385124887685709)
      ·
        refine ⟨27906968679144421832882141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74418583144385124887685709 27906968679144421832882141)
        ·
          refine ⟨10465113254679158187330803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27906968679144421832882141 10465113254679158187330803)
          ·
            refine ⟨15697669882018737280996205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465113254679158187330803 15697669882018737280996205)
            ·
              refine ⟨5886626205757026480373577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15697669882018737280996205 5886626205757026480373577)
              ·
                refine ⟨4414969654317769860280183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886626205757026480373577 4414969654317769860280183)
                ·
                  refine ⟨6622454481476654790420275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414969654317769860280183 6622454481476654790420275)
                  ·
                    refine ⟨9933681722214982185630413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622454481476654790420275 9933681722214982185630413)
                    ·
                      refine ⟨3725130645830618319611405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933681722214982185630413 3725130645830618319611405)
                      ·
                        rfl

theorem cell23_7254666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7254666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254666 prefixEnd_7254666 := by exact prefixLift 7254666
  have htrace : WordTrace (prefixWord ++ tailWord_7254666) baseStart_7254666 baseEnd_7254666 := by
    simpa [prefixWord, tailWord_7254666, baseEnd_7254666] using wordTrace_append hprefix tailTrace_7254666
  have hstable : (prefixWord ++ tailWord_7254666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254666).length < 2 ^ (prefixWord ++ tailWord_7254666).sum := by decide
  have hdescent : baseEnd_7254666 < baseStart_7254666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254681 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7254681 : Nat := 118140960795 + 7254681 * 2 ^ 59
def prefixEnd_7254681 : Nat := 4983230072969 + 3 ^ 40 * 7254681 * 2
def baseEnd_7254681 : Nat := 3725138348040435760923835

theorem tailTrace_7254681 : CollatzResearch.WordTrace tailWord_7254681 prefixEnd_7254681 3725138348040435760923835 := by
  unfold tailWord_7254681
  simp only [CollatzResearch.WordTrace]
  refine ⟨264599953830537212718011897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176399969220358141812007931 264599953830537212718011897)
  ·
    refine ⟨198449965372902909538508923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264599953830537212718011897 198449965372902909538508923)
    ·
      refine ⟨297674948059354364307763385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198449965372902909538508923 297674948059354364307763385)
      ·
        refine ⟨223256211044515773230822539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297674948059354364307763385 223256211044515773230822539)
        ·
          refine ⟨334884316566773659846233809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223256211044515773230822539 334884316566773659846233809)
          ·
            refine ⟨251163237425080244884675357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334884316566773659846233809 251163237425080244884675357)
            ·
              refine ⟨94186214034405091831753259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251163237425080244884675357 94186214034405091831753259)
              ·
                refine ⟨141279321051607637747629889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94186214034405091831753259 141279321051607637747629889)
                ·
                  refine ⟨105959490788705728310722417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141279321051607637747629889 105959490788705728310722417)
                  ·
                    refine ⟨79469618091529296233041813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105959490788705728310722417 79469618091529296233041813)
                    ·
                      refine ⟨3725138348040435760923835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79469618091529296233041813 3725138348040435760923835)
                      ·
                        rfl

theorem cell23_7254681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7254681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254681 prefixEnd_7254681 := by exact prefixLift 7254681
  have htrace : WordTrace (prefixWord ++ tailWord_7254681) baseStart_7254681 baseEnd_7254681 := by
    simpa [prefixWord, tailWord_7254681, baseEnd_7254681] using wordTrace_append hprefix tailTrace_7254681
  have hstable : (prefixWord ++ tailWord_7254681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254681).length < 2 ^ (prefixWord ++ tailWord_7254681).sum := by decide
  have hdescent : baseEnd_7254681 < baseStart_7254681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254689 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7254689 : Nat := 118140960795 + 7254689 * 2 ^ 59
def prefixEnd_7254689 : Nat := 4983230072969 + 3 ^ 40 * 7254689 * 2
def baseEnd_7254689 : Nat := 3725142455885671729623799

theorem tailTrace_7254689 : CollatzResearch.WordTrace tailWord_7254689 prefixEnd_7254689 3725142455885671729623799 := by
  unfold tailWord_7254689
  simp only [CollatzResearch.WordTrace]
  refine ⟨264600245614508230084303121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176400163743005486722868747 264600245614508230084303121)
  ·
    refine ⟨198450184210881172563227341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264600245614508230084303121 198450184210881172563227341)
    ·
      refine ⟨74418819079080439711210253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198450184210881172563227341 74418819079080439711210253)
      ·
        refine ⟨27907057154655164891703845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74418819079080439711210253 27907057154655164891703845)
        ·
          refine ⟨5232573216497843417194471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27907057154655164891703845 5232573216497843417194471)
          ·
            refine ⟨7848859824746765125791707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232573216497843417194471 7848859824746765125791707)
            ·
              refine ⟨11773289737120147688687561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848859824746765125791707 11773289737120147688687561)
              ·
                refine ⟨8829967302840110766515671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11773289737120147688687561 8829967302840110766515671)
                ·
                  refine ⟨13244950954260166149773507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829967302840110766515671 13244950954260166149773507)
                  ·
                    refine ⟨19867426431390249224660261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13244950954260166149773507 19867426431390249224660261)
                    ·
                      refine ⟨3725142455885671729623799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19867426431390249224660261 3725142455885671729623799)
                      ·
                        rfl

theorem cell23_7254689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7254689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254689 prefixEnd_7254689 := by exact prefixLift 7254689
  have htrace : WordTrace (prefixWord ++ tailWord_7254689) baseStart_7254689 baseEnd_7254689 := by
    simpa [prefixWord, tailWord_7254689, baseEnd_7254689] using wordTrace_append hprefix tailTrace_7254689
  have hstable : (prefixWord ++ tailWord_7254689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254689).length < 2 ^ (prefixWord ++ tailWord_7254689).sum := by decide
  have hdescent : baseEnd_7254689 < baseStart_7254689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254691 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 7]
def baseStart_7254691 : Nat := 118140960795 + 7254691 * 2 ^ 59
def prefixEnd_7254691 : Nat := 4983230072969 + 3 ^ 40 * 7254691 * 2
def baseEnd_7254691 : Nat := 1241714494282326907266263

theorem tailTrace_7254691 : CollatzResearch.WordTrace tailWord_7254691 prefixEnd_7254691 1241714494282326907266263 := by
  unfold tailWord_7254691
  simp only [CollatzResearch.WordTrace]
  refine ⟨264600318560500984425875927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176400212373667322950583951 264600318560500984425875927)
  ·
    refine ⟨396900477840751476638813891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264600318560500984425875927 396900477840751476638813891)
    ·
      refine ⟨595350716761127214958220837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396900477840751476638813891 595350716761127214958220837)
      ·
        refine ⟨111628259392711352804666407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595350716761127214958220837 111628259392711352804666407)
        ·
          refine ⟨167442389089067029206999611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111628259392711352804666407 167442389089067029206999611)
          ·
            refine ⟨251163583633600543810499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167442389089067029206999611 251163583633600543810499417)
            ·
              refine ⟨188372687725200407857874563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251163583633600543810499417 188372687725200407857874563)
              ·
                refine ⟨282559031587800611786811845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188372687725200407857874563 282559031587800611786811845)
                ·
                  refine ⟨52979818422712614710027221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282559031587800611786811845 52979818422712614710027221)
                  ·
                    refine ⟨1241714494282326907266263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52979818422712614710027221 1241714494282326907266263)
                    ·
                      rfl

theorem cell23_7254691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_7254691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254691 prefixEnd_7254691 := by exact prefixLift 7254691
  have htrace : WordTrace (prefixWord ++ tailWord_7254691) baseStart_7254691 baseEnd_7254691 := by
    simpa [prefixWord, tailWord_7254691, baseEnd_7254691] using wordTrace_append hprefix tailTrace_7254691
  have hstable : (prefixWord ++ tailWord_7254691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254691).length < 2 ^ (prefixWord ++ tailWord_7254691).sum := by decide
  have hdescent : baseEnd_7254691 < baseStart_7254691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254702 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7254702 : Nat := 118140960795 + 7254702 * 2 ^ 59
def prefixEnd_7254702 : Nat := 4983230072969 + 3 ^ 40 * 7254702 * 2
def baseEnd_7254702 : Nat := 3725149131134180178761239

theorem tailTrace_7254702 : CollatzResearch.WordTrace tailWord_7254702 prefixEnd_7254702 3725149131134180178761239 := by
  unfold tailWord_7254702
  simp only [CollatzResearch.WordTrace]
  refine ⟨33075089970432641663065795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176400479842307422203017573 33075089970432641663065795)
  ·
    refine ⟨49612634955648962494598693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33075089970432641663065795 49612634955648962494598693)
    ·
      refine ⟨9302369054184180467737255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49612634955648962494598693 9302369054184180467737255)
      ·
        refine ⟨13953553581276270701605883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302369054184180467737255 13953553581276270701605883)
        ·
          refine ⟨20930330371914406052408825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953553581276270701605883 20930330371914406052408825)
          ·
            refine ⟨15697747778935804539306619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930330371914406052408825 15697747778935804539306619)
            ·
              refine ⟨23546621668403706808959929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697747778935804539306619 23546621668403706808959929)
              ·
                refine ⟨17659966251302780106719947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23546621668403706808959929 17659966251302780106719947)
                ·
                  refine ⟨26489949376954170160079921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17659966251302780106719947 26489949376954170160079921)
                  ·
                    refine ⟨19867462032715627620059941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26489949376954170160079921 19867462032715627620059941)
                    ·
                      refine ⟨3725149131134180178761239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19867462032715627620059941 3725149131134180178761239)
                      ·
                        rfl

theorem cell23_7254702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7254702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254702 prefixEnd_7254702 := by exact prefixLift 7254702
  have htrace : WordTrace (prefixWord ++ tailWord_7254702) baseStart_7254702 baseEnd_7254702 := by
    simpa [prefixWord, tailWord_7254702, baseEnd_7254702] using wordTrace_append hprefix tailTrace_7254702
  have hstable : (prefixWord ++ tailWord_7254702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254702).length < 2 ^ (prefixWord ++ tailWord_7254702).sum := by decide
  have hdescent : baseEnd_7254702 < baseStart_7254702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254709 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7254709 : Nat := 118140960795 + 7254709 * 2 ^ 59
def prefixEnd_7254709 : Nat := 4983230072969 + 3 ^ 40 * 7254709 * 2
def baseEnd_7254709 : Nat := 3725152725498761651373707

theorem tailTrace_7254709 : CollatzResearch.WordTrace tailWord_7254709 prefixEnd_7254709 3725152725498761651373707 := by
  unfold tailWord_7254709
  simp only [CollatzResearch.WordTrace]
  refine ⟨264600975074435773500031181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176400650049623849000020787 264600975074435773500031181)
  ·
    refine ⟨99225365652913415062511693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264600975074435773500031181 99225365652913415062511693)
    ·
      refine ⟨37209512119842530648441885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99225365652913415062511693 37209512119842530648441885)
      ·
        refine ⟨13953567044940948993165707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37209512119842530648441885 13953567044940948993165707)
        ·
          refine ⟨20930350567411423489748561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953567044940948993165707 20930350567411423489748561)
          ·
            refine ⟨15697762925558567617311421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930350567411423489748561 15697762925558567617311421)
            ·
              refine ⟨5886661097084462856491783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15697762925558567617311421 5886661097084462856491783)
              ·
                refine ⟨8829991645626694284737675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886661097084462856491783 8829991645626694284737675)
                ·
                  refine ⟨13244987468440041427106513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829991645626694284737675 13244987468440041427106513)
                  ·
                    refine ⟨9933740601330031070329885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13244987468440041427106513 9933740601330031070329885)
                    ·
                      refine ⟨3725152725498761651373707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933740601330031070329885 3725152725498761651373707)
                      ·
                        rfl

theorem cell23_7254709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7254709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254709 prefixEnd_7254709 := by exact prefixLift 7254709
  have htrace : WordTrace (prefixWord ++ tailWord_7254709) baseStart_7254709 baseEnd_7254709 := by
    simpa [prefixWord, tailWord_7254709, baseEnd_7254709] using wordTrace_append hprefix tailTrace_7254709
  have hstable : (prefixWord ++ tailWord_7254709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254709).length < 2 ^ (prefixWord ++ tailWord_7254709).sum := by decide
  have hdescent : baseEnd_7254709 < baseStart_7254709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254728 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7254728 : Nat := 118140960795 + 7254728 * 2 ^ 59
def prefixEnd_7254728 : Nat := 4983230072969 + 3 ^ 40 * 7254728 * 2
def baseEnd_7254728 : Nat := 3725162481631197077036119

theorem tailTrace_7254728 : CollatzResearch.WordTrace tailWord_7254728 prefixEnd_7254728 3725162481631197077036119 := by
  unfold tailWord_7254728
  simp only [CollatzResearch.WordTrace]
  refine ⟨132300834030683469872486419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176401112040911293163315225 132300834030683469872486419)
  ·
    refine ⟨198451251046025204808729629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132300834030683469872486419 198451251046025204808729629)
    ·
      refine ⟨74419219142259451803273611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198451251046025204808729629 74419219142259451803273611)
      ·
        refine ⟨111628828713389177704910417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74419219142259451803273611 111628828713389177704910417)
        ·
          refine ⟨83721621535041883278682813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111628828713389177704910417 83721621535041883278682813)
          ·
            refine ⟨31395608075640706229506055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83721621535041883278682813 31395608075640706229506055)
            ·
              refine ⟨47093412113461059344259083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31395608075640706229506055 47093412113461059344259083)
              ·
                refine ⟨70640118170191589016388625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47093412113461059344259083 70640118170191589016388625)
                ·
                  refine ⟨52980088627643691762291469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70640118170191589016388625 52980088627643691762291469)
                  ·
                    refine ⟨19867533235366384410859301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52980088627643691762291469 19867533235366384410859301)
                    ·
                      refine ⟨3725162481631197077036119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19867533235366384410859301 3725162481631197077036119)
                      ·
                        rfl

theorem cell23_7254728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7254728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254728 prefixEnd_7254728 := by exact prefixLift 7254728
  have htrace : WordTrace (prefixWord ++ tailWord_7254728) baseStart_7254728 baseEnd_7254728 := by
    simpa [prefixWord, tailWord_7254728, baseEnd_7254728] using wordTrace_append hprefix tailTrace_7254728
  have hstable : (prefixWord ++ tailWord_7254728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254728).length < 2 ^ (prefixWord ++ tailWord_7254728).sum := by decide
  have hdescent : baseEnd_7254728 < baseStart_7254728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254732 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7254732 : Nat := 118140960795 + 7254732 * 2 ^ 59
def prefixEnd_7254732 : Nat := 4983230072969 + 3 ^ 40 * 7254732 * 2
def baseEnd_7254732 : Nat := 3725164535553815061386101

theorem tailTrace_7254732 : CollatzResearch.WordTrace tailWord_7254732 prefixEnd_7254732 3725164535553815061386101 := by
  unfold tailWord_7254732
  simp only [CollatzResearch.WordTrace]
  refine ⟨132300906976676224214059225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176401209302234965618745633 132300906976676224214059225)
  ·
    refine ⟨99225680232507168160544419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132300906976676224214059225 99225680232507168160544419)
    ·
      refine ⟨148838520348760752240816629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99225680232507168160544419 148838520348760752240816629)
      ·
        refine ⟨13953611282696320522576559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148838520348760752240816629 13953611282696320522576559)
        ·
          refine ⟨20930416924044480783864839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953611282696320522576559 20930416924044480783864839)
          ·
            refine ⟨31395625386066721175797259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930416924044480783864839 31395625386066721175797259)
            ·
              refine ⟨47093438079100081763695889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31395625386066721175797259 47093438079100081763695889)
              ·
                refine ⟨35320078559325061322771917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47093438079100081763695889 35320078559325061322771917)
                ·
                  refine ⟨13245029459746897996039469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35320078559325061322771917 13245029459746897996039469)
                  ·
                    refine ⟨4966886047405086748514801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13245029459746897996039469 4966886047405086748514801)
                    ·
                      refine ⟨3725164535553815061386101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966886047405086748514801 3725164535553815061386101)
                      ·
                        rfl

theorem cell23_7254732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7254732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254732 prefixEnd_7254732 := by exact prefixLift 7254732
  have htrace : WordTrace (prefixWord ++ tailWord_7254732) baseStart_7254732 baseEnd_7254732 := by
    simpa [prefixWord, tailWord_7254732, baseEnd_7254732] using wordTrace_append hprefix tailTrace_7254732
  have hstable : (prefixWord ++ tailWord_7254732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254732).length < 2 ^ (prefixWord ++ tailWord_7254732).sum := by decide
  have hdescent : baseEnd_7254732 < baseStart_7254732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254762 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_7254762 : Nat := 118140960795 + 7254762 * 2 ^ 59
def prefixEnd_7254762 : Nat := 4983230072969 + 3 ^ 40 * 7254762 * 2
def baseEnd_7254762 : Nat := 3725179939973449944010963

theorem tailTrace_7254762 : CollatzResearch.WordTrace tailWord_7254762 prefixEnd_7254762 3725179939973449944010963 := by
  unfold tailWord_7254762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66150727035810940887927635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176401938762162509034473693 66150727035810940887927635)
  ·
    refine ⟨99226090553716411331891453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66150727035810940887927635 99226090553716411331891453)
    ·
      refine ⟨37209783957643654249459295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99226090553716411331891453 37209783957643654249459295)
      ·
        refine ⟨55814675936465481374188943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37209783957643654249459295 55814675936465481374188943)
        ·
          refine ⟨83722013904698222061283415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55814675936465481374188943 83722013904698222061283415)
          ·
            refine ⟨125583020857047333091925123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83722013904698222061283415 125583020857047333091925123)
            ·
              refine ⟨188374531285570999637887685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125583020857047333091925123 188374531285570999637887685)
              ·
                refine ⟨35320224616044562432103941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188374531285570999637887685 35320224616044562432103941)
                ·
                  refine ⟨6622542115508355456019489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35320224616044562432103941 6622542115508355456019489)
                  ·
                    refine ⟨4966906586631266592014617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622542115508355456019489 4966906586631266592014617)
                    ·
                      refine ⟨3725179939973449944010963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966906586631266592014617 3725179939973449944010963)
                      ·
                        rfl

theorem cell23_7254762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_7254762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254762 prefixEnd_7254762 := by exact prefixLift 7254762
  have htrace : WordTrace (prefixWord ++ tailWord_7254762) baseStart_7254762 baseEnd_7254762 := by
    simpa [prefixWord, tailWord_7254762, baseEnd_7254762] using wordTrace_append hprefix tailTrace_7254762
  have hstable : (prefixWord ++ tailWord_7254762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254762).length < 2 ^ (prefixWord ++ tailWord_7254762).sum := by decide
  have hdescent : baseEnd_7254762 < baseStart_7254762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254766 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_7254766 : Nat := 118140960795 + 7254766 * 2 ^ 59
def prefixEnd_7254766 : Nat := 4983230072969 + 3 ^ 40 * 7254766 * 2
def baseEnd_7254766 : Nat := 3725181993896067928360945

theorem tailTrace_7254766 : CollatzResearch.WordTrace tailWord_7254766 prefixEnd_7254766 3725181993896067928360945 := by
  unfold tailWord_7254766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33075381754403659029357019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176402036023486181489904101 33075381754403659029357019)
  ·
    refine ⟨49613072631605488544035529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33075381754403659029357019 49613072631605488544035529)
    ·
      refine ⟨37209804473704116408026647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49613072631605488544035529 37209804473704116408026647)
      ·
        refine ⟨55814706710556174612039971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37209804473704116408026647 55814706710556174612039971)
        ·
          refine ⟨83722060065834261918059957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55814706710556174612039971 83722060065834261918059957)
          ·
            refine ⟨7848943131171962054818121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83722060065834261918059957 7848943131171962054818121)
            ·
              refine ⟨5886707348378971541113591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7848943131171962054818121 5886707348378971541113591)
              ·
                refine ⟨8830061022568457311670387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886707348378971541113591 8830061022568457311670387)
                ·
                  refine ⟨13245091533852685967505581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830061022568457311670387 13245091533852685967505581)
                  ·
                    refine ⟨4966909325194757237814593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13245091533852685967505581 4966909325194757237814593)
                    ·
                      refine ⟨3725181993896067928360945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4966909325194757237814593 3725181993896067928360945)
                      ·
                        rfl

theorem cell23_7254766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_7254766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254766 prefixEnd_7254766 := by exact prefixLift 7254766
  have htrace : WordTrace (prefixWord ++ tailWord_7254766) baseStart_7254766 baseEnd_7254766 := by
    simpa [prefixWord, tailWord_7254766, baseEnd_7254766] using wordTrace_append hprefix tailTrace_7254766
  have hstable : (prefixWord ++ tailWord_7254766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254766).length < 2 ^ (prefixWord ++ tailWord_7254766).sum := by decide
  have hdescent : baseEnd_7254766 < baseStart_7254766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254808 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7254808 : Nat := 118140960795 + 7254808 * 2 ^ 59
def prefixEnd_7254808 : Nat := 4983230072969 + 3 ^ 40 * 7254808 * 2
def baseEnd_7254808 : Nat := 3725203560083556764035751

theorem tailTrace_7254808 : CollatzResearch.WordTrace tailWord_7254808 prefixEnd_7254808 3725203560083556764035751 := by
  unfold tailWord_7254808
  simp only [CollatzResearch.WordTrace]
  refine ⟨132302292950538556703942539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176403057267384742271923385 132302292950538556703942539)
  ·
    refine ⟨198453439425807835055913809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132302292950538556703942539 198453439425807835055913809)
    ·
      refine ⟨148840079569355876291935357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198453439425807835055913809 148840079569355876291935357)
      ·
        refine ⟨55815029838508453609475759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148840079569355876291935357 55815029838508453609475759)
        ·
          refine ⟨83722544757762680414213639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55815029838508453609475759 83722544757762680414213639)
          ·
            refine ⟨125583817136644020621320459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83722544757762680414213639 125583817136644020621320459)
            ·
              refine ⟨188375725704966030931980689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125583817136644020621320459 188375725704966030931980689)
              ·
                refine ⟨141281794278724523198985517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188375725704966030931980689 141281794278724523198985517)
                ·
                  refine ⟨52980672854521696199619569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141281794278724523198985517 52980672854521696199619569)
                  ·
                    refine ⟨39735504640891272149714677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52980672854521696199619569 39735504640891272149714677)
                    ·
                      refine ⟨3725203560083556764035751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39735504640891272149714677 3725203560083556764035751)
                      ·
                        rfl

theorem cell23_7254808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7254808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254808 prefixEnd_7254808 := by exact prefixLift 7254808
  have htrace : WordTrace (prefixWord ++ tailWord_7254808) baseStart_7254808 baseEnd_7254808 := by
    simpa [prefixWord, tailWord_7254808, baseEnd_7254808] using wordTrace_append hprefix tailTrace_7254808
  have hstable : (prefixWord ++ tailWord_7254808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254808).length < 2 ^ (prefixWord ++ tailWord_7254808).sum := by decide
  have hdescent : baseEnd_7254808 < baseStart_7254808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254835 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4]
def baseStart_7254835 : Nat := 118140960795 + 7254835 * 2 ^ 59
def prefixEnd_7254835 : Nat := 4983230072969 + 3 ^ 40 * 7254835 * 2
def baseEnd_7254835 : Nat := 3725217424061228158398127

theorem tailTrace_7254835 : CollatzResearch.WordTrace tailWord_7254835 prefixEnd_7254835 3725217424061228158398127 := by
  unfold tailWord_7254835
  simp only [CollatzResearch.WordTrace]
  refine ⟨264605570671979297019117959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176403713781319531346078639 264605570671979297019117959)
  ·
    refine ⟨396908356007968945528676939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264605570671979297019117959 396908356007968945528676939)
    ·
      refine ⟨595362534011953418293015409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396908356007968945528676939 595362534011953418293015409)
      ·
        refine ⟨446521900508965063719761557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595362534011953418293015409 446521900508965063719761557)
        ·
          refine ⟨20930714086357737361863823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446521900508965063719761557 20930714086357737361863823)
          ·
            refine ⟨31396071129536606042795735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930714086357737361863823 31396071129536606042795735)
            ·
              refine ⟨47094106694304909064193603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31396071129536606042795735 47094106694304909064193603)
              ·
                refine ⟨70641160041457363596290405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47094106694304909064193603 70641160041457363596290405)
                ·
                  refine ⟨13245217507773255674304451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70641160041457363596290405 13245217507773255674304451)
                  ·
                    refine ⟨19867826261659883511456677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13245217507773255674304451 19867826261659883511456677)
                    ·
                      refine ⟨3725217424061228158398127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19867826261659883511456677 3725217424061228158398127)
                      ·
                        rfl

theorem cell23_7254835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_7254835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254835 prefixEnd_7254835 := by exact prefixLift 7254835
  have htrace : WordTrace (prefixWord ++ tailWord_7254835) baseStart_7254835 baseEnd_7254835 := by
    simpa [prefixWord, tailWord_7254835, baseEnd_7254835] using wordTrace_append hprefix tailTrace_7254835
  have hstable : (prefixWord ++ tailWord_7254835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254835).length < 2 ^ (prefixWord ++ tailWord_7254835).sum := by decide
  have hdescent : baseEnd_7254835 < baseStart_7254835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254836 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7254836 : Nat := 118140960795 + 7254836 * 2 ^ 59
def prefixEnd_7254836 : Nat := 4983230072969 + 3 ^ 40 * 7254836 * 2
def baseEnd_7254836 : Nat := 413913104171320294942847

theorem tailTrace_7254836 : CollatzResearch.WordTrace tailWord_7254836 prefixEnd_7254836 413913104171320294942847 := by
  unfold tailWord_7254836
  simp only [CollatzResearch.WordTrace]
  refine ⟨132302803572487837094952181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176403738096650449459936241 132302803572487837094952181)
  ·
    refine ⟨12403387834920734727651767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132302803572487837094952181 12403387834920734727651767)
    ·
      refine ⟨18605081752381102091477651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12403387834920734727651767 18605081752381102091477651)
      ·
        refine ⟨27907622628571653137216477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605081752381102091477651 27907622628571653137216477)
        ·
          refine ⟨10465358485714369926456179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27907622628571653137216477 10465358485714369926456179)
          ·
            refine ⟨15698037728571554889684269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465358485714369926456179 15698037728571554889684269)
            ·
              refine ⟨5886764148214333083631601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15698037728571554889684269 5886764148214333083631601)
              ·
                refine ⟨4415073111160749812723701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886764148214333083631601 4415073111160749812723701)
                ·
                  refine ⟨413913104171320294942847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4415073111160749812723701 413913104171320294942847)
                  ·
                    rfl

theorem cell23_7254836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7254836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254836 prefixEnd_7254836 := by exact prefixLift 7254836
  have htrace : WordTrace (prefixWord ++ tailWord_7254836) baseStart_7254836 baseEnd_7254836 := by
    simpa [prefixWord, tailWord_7254836, baseEnd_7254836] using wordTrace_append hprefix tailTrace_7254836
  have hstable : (prefixWord ++ tailWord_7254836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254836).length < 2 ^ (prefixWord ++ tailWord_7254836).sum := by decide
  have hdescent : baseEnd_7254836 < baseStart_7254836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254848 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_7254848 : Nat := 118140960795 + 7254848 * 2 ^ 59
def prefixEnd_7254848 : Nat := 4983230072969 + 3 ^ 40 * 7254848 * 2
def baseEnd_7254848 : Nat := 3725224099309736607535567

theorem tailTrace_7254848 : CollatzResearch.WordTrace tailWord_7254848 prefixEnd_7254848 3725224099309736607535567 := by
  unfold tailWord_7254848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132303022410466100119670599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176404029880621466826227465 132303022410466100119670599)
  ·
    refine ⟨198454533615699150179505899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132303022410466100119670599 198454533615699150179505899)
    ·
      refine ⟨297681800423548725269258849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198454533615699150179505899 297681800423548725269258849)
      ·
        refine ⟨223261350317661543951944137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297681800423548725269258849 223261350317661543951944137)
        ·
          refine ⟨167446012738246157963958103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223261350317661543951944137 167446012738246157963958103)
          ·
            refine ⟨251169019107369236945937155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167446012738246157963958103 251169019107369236945937155)
            ·
              refine ⟨376753528661053855418905733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251169019107369236945937155 376753528661053855418905733)
              ·
                refine ⟨70641286623947597891044825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376753528661053855418905733 70641286623947597891044825)
                ·
                  refine ⟨52980964967960698418283619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70641286623947597891044825 52980964967960698418283619)
                  ·
                    refine ⟨79471447451941047627425429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52980964967960698418283619 79471447451941047627425429)
                    ·
                      refine ⟨3725224099309736607535567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79471447451941047627425429 3725224099309736607535567)
                      ·
                        rfl

theorem cell23_7254848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_7254848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254848 prefixEnd_7254848 := by exact prefixLift 7254848
  have htrace : WordTrace (prefixWord ++ tailWord_7254848) baseStart_7254848 baseEnd_7254848 := by
    simpa [prefixWord, tailWord_7254848, baseEnd_7254848] using wordTrace_append hprefix tailTrace_7254848
  have hstable : (prefixWord ++ tailWord_7254848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254848).length < 2 ^ (prefixWord ++ tailWord_7254848).sum := by decide
  have hdescent : baseEnd_7254848 < baseStart_7254848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254855 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_7254855 : Nat := 118140960795 + 7254855 * 2 ^ 59
def prefixEnd_7254855 : Nat := 4983230072969 + 3 ^ 40 * 7254855 * 2
def baseEnd_7254855 : Nat := 3725227693674318080148035

theorem tailTrace_7254855 : CollatzResearch.WordTrace tailWord_7254855 prefixEnd_7254855 3725227693674318080148035 := by
  unfold tailWord_7254855
  simp only [CollatzResearch.WordTrace]
  refine ⟨264606300131906840434846019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176404200087937893623230679 264606300131906840434846019)
  ·
    refine ⟨396909450197860260652269029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264606300131906840434846019 396909450197860260652269029)
    ·
      refine ⟨74420521912098798872300443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396909450197860260652269029 74420521912098798872300443)
      ·
        refine ⟨111630782868148198308450665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74420521912098798872300443 111630782868148198308450665)
        ·
          refine ⟨83723087151111148731337999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111630782868148198308450665 83723087151111148731337999)
          ·
            refine ⟨125584630726666723097006999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83723087151111148731337999 125584630726666723097006999)
            ·
              refine ⟨188376946090000084645510499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125584630726666723097006999 188376946090000084645510499)
              ·
                refine ⟨282565419135000126968265749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188376946090000084645510499 282565419135000126968265749)
                ·
                  refine ⟨13245254021953130951637457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282565419135000126968265749 13245254021953130951637457)
                  ·
                    refine ⟨9933940516464848213728093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13245254021953130951637457 9933940516464848213728093)
                    ·
                      refine ⟨3725227693674318080148035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9933940516464848213728093 3725227693674318080148035)
                      ·
                        rfl

theorem cell23_7254855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_7254855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254855 prefixEnd_7254855 := by exact prefixLift 7254855
  have htrace : WordTrace (prefixWord ++ tailWord_7254855) baseStart_7254855 baseEnd_7254855 := by
    simpa [prefixWord, tailWord_7254855, baseEnd_7254855] using wordTrace_append hprefix tailTrace_7254855
  have hstable : (prefixWord ++ tailWord_7254855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254855).length < 2 ^ (prefixWord ++ tailWord_7254855).sum := by decide
  have hdescent : baseEnd_7254855 < baseStart_7254855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254858 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_7254858 : Nat := 118140960795 + 7254858 * 2 ^ 59
def prefixEnd_7254858 : Nat := 4983230072969 + 3 ^ 40 * 7254858 * 2
def baseEnd_7254858 : Nat := 413914359346253507601169

theorem tailTrace_7254858 : CollatzResearch.WordTrace tailWord_7254858 prefixEnd_7254858 413914359346253507601169 := by
  unfold tailWord_7254858
  simp only [CollatzResearch.WordTrace]
  refine ⟨66151602387723992986801307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176404273033930647964803485 66151602387723992986801307)
  ·
    refine ⟨99227403581585989480201961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66151602387723992986801307 99227403581585989480201961)
    ·
      refine ⟨74420552686189492110151471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99227403581585989480201961 74420552686189492110151471)
      ·
        refine ⟨111630829029284238165227207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74420552686189492110151471 111630829029284238165227207)
        ·
          refine ⟨167446243543926357247840811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111630829029284238165227207 167446243543926357247840811)
          ·
            refine ⟨251169365315889535871761217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167446243543926357247840811 251169365315889535871761217)
            ·
              refine ⟨188377023986917151903820913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251169365315889535871761217 188377023986917151903820913)
              ·
                refine ⟨141282767990187863927865685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188377023986917151903820913 141282767990187863927865685)
                ·
                  refine ⟨413914359346253507601169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141282767990187863927865685 413914359346253507601169)
                  ·
                    rfl

theorem cell23_7254858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_7254858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254858 prefixEnd_7254858 := by exact prefixLift 7254858
  have htrace : WordTrace (prefixWord ++ tailWord_7254858) baseStart_7254858 baseEnd_7254858 := by
    simpa [prefixWord, tailWord_7254858, baseEnd_7254858] using wordTrace_append hprefix tailTrace_7254858
  have hstable : (prefixWord ++ tailWord_7254858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254858).length < 2 ^ (prefixWord ++ tailWord_7254858).sum := by decide
  have hdescent : baseEnd_7254858 < baseStart_7254858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254905 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_7254905 : Nat := 118140960795 + 7254905 * 2 ^ 59
def prefixEnd_7254905 : Nat := 4983230072969 + 3 ^ 40 * 7254905 * 2
def baseEnd_7254905 : Nat := 1241751122569014294840935

theorem tailTrace_7254905 : CollatzResearch.WordTrace tailWord_7254905 prefixEnd_7254905 1241751122569014294840935 := by
  unfold tailWord_7254905
  simp only [CollatzResearch.WordTrace]
  refine ⟨264608123781725698974166169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176405415854483799316110779 264608123781725698974166169)
  ·
    refine ⟨198456092836294274230624627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264608123781725698974166169 198456092836294274230624627)
    ·
      refine ⟨297684139254441411345936941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198456092836294274230624627 297684139254441411345936941)
      ·
        refine ⟨111631552220415529254726353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297684139254441411345936941 111631552220415529254726353)
        ·
          refine ⟨83723664165311646941044765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111631552220415529254726353 83723664165311646941044765)
          ·
            refine ⟨31396374061991867602891787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83723664165311646941044765 31396374061991867602891787)
            ·
              refine ⟨47094561092987801404337681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31396374061991867602891787 47094561092987801404337681)
              ·
                refine ⟨35320920819740851053253261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47094561092987801404337681 35320920819740851053253261)
                ·
                  refine ⟨13245345307402819144969973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35320920819740851053253261 13245345307402819144969973)
                  ·
                    refine ⟨1241751122569014294840935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13245345307402819144969973 1241751122569014294840935)
                    ·
                      rfl

theorem cell23_7254905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_7254905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254905 prefixEnd_7254905 := by exact prefixLift 7254905
  have htrace : WordTrace (prefixWord ++ tailWord_7254905) baseStart_7254905 baseEnd_7254905 := by
    simpa [prefixWord, tailWord_7254905, baseEnd_7254905] using wordTrace_append hprefix tailTrace_7254905
  have hstable : (prefixWord ++ tailWord_7254905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254905).length < 2 ^ (prefixWord ++ tailWord_7254905).sum := by decide
  have hdescent : baseEnd_7254905 < baseStart_7254905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254919 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_7254919 : Nat := 118140960795 + 7254919 * 2 ^ 59
def prefixEnd_7254919 : Nat := 4983230072969 + 3 ^ 40 * 7254919 * 2
def baseEnd_7254919 : Nat := 3725260556436205829747741

theorem tailTrace_7254919 : CollatzResearch.WordTrace tailWord_7254919 prefixEnd_7254919 3725260556436205829747741 := by
  unfold tailWord_7254919
  simp only [CollatzResearch.WordTrace]
  refine ⟨264608634403674979365175811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176405756269116652910117207 264608634403674979365175811)
  ·
    refine ⟨396912951605512469047763717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264608634403674979365175811 396912951605512469047763717)
    ·
      refine ⟨74421178426033587946455697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396912951605512469047763717 74421178426033587946455697)
      ·
        refine ⟨55815883819525190959841773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74421178426033587946455697 55815883819525190959841773)
        ·
          refine ⟨20930956432321946609940665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55815883819525190959841773 20930956432321946609940665)
          ·
            refine ⟨15698217324241459957455499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930956432321946609940665 15698217324241459957455499)
            ·
              refine ⟨23547325986362189936183249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15698217324241459957455499 23547325986362189936183249)
              ·
                refine ⟨17660494489771642452137437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23547325986362189936183249 17660494489771642452137437)
                ·
                  refine ⟨6622685433664365919551539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17660494489771642452137437 6622685433664365919551539)
                  ·
                    refine ⟨9934028150496548879327309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622685433664365919551539 9934028150496548879327309)
                    ·
                      refine ⟨3725260556436205829747741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934028150496548879327309 3725260556436205829747741)
                      ·
                        rfl

theorem cell23_7254919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_7254919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254919 prefixEnd_7254919 := by exact prefixLift 7254919
  have htrace : WordTrace (prefixWord ++ tailWord_7254919) baseStart_7254919 baseEnd_7254919 := by
    simpa [prefixWord, tailWord_7254919, baseEnd_7254919] using wordTrace_append hprefix tailTrace_7254919
  have hstable : (prefixWord ++ tailWord_7254919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254919).length < 2 ^ (prefixWord ++ tailWord_7254919).sum := by decide
  have hdescent : baseEnd_7254919 < baseStart_7254919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254922 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_7254922 : Nat := 118140960795 + 7254922 * 2 ^ 59
def prefixEnd_7254922 : Nat := 4983230072969 + 3 ^ 40 * 7254922 * 2
def baseEnd_7254922 : Nat := 1241754032292723106003409

theorem tailTrace_7254922 : CollatzResearch.WordTrace tailWord_7254922 prefixEnd_7254922 1241754032292723106003409 := by
  unfold tailWord_7254922
  simp only [CollatzResearch.WordTrace]
  refine ⟨66152185955666027719383755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176405829215109407251690013 66152185955666027719383755)
  ·
    refine ⟨99228278933499041579075633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66152185955666027719383755 99228278933499041579075633)
    ·
      refine ⟨74421209200124281184306725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99228278933499041579075633 74421209200124281184306725)
      ·
        refine ⟨13953976725023302722057511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74421209200124281184306725 13953976725023302722057511)
        ·
          refine ⟨20930965087534954083086267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953976725023302722057511 20930965087534954083086267)
          ·
            refine ⟨31396447631302431124629401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930965087534954083086267 31396447631302431124629401)
            ·
              refine ⟨23547335723476823343472051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31396447631302431124629401 23547335723476823343472051)
              ·
                refine ⟨35321003585215235015208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23547335723476823343472051 35321003585215235015208077)
                ·
                  refine ⟨13245376344455713130703029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35321003585215235015208077 13245376344455713130703029)
                  ·
                    refine ⟨1241754032292723106003409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13245376344455713130703029 1241754032292723106003409)
                    ·
                      rfl

theorem cell23_7254922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_7254922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254922 prefixEnd_7254922 := by exact prefixLift 7254922
  have htrace : WordTrace (prefixWord ++ tailWord_7254922) baseStart_7254922 baseEnd_7254922 := by
    simpa [prefixWord, tailWord_7254922, baseEnd_7254922] using wordTrace_append hprefix tailTrace_7254922
  have hstable : (prefixWord ++ tailWord_7254922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254922).length < 2 ^ (prefixWord ++ tailWord_7254922).sum := by decide
  have hdescent : baseEnd_7254922 < baseStart_7254922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254935 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 6]
def baseStart_7254935 : Nat := 118140960795 + 7254935 * 2 ^ 59
def prefixEnd_7254935 : Nat := 4983230072969 + 3 ^ 40 * 7254935 * 2
def baseEnd_7254935 : Nat := 1241756257375559255715889

theorem tailTrace_7254935 : CollatzResearch.WordTrace tailWord_7254935 prefixEnd_7254935 1241756257375559255715889 := by
  unfold tailWord_7254935
  simp only [CollatzResearch.WordTrace]
  refine ⟨264609217971617014097758259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176406145314411342731838839 264609217971617014097758259)
  ·
    refine ⟨396913826957425521146637389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264609217971617014097758259 396913826957425521146637389)
    ·
      refine ⟨148842685109034570429989021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396913826957425521146637389 148842685109034570429989021)
      ·
        refine ⟨55816006915887963911245883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148842685109034570429989021 55816006915887963911245883)
        ·
          refine ⟨83724010373831945866868825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55816006915887963911245883 83724010373831945866868825)
          ·
            refine ⟨62793007780373959400151619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83724010373831945866868825 62793007780373959400151619)
            ·
              refine ⟨94189511670560939100227429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62793007780373959400151619 94189511670560939100227429)
              ·
                refine ⟨17660533438230176081292643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94189511670560939100227429 17660533438230176081292643)
                ·
                  refine ⟨26490800157345264121938965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17660533438230176081292643 26490800157345264121938965)
                  ·
                    refine ⟨1241756257375559255715889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26490800157345264121938965 1241756257375559255715889)
                    ·
                      rfl

theorem cell23_7254935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_7254935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254935 prefixEnd_7254935 := by exact prefixLift 7254935
  have htrace : WordTrace (prefixWord ++ tailWord_7254935) baseStart_7254935 baseEnd_7254935 := by
    simpa [prefixWord, tailWord_7254935, baseEnd_7254935] using wordTrace_append hprefix tailTrace_7254935
  have hstable : (prefixWord ++ tailWord_7254935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254935).length < 2 ^ (prefixWord ++ tailWord_7254935).sum := by decide
  have hdescent : baseEnd_7254935 < baseStart_7254935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7254965 : List Nat := [1, 3, 3, 2, 1, 1, 2, 10]
def baseStart_7254965 : Nat := 118140960795 + 7254965 * 2 ^ 59
def prefixEnd_7254965 : Nat := 4983230072969 + 3 ^ 40 * 7254965 * 2
def baseEnd_7254965 : Nat := 137973488020233801843427

theorem tailTrace_7254965 : CollatzResearch.WordTrace tailWord_7254965 prefixEnd_7254965 137973488020233801843427 := by
  unfold tailWord_7254965
  simp only [CollatzResearch.WordTrace]
  refine ⟨264610312161508329221350349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176406874774338886147566899 264610312161508329221350349)
  ·
    refine ⟨99228867060565623458006381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264610312161508329221350349 99228867060565623458006381)
    ·
      refine ⟨37210825147712108796752393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99228867060565623458006381 37210825147712108796752393)
      ·
        refine ⟨27908118860784081597564295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37210825147712108796752393 27908118860784081597564295)
        ·
          refine ⟨41862178291176122396346443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27908118860784081597564295 41862178291176122396346443)
          ·
            refine ⟨62793267436764183594519665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41862178291176122396346443 62793267436764183594519665)
            ·
              refine ⟨47094950577573137695889749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62793267436764183594519665 47094950577573137695889749)
              ·
                refine ⟨137973488020233801843427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47094950577573137695889749 137973488020233801843427)
                ·
                  rfl

theorem cell23_7254965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 10].length) (baseStart_7254965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7254965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7254965 prefixEnd_7254965 := by exact prefixLift 7254965
  have htrace : WordTrace (prefixWord ++ tailWord_7254965) baseStart_7254965 baseEnd_7254965 := by
    simpa [prefixWord, tailWord_7254965, baseEnd_7254965] using wordTrace_append hprefix tailTrace_7254965
  have hstable : (prefixWord ++ tailWord_7254965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7254965).length < 2 ^ (prefixWord ++ tailWord_7254965).sum := by decide
  have hdescent : baseEnd_7254965 < baseStart_7254965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7254965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255009 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_7255009 : Nat := 118140960795 + 7255009 * 2 ^ 59
def prefixEnd_7255009 : Nat := 4983230072969 + 3 ^ 40 * 7255009 * 2
def baseEnd_7255009 : Nat := 3725306769695110477622327

theorem tailTrace_7255009 : CollatzResearch.WordTrace tailWord_7255009 prefixEnd_7255009 3725306769695110477622327 := by
  unfold tailWord_7255009
  simp only [CollatzResearch.WordTrace]
  refine ⟨264611916973348924735952081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176407944648899283157301387 264611916973348924735952081)
  ·
    refine ⟨198458937730011693551964061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264611916973348924735952081 198458937730011693551964061)
    ·
      refine ⟨74422101648754385081986523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198458937730011693551964061 74422101648754385081986523)
      ·
        refine ⟨111633152473131577622979785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74422101648754385081986523 111633152473131577622979785)
        ·
          refine ⟨83724864354848683217234839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111633152473131577622979785 83724864354848683217234839)
          ·
            refine ⟨125587296532273024825852259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83724864354848683217234839 125587296532273024825852259)
            ·
              refine ⟨188380944798409537238778389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125587296532273024825852259 188380944798409537238778389)
              ·
                refine ⟨8830356787425447058067737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188380944798409537238778389 8830356787425447058067737)
                ·
                  refine ⟨6622767590569085293550803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830356787425447058067737 6622767590569085293550803)
                  ·
                    refine ⟨9934151385853627940326205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622767590569085293550803 9934151385853627940326205)
                    ·
                      refine ⟨3725306769695110477622327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934151385853627940326205 3725306769695110477622327)
                      ·
                        rfl

theorem cell23_7255009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_7255009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255009 prefixEnd_7255009 := by exact prefixLift 7255009
  have htrace : WordTrace (prefixWord ++ tailWord_7255009) baseStart_7255009 baseEnd_7255009 := by
    simpa [prefixWord, tailWord_7255009, baseEnd_7255009] using wordTrace_append hprefix tailTrace_7255009
  have hstable : (prefixWord ++ tailWord_7255009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255009).length < 2 ^ (prefixWord ++ tailWord_7255009).sum := by decide
  have hdescent : baseEnd_7255009 < baseStart_7255009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255010 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7255010 : Nat := 118140960795 + 7255010 * 2 ^ 59
def prefixEnd_7255010 : Nat := 4983230072969 + 3 ^ 40 * 7255010 * 2
def baseEnd_7255010 : Nat := 3725307283175764973709823

theorem tailTrace_7255010 : CollatzResearch.WordTrace tailWord_7255010 prefixEnd_7255010 3725307283175764973709823 := by
  unfold tailWord_7255010
  simp only [CollatzResearch.WordTrace]
  refine ⟨66152988361586325476684621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176407968964230201271158989 66152988361586325476684621)
  ·
    refine ⟨24807370635594872053756733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66152988361586325476684621 24807370635594872053756733)
    ·
      refine ⟨9302763988348077020158775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24807370635594872053756733 9302763988348077020158775)
      ·
        refine ⟨13954145982522115530238163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302763988348077020158775 13954145982522115530238163)
        ·
          refine ⟨20931218973783173295357245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954145982522115530238163 20931218973783173295357245)
          ·
            refine ⟨7849207115168689985758967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20931218973783173295357245 7849207115168689985758967)
            ·
              refine ⟨11773810672753034978638451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849207115168689985758967 11773810672753034978638451)
              ·
                refine ⟨17660716009129552467957677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11773810672753034978638451 17660716009129552467957677)
                ·
                  refine ⟨6622768503423582175484129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17660716009129552467957677 6622768503423582175484129)
                  ·
                    refine ⟨4967076377567686631613097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622768503423582175484129 4967076377567686631613097)
                    ·
                      refine ⟨3725307283175764973709823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967076377567686631613097 3725307283175764973709823)
                      ·
                        rfl

theorem cell23_7255010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7255010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255010 prefixEnd_7255010 := by exact prefixLift 7255010
  have htrace : WordTrace (prefixWord ++ tailWord_7255010) baseStart_7255010 baseEnd_7255010 := by
    simpa [prefixWord, tailWord_7255010, baseEnd_7255010] using wordTrace_append hprefix tailTrace_7255010
  have hstable : (prefixWord ++ tailWord_7255010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255010).length < 2 ^ (prefixWord ++ tailWord_7255010).sum := by decide
  have hdescent : baseEnd_7255010 < baseStart_7255010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255036 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_7255036 : Nat := 118140960795 + 7255036 * 2 ^ 59
def prefixEnd_7255036 : Nat := 4983230072969 + 3 ^ 40 * 7255036 * 2
def baseEnd_7255036 : Nat := 3725320633672781871984703

theorem tailTrace_7255036 : CollatzResearch.WordTrace tailWord_7255036 prefixEnd_7255036 3725320633672781871984703 := by
  unfold tailWord_7255036
  simp only [CollatzResearch.WordTrace]
  refine ⟨132306450872125554173592481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176408601162834072231456641 132306450872125554173592481)
  ·
    refine ⟨99229838154094165630194361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132306450872125554173592481 99229838154094165630194361)
    ·
      refine ⟨74422378615570624222645771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99229838154094165630194361 74422378615570624222645771)
      ·
        refine ⟨111633567923355936333968657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74422378615570624222645771 111633567923355936333968657)
        ·
          refine ⟨83725175942516952250476493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111633567923355936333968657 83725175942516952250476493)
          ·
            refine ⟨31396940978443857093928685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83725175942516952250476493 31396940978443857093928685)
            ·
              refine ⟨11773852866916446410223257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31396940978443857093928685 11773852866916446410223257)
              ·
                refine ⟨8830389650187334807667443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11773852866916446410223257 8830389650187334807667443)
                ·
                  refine ⟨13245584475281002211501165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830389650187334807667443 13245584475281002211501165)
                  ·
                    refine ⟨4967094178230375829312937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13245584475281002211501165 4967094178230375829312937)
                    ·
                      refine ⟨3725320633672781871984703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967094178230375829312937 3725320633672781871984703)
                      ·
                        rfl

theorem cell23_7255036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_7255036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255036 prefixEnd_7255036 := by exact prefixLift 7255036
  have htrace : WordTrace (prefixWord ++ tailWord_7255036) baseStart_7255036 baseEnd_7255036 := by
    simpa [prefixWord, tailWord_7255036, baseEnd_7255036] using wordTrace_append hprefix tailTrace_7255036
  have hstable : (prefixWord ++ tailWord_7255036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255036).length < 2 ^ (prefixWord ++ tailWord_7255036).sum := by decide
  have hdescent : baseEnd_7255036 < baseStart_7255036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255049 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 6, 2, 2]
def baseStart_7255049 : Nat := 118140960795 + 7255049 * 2 ^ 59
def prefixEnd_7255049 : Nat := 4983230072969 + 3 ^ 40 * 7255049 * 2
def baseEnd_7255049 : Nat := 3725327308921290321122143

theorem tailTrace_7255049 : CollatzResearch.WordTrace tailWord_7255049 prefixEnd_7255049 3725327308921290321122143 := by
  unfold tailWord_7255049
  simp only [CollatzResearch.WordTrace]
  refine ⟨264613375893204011567408201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176408917262136007711605467 264613375893204011567408201)
  ·
    refine ⟨198460031919903008675556151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264613375893204011567408201 198460031919903008675556151)
    ·
      refine ⟨297690047879854513013334227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198460031919903008675556151 297690047879854513013334227)
      ·
        refine ⟨446535071819781769520001341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297690047879854513013334227 446535071819781769520001341)
        ·
          refine ⟨167450651932418163570000503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446535071819781769520001341 167450651932418163570000503)
          ·
            refine ⟨251175977898627245355000755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167450651932418163570000503 251175977898627245355000755)
            ·
              refine ⟨376763966847940868032501133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251175977898627245355000755 376763966847940868032501133)
              ·
                refine ⟨141286487567977825512187925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376763966847940868032501133 141286487567977825512187925)
                ·
                  refine ⟨6622804104748960570883809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141286487567977825512187925 6622804104748960570883809)
                  ·
                    refine ⟨4967103078561720428162857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622804104748960570883809 4967103078561720428162857)
                    ·
                      refine ⟨3725327308921290321122143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967103078561720428162857 3725327308921290321122143)
                      ·
                        rfl

theorem cell23_7255049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2, 2].length) (baseStart_7255049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255049 prefixEnd_7255049 := by exact prefixLift 7255049
  have htrace : WordTrace (prefixWord ++ tailWord_7255049) baseStart_7255049 baseEnd_7255049 := by
    simpa [prefixWord, tailWord_7255049, baseEnd_7255049] using wordTrace_append hprefix tailTrace_7255049
  have hstable : (prefixWord ++ tailWord_7255049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255049).length < 2 ^ (prefixWord ++ tailWord_7255049).sum := by decide
  have hdescent : baseEnd_7255049 < baseStart_7255049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255052 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7255052 : Nat := 118140960795 + 7255052 * 2 ^ 59
def prefixEnd_7255052 : Nat := 4983230072969 + 3 ^ 40 * 7255052 * 2
def baseEnd_7255052 : Nat := 3725328849363253809384629

theorem tailTrace_7255052 : CollatzResearch.WordTrace tailWord_7255052 prefixEnd_7255052 3725328849363253809384629 := by
  unfold tailWord_7255052
  simp only [CollatzResearch.WordTrace]
  refine ⟨132306742656096571539883705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176408990208128762053178273 132306742656096571539883705)
  ·
    refine ⟨99230056992072428654912779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132306742656096571539883705 99230056992072428654912779)
    ·
      refine ⟨148845085488108642982369169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99230056992072428654912779 148845085488108642982369169)
      ·
        refine ⟨111633814116081482236776877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148845085488108642982369169 111633814116081482236776877)
        ·
          refine ⟨41862680293530555838791329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111633814116081482236776877 41862680293530555838791329)
          ·
            refine ⟨31397010220147916879093497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41862680293530555838791329 31397010220147916879093497)
            ·
              refine ⟨23547757665110937659320123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31397010220147916879093497 23547757665110937659320123)
              ·
                refine ⟨35321636497666406488980185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23547757665110937659320123 35321636497666406488980185)
                ·
                  refine ⟨26491227373249804866735139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35321636497666406488980185 26491227373249804866735139)
                  ·
                    refine ⟨39736841059874707300102709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26491227373249804866735139 39736841059874707300102709)
                    ·
                      refine ⟨3725328849363253809384629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39736841059874707300102709 3725328849363253809384629)
                      ·
                        rfl

theorem cell23_7255052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7255052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255052 prefixEnd_7255052 := by exact prefixLift 7255052
  have htrace : WordTrace (prefixWord ++ tailWord_7255052) baseStart_7255052 baseEnd_7255052 := by
    simpa [prefixWord, tailWord_7255052, baseEnd_7255052] using wordTrace_append hprefix tailTrace_7255052
  have hstable : (prefixWord ++ tailWord_7255052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255052).length < 2 ^ (prefixWord ++ tailWord_7255052).sum := by decide
  have hdescent : baseEnd_7255052 < baseStart_7255052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255065 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7255065 : Nat := 118140960795 + 7255065 * 2 ^ 59
def prefixEnd_7255065 : Nat := 4983230072969 + 3 ^ 40 * 7255065 * 2
def baseEnd_7255065 : Nat := 3725335524611762258522069

theorem tailTrace_7255065 : CollatzResearch.WordTrace tailWord_7255065 prefixEnd_7255065 3725335524611762258522069 := by
  unfold tailWord_7255065
  simp only [CollatzResearch.WordTrace]
  refine ⟨264613959461146046299990649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176409306307430697533327099 264613959461146046299990649)
  ·
    refine ⟨198460469595859534724992987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264613959461146046299990649 198460469595859534724992987)
    ·
      refine ⟨297690704393789302087489481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198460469595859534724992987 297690704393789302087489481)
      ·
        refine ⟨223268028295341976565617111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297690704393789302087489481 223268028295341976565617111)
        ·
          refine ⟨334902042443012964848425667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223268028295341976565617111 334902042443012964848425667)
          ·
            refine ⟨502353063664519447272638501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334902042443012964848425667 502353063664519447272638501)
            ·
              refine ⟨94191199437097396363619719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502353063664519447272638501 94191199437097396363619719)
              ·
                refine ⟨141286799155646094545429579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94191199437097396363619719 141286799155646094545429579)
                ·
                  refine ⟨211930198733469141818144369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141286799155646094545429579 211930198733469141818144369)
                  ·
                    refine ⟨158947649050101856363608277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211930198733469141818144369 158947649050101856363608277)
                    ·
                      refine ⟨3725335524611762258522069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158947649050101856363608277 3725335524611762258522069)
                      ·
                        rfl

theorem cell23_7255065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7255065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255065 prefixEnd_7255065 := by exact prefixLift 7255065
  have htrace : WordTrace (prefixWord ++ tailWord_7255065) baseStart_7255065 baseEnd_7255065 := by
    simpa [prefixWord, tailWord_7255065, baseEnd_7255065] using wordTrace_append hprefix tailTrace_7255065
  have hstable : (prefixWord ++ tailWord_7255065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255065).length < 2 ^ (prefixWord ++ tailWord_7255065).sum := by decide
  have hdescent : baseEnd_7255065 < baseStart_7255065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255079 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7255079 : Nat := 118140960795 + 7255079 * 2 ^ 59
def prefixEnd_7255079 : Nat := 4983230072969 + 3 ^ 40 * 7255079 * 2
def baseEnd_7255079 : Nat := 3725342713340925203747005

theorem tailTrace_7255079 : CollatzResearch.WordTrace tailWord_7255079 prefixEnd_7255079 3725342713340925203747005 := by
  unfold tailWord_7255079
  simp only [CollatzResearch.WordTrace]
  refine ⟨264614470083095326691000291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176409646722063551127333527 264614470083095326691000291)
  ·
    refine ⟨396921705124642990036500437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264614470083095326691000291 396921705124642990036500437)
    ·
      refine ⟨9302852463858820078980479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 396921705124642990036500437 9302852463858820078980479)
      ·
        refine ⟨13954278695788230118470719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302852463858820078980479 13954278695788230118470719)
        ·
          refine ⟨20931418043682345177706079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954278695788230118470719 20931418043682345177706079)
          ·
            refine ⟨31397127065523517766559119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20931418043682345177706079 31397127065523517766559119)
            ·
              refine ⟨47095690598285276649838679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31397127065523517766559119 47095690598285276649838679)
              ·
                refine ⟨70643535897427914974758019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47095690598285276649838679 70643535897427914974758019)
                ·
                  refine ⟨105965303846141872462137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70643535897427914974758019 105965303846141872462137029)
                  ·
                    refine ⟨19868494471151601086650693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105965303846141872462137029 19868494471151601086650693)
                    ·
                      refine ⟨3725342713340925203747005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19868494471151601086650693 3725342713340925203747005)
                      ·
                        rfl

theorem cell23_7255079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7255079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255079 prefixEnd_7255079 := by exact prefixLift 7255079
  have htrace : WordTrace (prefixWord ++ tailWord_7255079) baseStart_7255079 baseEnd_7255079 := by
    simpa [prefixWord, tailWord_7255079, baseEnd_7255079] using wordTrace_append hprefix tailTrace_7255079
  have hstable : (prefixWord ++ tailWord_7255079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255079).length < 2 ^ (prefixWord ++ tailWord_7255079).sum := by decide
  have hdescent : baseEnd_7255079 < baseStart_7255079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255134 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7255134 : Nat := 118140960795 + 7255134 * 2 ^ 59
def prefixEnd_7255134 : Nat := 4983230072969 + 3 ^ 40 * 7255134 * 2
def baseEnd_7255134 : Nat := 3725370954776922488559253

theorem tailTrace_7255134 : CollatzResearch.WordTrace tailWord_7255134 prefixEnd_7255134 3725370954776922488559253 := by
  unfold tailWord_7255134
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077059512237008885531557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176410984065264047389501637 33077059512237008885531557)
  ·
    refine ⟨6201948658544439166037167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33077059512237008885531557 6201948658544439166037167)
    ·
      refine ⟨9302922987816658749055751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201948658544439166037167 9302922987816658749055751)
      ·
        refine ⟨13954384481724988123583627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9302922987816658749055751 13954384481724988123583627)
        ·
          refine ⟨20931576722587482185375441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954384481724988123583627 20931576722587482185375441)
          ·
            refine ⟨15698682541940611639031581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20931576722587482185375441 15698682541940611639031581)
            ·
              refine ⟨5887005953227729364636843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15698682541940611639031581 5887005953227729364636843)
              ·
                refine ⟨8830508929841594046955265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887005953227729364636843 8830508929841594046955265)
                ·
                  refine ⟨6622881697381195535216449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830508929841594046955265 6622881697381195535216449)
                  ·
                    refine ⟨4967161273035896651412337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622881697381195535216449 4967161273035896651412337)
                    ·
                      refine ⟨3725370954776922488559253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967161273035896651412337 3725370954776922488559253)
                      ·
                        rfl

theorem cell23_7255134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7255134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255134 prefixEnd_7255134 := by exact prefixLift 7255134
  have htrace : WordTrace (prefixWord ++ tailWord_7255134) baseStart_7255134 baseEnd_7255134 := by
    simpa [prefixWord, tailWord_7255134, baseEnd_7255134] using wordTrace_append hprefix tailTrace_7255134
  have hstable : (prefixWord ++ tailWord_7255134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255134).length < 2 ^ (prefixWord ++ tailWord_7255134).sum := by decide
  have hdescent : baseEnd_7255134 < baseStart_7255134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255152 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_7255152 : Nat := 118140960795 + 7255152 * 2 ^ 59
def prefixEnd_7255152 : Nat := 4983230072969 + 3 ^ 40 * 7255152 * 2
def baseEnd_7255152 : Nat := 3725380197428703418134169

theorem tailTrace_7255152 : CollatzResearch.WordTrace tailWord_7255152 prefixEnd_7255152 3725380197428703418134169 := by
  unfold tailWord_7255152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132308566305915430079203855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176411421741220573438938473 132308566305915430079203855)
  ·
    refine ⟨198462849458873145118805783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132308566305915430079203855 198462849458873145118805783)
    ·
      refine ⟨297694274188309717678208675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198462849458873145118805783 297694274188309717678208675)
      ·
        refine ⟨446541411282464576517313013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297694274188309717678208675 446541411282464576517313013)
        ·
          refine ⟨41863257307731054048498095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446541411282464576517313013 41863257307731054048498095)
          ·
            refine ⟨62794885961596581072747143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41863257307731054048498095 62794885961596581072747143)
            ·
              refine ⟨94192328942394871609120715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62794885961596581072747143 94192328942394871609120715)
              ·
                refine ⟨141288493413592307413681073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94192328942394871609120715 141288493413592307413681073)
                ·
                  refine ⟨105966370060194230560260805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141288493413592307413681073 105966370060194230560260805)
                  ·
                    refine ⟨19868694386286418230048901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105966370060194230560260805 19868694386286418230048901)
                    ·
                      refine ⟨3725380197428703418134169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19868694386286418230048901 3725380197428703418134169)
                      ·
                        rfl

theorem cell23_7255152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_7255152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255152 prefixEnd_7255152 := by exact prefixLift 7255152
  have htrace : WordTrace (prefixWord ++ tailWord_7255152) baseStart_7255152 baseEnd_7255152 := by
    simpa [prefixWord, tailWord_7255152, baseEnd_7255152] using wordTrace_append hprefix tailTrace_7255152
  have hstable : (prefixWord ++ tailWord_7255152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255152).length < 2 ^ (prefixWord ++ tailWord_7255152).sum := by decide
  have hdescent : baseEnd_7255152 < baseStart_7255152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255159 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_7255159 : Nat := 118140960795 + 7255159 * 2 ^ 59
def prefixEnd_7255159 : Nat := 4983230072969 + 3 ^ 40 * 7255159 * 2
def baseEnd_7255159 : Nat := 3725383791793284890746637

theorem tailTrace_7255159 : CollatzResearch.WordTrace tailWord_7255159 prefixEnd_7255159 3725383791793284890746637 := by
  unfold tailWord_7255159
  simp only [CollatzResearch.WordTrace]
  refine ⟨264617387922805500353912531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176411591948537000235941687 264617387922805500353912531)
  ·
    refine ⟨396926081884208250530868797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264617387922805500353912531 396926081884208250530868797)
    ·
      refine ⟨148847280706578093949075799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396926081884208250530868797 148847280706578093949075799)
      ·
        refine ⟨223270921059867140923613699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148847280706578093949075799 223270921059867140923613699)
        ·
          refine ⟨334906381589800711385420549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223270921059867140923613699 334906381589800711385420549)
          ·
            refine ⟨62794946548087633384766353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334906381589800711385420549 62794946548087633384766353)
            ·
              refine ⟨47096209911065725038574765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62794946548087633384766353 47096209911065725038574765)
              ·
                refine ⟨17661078716649646889465537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47096209911065725038574765 17661078716649646889465537)
                ·
                  refine ⟨13245809037487235167099153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17661078716649646889465537 13245809037487235167099153)
                  ·
                    refine ⟨9934356778115426375324365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13245809037487235167099153 9934356778115426375324365)
                    ·
                      refine ⟨3725383791793284890746637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934356778115426375324365 3725383791793284890746637)
                      ·
                        rfl

theorem cell23_7255159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_7255159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255159 prefixEnd_7255159 := by exact prefixLift 7255159
  have htrace : WordTrace (prefixWord ++ tailWord_7255159) baseStart_7255159 baseEnd_7255159 := by
    simpa [prefixWord, tailWord_7255159, baseEnd_7255159] using wordTrace_append hprefix tailTrace_7255159
  have hstable : (prefixWord ++ tailWord_7255159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255159).length < 2 ^ (prefixWord ++ tailWord_7255159).sum := by decide
  have hdescent : baseEnd_7255159 < baseStart_7255159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255196 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 6]
def baseStart_7255196 : Nat := 118140960795 + 7255196 * 2 ^ 59
def prefixEnd_7255196 : Nat := 4983230072969 + 3 ^ 40 * 7255196 * 2
def baseEnd_7255196 : Nat := 413933643397500138442663

theorem tailTrace_7255196 : CollatzResearch.WordTrace tailWord_7255196 prefixEnd_7255196 413933643397500138442663 := by
  unfold tailWord_7255196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132309368711835727836504721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176412491615780970448672961 132309368711835727836504721)
  ·
    refine ⟨99232026533876795877378541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132309368711835727836504721 99232026533876795877378541)
    ·
      refine ⟨37212009950203798454016953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99232026533876795877378541 37212009950203798454016953)
      ·
        refine ⟨27909007462652848840512715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37212009950203798454016953 27909007462652848840512715)
        ·
          refine ⟨41863511193979273260769073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27909007462652848840512715 41863511193979273260769073)
          ·
            refine ⟨31397633395484454945576805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41863511193979273260769073 31397633395484454945576805)
            ·
              refine ⟨5887056261653335302295651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31397633395484454945576805 5887056261653335302295651)
              ·
                refine ⟨8830584392480002953443477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887056261653335302295651 8830584392480002953443477)
                ·
                  refine ⟨413933643397500138442663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8830584392480002953443477 413933643397500138442663)
                  ·
                    rfl

theorem cell23_7255196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_7255196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255196 prefixEnd_7255196 := by exact prefixLift 7255196
  have htrace : WordTrace (prefixWord ++ tailWord_7255196) baseStart_7255196 baseEnd_7255196 := by
    simpa [prefixWord, tailWord_7255196, baseEnd_7255196] using wordTrace_append hprefix tailTrace_7255196
  have hstable : (prefixWord ++ tailWord_7255196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255196).length < 2 ^ (prefixWord ++ tailWord_7255196).sum := by decide
  have hdescent : baseEnd_7255196 < baseStart_7255196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255223 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_7255223 : Nat := 118140960795 + 7255223 * 2 ^ 59
def prefixEnd_7255223 : Nat := 4983230072969 + 3 ^ 40 * 7255223 * 2
def baseEnd_7255223 : Nat := 3725416654555172640346343

theorem tailTrace_7255223 : CollatzResearch.WordTrace tailWord_7255223 prefixEnd_7255223 3725416654555172640346343 := by
  unfold tailWord_7255223
  simp only [CollatzResearch.WordTrace]
  refine ⟨264619722194573639284242323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176413148129715759522828215 264619722194573639284242323)
  ·
    refine ⟨396929583291860458926363485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264619722194573639284242323 396929583291860458926363485)
    ·
      refine ⟨148848593734447672097386307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396929583291860458926363485 148848593734447672097386307)
      ·
        refine ⟨223272890601671508146079461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148848593734447672097386307 223272890601671508146079461)
        ·
          refine ⟨41863666987813407777389899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223272890601671508146079461 41863666987813407777389899)
          ·
            refine ⟨62795500481720111666084849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41863666987813407777389899 62795500481720111666084849)
            ·
              refine ⟨47096625361290083749563637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62795500481720111666084849 47096625361290083749563637)
              ·
                refine ⟨4415308627620945351521591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47096625361290083749563637 4415308627620945351521591)
                ·
                  refine ⟨6622962941431418027282387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415308627620945351521591 6622962941431418027282387)
                  ·
                    refine ⟨9934444412147127040923581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622962941431418027282387 9934444412147127040923581)
                    ·
                      refine ⟨3725416654555172640346343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934444412147127040923581 3725416654555172640346343)
                      ·
                        rfl

theorem cell23_7255223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_7255223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255223 prefixEnd_7255223 := by exact prefixLift 7255223
  have htrace : WordTrace (prefixWord ++ tailWord_7255223) baseStart_7255223 baseEnd_7255223 := by
    simpa [prefixWord, tailWord_7255223, baseEnd_7255223] using wordTrace_append hprefix tailTrace_7255223
  have hstable : (prefixWord ++ tailWord_7255223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255223).length < 2 ^ (prefixWord ++ tailWord_7255223).sum := by decide
  have hdescent : baseEnd_7255223 < baseStart_7255223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255239 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 4, 4]
def baseStart_7255239 : Nat := 118140960795 + 7255239 * 2 ^ 59
def prefixEnd_7255239 : Nat := 4983230072969 + 3 ^ 40 * 7255239 * 2
def baseEnd_7255239 : Nat := 1241808290081881525915423

theorem tailTrace_7255239 : CollatzResearch.WordTrace tailWord_7255239 prefixEnd_7255239 1241808290081881525915423 := by
  unfold tailWord_7255239
  simp only [CollatzResearch.WordTrace]
  refine ⟨264620305762515674016824771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176413537175010449344549847 264620305762515674016824771)
  ·
    refine ⟨396930458643773511025237157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264620305762515674016824771 396930458643773511025237157)
    ·
      refine ⟨74424460995707533317231967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396930458643773511025237157 74424460995707533317231967)
      ·
        refine ⟨111636691493561299975847951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74424460995707533317231967 111636691493561299975847951)
        ·
          refine ⟨167455037240341949963771927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111636691493561299975847951 167455037240341949963771927)
          ·
            refine ⟨251182555860512924945657891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167455037240341949963771927 251182555860512924945657891)
            ·
              refine ⟨376773833790769387418486837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251182555860512924945657891 376773833790769387418486837)
              ·
                refine ⟨35322546917884630070483141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376773833790769387418486837 35322546917884630070483141)
                ·
                  refine ⟨6622977547103368138215589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35322546917884630070483141 6622977547103368138215589)
                  ·
                    refine ⟨1241808290081881525915423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6622977547103368138215589 1241808290081881525915423)
                    ·
                      rfl

theorem cell23_7255239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_7255239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255239 prefixEnd_7255239 := by exact prefixLift 7255239
  have htrace : WordTrace (prefixWord ++ tailWord_7255239) baseStart_7255239 baseEnd_7255239 := by
    simpa [prefixWord, tailWord_7255239, baseEnd_7255239] using wordTrace_append hprefix tailTrace_7255239
  have hstable : (prefixWord ++ tailWord_7255239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255239).length < 2 ^ (prefixWord ++ tailWord_7255239).sum := by decide
  have hdescent : baseEnd_7255239 < baseStart_7255239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255240 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_7255240 : Nat := 118140960795 + 7255240 * 2 ^ 59
def prefixEnd_7255240 : Nat := 4983230072969 + 3 ^ 40 * 7255240 * 2
def baseEnd_7255240 : Nat := 3725425383726299073833765

theorem tailTrace_7255240 : CollatzResearch.WordTrace tailWord_7255240 prefixEnd_7255240 3725425383726299073833765 := by
  unfold tailWord_7255240
  simp only [CollatzResearch.WordTrace]
  refine ⟨132310171117756025593805587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176413561490341367458407449 132310171117756025593805587)
  ·
    refine ⟨198465256676634038390708381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132310171117756025593805587 198465256676634038390708381)
    ·
      refine ⟨74424471253737764396515643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198465256676634038390708381 74424471253737764396515643)
      ·
        refine ⟨111636706880606646594773465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74424471253737764396515643 111636706880606646594773465)
        ·
          refine ⟨83727530160454984946080099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111636706880606646594773465 83727530160454984946080099)
          ·
            refine ⟨125591295240682477419120149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83727530160454984946080099 125591295240682477419120149)
            ·
              refine ⟨5887091964406991129021257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125591295240682477419120149 5887091964406991129021257)
              ·
                refine ⟨4415318973305243346765943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887091964406991129021257 4415318973305243346765943)
                ·
                  refine ⟨6622978459957865020148915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415318973305243346765943 6622978459957865020148915)
                  ·
                    refine ⟨9934467689936797530223373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622978459957865020148915 9934467689936797530223373)
                    ·
                      refine ⟨3725425383726299073833765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934467689936797530223373 3725425383726299073833765)
                      ·
                        rfl

theorem cell23_7255240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_7255240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255240 prefixEnd_7255240 := by exact prefixLift 7255240
  have htrace : WordTrace (prefixWord ++ tailWord_7255240) baseStart_7255240 baseEnd_7255240 := by
    simpa [prefixWord, tailWord_7255240, baseEnd_7255240] using wordTrace_append hprefix tailTrace_7255240
  have hstable : (prefixWord ++ tailWord_7255240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255240).length < 2 ^ (prefixWord ++ tailWord_7255240).sum := by decide
  have hdescent : baseEnd_7255240 < baseStart_7255240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255256 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_7255256 : Nat := 118140960795 + 7255256 * 2 ^ 59
def prefixEnd_7255256 : Nat := 4983230072969 + 3 ^ 40 * 7255256 * 2
def baseEnd_7255256 : Nat := 1241811199805590337077897

theorem tailTrace_7255256 : CollatzResearch.WordTrace tailWord_7255256 prefixEnd_7255256 1241811199805590337077897 := by
  unfold tailWord_7255256
  simp only [CollatzResearch.WordTrace]
  refine ⟨132310462901727042960096811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176413950535636057280129081 132310462901727042960096811)
  ·
    refine ⟨198465694352590564440145217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132310462901727042960096811 198465694352590564440145217)
    ·
      refine ⟨148849270764442923330108913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198465694352590564440145217 148849270764442923330108913)
      ·
        refine ⟨111636953073332192497581685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148849270764442923330108913 111636953073332192497581685)
        ·
          refine ⟨10465964350624893046648283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111636953073332192497581685 10465964350624893046648283)
          ·
            refine ⟨15698946525937339569972425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465964350624893046648283 15698946525937339569972425)
            ·
              refine ⟨11774209894453004677479319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15698946525937339569972425 11774209894453004677479319)
              ·
                refine ⟨17661314841679507016218979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774209894453004677479319 17661314841679507016218979)
                ·
                  refine ⟨26491972262519260524328469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17661314841679507016218979 26491972262519260524328469)
                  ·
                    refine ⟨1241811199805590337077897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26491972262519260524328469 1241811199805590337077897)
                    ·
                      rfl

theorem cell23_7255256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_7255256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255256 prefixEnd_7255256 := by exact prefixLift 7255256
  have htrace : WordTrace (prefixWord ++ tailWord_7255256) baseStart_7255256 baseEnd_7255256 := by
    simpa [prefixWord, tailWord_7255256, baseEnd_7255256] using wordTrace_append hprefix tailTrace_7255256
  have hstable : (prefixWord ++ tailWord_7255256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255256).length < 2 ^ (prefixWord ++ tailWord_7255256).sum := by decide
  have hdescent : baseEnd_7255256 < baseStart_7255256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255283 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 1, 2, 3]
def baseStart_7255283 : Nat := 118140960795 + 7255283 * 2 ^ 59
def prefixEnd_7255283 : Nat := 4983230072969 + 3 ^ 40 * 7255283 * 2
def baseEnd_7255283 : Nat := 3725447463394442405596067

theorem tailTrace_7255283 : CollatzResearch.WordTrace tailWord_7255283 prefixEnd_7255283 3725447463394442405596067 := by
  unfold tailWord_7255283
  simp only [CollatzResearch.WordTrace]
  refine ⟨264621910574356269531426503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176414607049570846354284335 264621910574356269531426503)
  ·
    refine ⟨396932865861534404297139755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264621910574356269531426503 396932865861534404297139755)
    ·
      refine ⟨595399298792301606445709633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396932865861534404297139755 595399298792301606445709633)
      ·
        refine ⟨446549474094226204834282225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595399298792301606445709633 446549474094226204834282225)
        ·
          refine ⟨334912105570669653625711669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446549474094226204834282225 334912105570669653625711669)
          ·
            refine ⟨31398009897250280027410469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334912105570669653625711669 31398009897250280027410469)
            ·
              refine ⟨5887126855734427505139463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31398009897250280027410469 5887126855734427505139463)
              ·
                refine ⟨8830690283601641257709195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887126855734427505139463 8830690283601641257709195)
                ·
                  refine ⟨13246035425402461886563793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830690283601641257709195 13246035425402461886563793)
                  ·
                    refine ⟨9934526569051846414922845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13246035425402461886563793 9934526569051846414922845)
                    ·
                      refine ⟨3725447463394442405596067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934526569051846414922845 3725447463394442405596067)
                      ·
                        rfl

theorem cell23_7255283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 2, 3].length) (baseStart_7255283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255283 prefixEnd_7255283 := by exact prefixLift 7255283
  have htrace : WordTrace (prefixWord ++ tailWord_7255283) baseStart_7255283 baseEnd_7255283 := by
    simpa [prefixWord, tailWord_7255283, baseEnd_7255283] using wordTrace_append hprefix tailTrace_7255283
  have hstable : (prefixWord ++ tailWord_7255283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255283).length < 2 ^ (prefixWord ++ tailWord_7255283).sum := by decide
  have hdescent : baseEnd_7255283 < baseStart_7255283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255339 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3]
def baseStart_7255339 : Nat := 118140960795 + 7255339 * 2 ^ 59
def prefixEnd_7255339 : Nat := 4983230072969 + 3 ^ 40 * 7255339 * 2
def baseEnd_7255339 : Nat := 3725476218311094186495809

theorem tailTrace_7255339 : CollatzResearch.WordTrace tailWord_7255339 prefixEnd_7255339 3725476218311094186495809 := by
  unfold tailWord_7255339
  simp only [CollatzResearch.WordTrace]
  refine ⟨264623953062153391095465071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176415968708102260730310047 264623953062153391095465071)
  ·
    refine ⟨396935929593230086643197607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264623953062153391095465071 396935929593230086643197607)
    ·
      refine ⟨595403894389845129964796411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396935929593230086643197607 595403894389845129964796411)
      ·
        refine ⟨893105841584767694947194617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595403894389845129964796411 893105841584767694947194617)
        ·
          refine ⟨669829381188575771210395963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893105841584767694947194617 669829381188575771210395963)
          ·
            refine ⟨1004744071782863656815593945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669829381188575771210395963 1004744071782863656815593945)
            ·
              refine ⟨753558053837147742611695459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004744071782863656815593945 753558053837147742611695459)
              ·
                refine ⟨1130337080755721613917543189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753558053837147742611695459 1130337080755721613917543189)
                ·
                  refine ⟨52984550660424450652384837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1130337080755721613917543189 52984550660424450652384837)
                  ·
                    refine ⟨9934603248829584497322157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52984550660424450652384837 9934603248829584497322157)
                    ·
                      refine ⟨3725476218311094186495809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934603248829584497322157 3725476218311094186495809)
                      ·
                        rfl

theorem cell23_7255339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 3].length) (baseStart_7255339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255339 prefixEnd_7255339 := by exact prefixLift 7255339
  have htrace : WordTrace (prefixWord ++ tailWord_7255339) baseStart_7255339 baseEnd_7255339 := by
    simpa [prefixWord, tailWord_7255339, baseEnd_7255339] using wordTrace_append hprefix tailTrace_7255339
  have hstable : (prefixWord ++ tailWord_7255339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255339).length < 2 ^ (prefixWord ++ tailWord_7255339).sum := by decide
  have hdescent : baseEnd_7255339 < baseStart_7255339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255364 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7255364 : Nat := 118140960795 + 7255364 * 2 ^ 59
def prefixEnd_7255364 : Nat := 4983230072969 + 3 ^ 40 * 7255364 * 2
def baseEnd_7255364 : Nat := 3725489055327456588683195

theorem tailTrace_7255364 : CollatzResearch.WordTrace tailWord_7255364 prefixEnd_7255364 3725489055327456588683195 := by
  unfold tailWord_7255364
  simp only [CollatzResearch.WordTrace]
  refine ⟨132312432443531410182562573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176416576591375213576750097 132312432443531410182562573)
  ·
    refine ⟨49617162166324278818460965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132312432443531410182562573 49617162166324278818460965)
    ·
      refine ⟨9303217906185802278461431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49617162166324278818460965 9303217906185802278461431)
      ·
        refine ⟨13954826859278703417692147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9303217906185802278461431 13954826859278703417692147)
        ·
          refine ⟨20932240288918055126538221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954826859278703417692147 20932240288918055126538221)
          ·
            refine ⟨7849590108344270672451833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20932240288918055126538221 7849590108344270672451833)
            ·
              refine ⟨5887192581258203004338875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7849590108344270672451833 5887192581258203004338875)
              ·
                refine ⟨8830788871887304506508313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887192581258203004338875 8830788871887304506508313)
                ·
                  refine ⟨6623091653915478379881235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830788871887304506508313 6623091653915478379881235)
                  ·
                    refine ⟨9934637480873217569821853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623091653915478379881235 9934637480873217569821853)
                    ·
                      refine ⟨3725489055327456588683195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934637480873217569821853 3725489055327456588683195)
                      ·
                        rfl

theorem cell23_7255364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7255364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255364 prefixEnd_7255364 := by exact prefixLift 7255364
  have htrace : WordTrace (prefixWord ++ tailWord_7255364) baseStart_7255364 baseEnd_7255364 := by
    simpa [prefixWord, tailWord_7255364, baseEnd_7255364] using wordTrace_append hprefix tailTrace_7255364
  have hstable : (prefixWord ++ tailWord_7255364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255364).length < 2 ^ (prefixWord ++ tailWord_7255364).sum := by decide
  have hdescent : baseEnd_7255364 < baseStart_7255364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255463 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_7255463 : Nat := 118140960795 + 7255463 * 2 ^ 59
def prefixEnd_7255463 : Nat := 4983230072969 + 3 ^ 40 * 7255463 * 2
def baseEnd_7255463 : Nat := 3725539889912251701345239

theorem tailTrace_7255463 : CollatzResearch.WordTrace tailWord_7255463 prefixEnd_7255463 3725539889912251701345239 := by
  unfold tailWord_7255463
  simp only [CollatzResearch.WordTrace]
  refine ⟨264628475713704160272979043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176418983809136106848652695 264628475713704160272979043)
  ·
    refine ⟨396942713570556240409468565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264628475713704160272979043 396942713570556240409468565)
    ·
      refine ⟨18606689698619823769193839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 396942713570556240409468565 18606689698619823769193839)
      ·
        refine ⟨27910034547929735653790759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18606689698619823769193839 27910034547929735653790759)
        ·
          refine ⟨41865051821894603480686139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27910034547929735653790759 41865051821894603480686139)
          ·
            refine ⟨62797577732841905221029209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41865051821894603480686139 62797577732841905221029209)
            ·
              refine ⟨47098183299631428915771907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62797577732841905221029209 47098183299631428915771907)
              ·
                refine ⟨70647274949447143373657861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47098183299631428915771907 70647274949447143373657861)
                ·
                  refine ⟨13246364053021339382560849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70647274949447143373657861 13246364053021339382560849)
                  ·
                    refine ⟨9934773039766004536920637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13246364053021339382560849 9934773039766004536920637)
                    ·
                      refine ⟨3725539889912251701345239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934773039766004536920637 3725539889912251701345239)
                      ·
                        rfl

theorem cell23_7255463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_7255463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255463 prefixEnd_7255463 := by exact prefixLift 7255463
  have htrace : WordTrace (prefixWord ++ tailWord_7255463) baseStart_7255463 baseEnd_7255463 := by
    simpa [prefixWord, tailWord_7255463, baseEnd_7255463] using wordTrace_append hprefix tailTrace_7255463
  have hstable : (prefixWord ++ tailWord_7255463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255463).length < 2 ^ (prefixWord ++ tailWord_7255463).sum := by decide
  have hdescent : baseEnd_7255463 < baseStart_7255463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255486 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_7255486 : Nat := 118140960795 + 7255486 * 2 ^ 59
def prefixEnd_7255486 : Nat := 4983230072969 + 3 ^ 40 * 7255486 * 2
def baseEnd_7255486 : Nat := 3725551699967305111357633

theorem tailTrace_7255486 : CollatzResearch.WordTrace tailWord_7255486 prefixEnd_7255486 3725551699967305111357633 := by
  unfold tailWord_7255486
  simp only [CollatzResearch.WordTrace]
  refine ⟨33078664324077604400133289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176419543061747223467377541 33078664324077604400133289)
  ·
    refine ⟨24808998243058203300099967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33078664324077604400133289 24808998243058203300099967)
    ·
      refine ⟨37213497364587304950149951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24808998243058203300099967 37213497364587304950149951)
      ·
        refine ⟨55820246046880957425224927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37213497364587304950149951 55820246046880957425224927)
        ·
          refine ⟨83730369070321436137837391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55820246046880957425224927 83730369070321436137837391)
          ·
            refine ⟨125595553605482154206756087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83730369070321436137837391 125595553605482154206756087)
            ·
              refine ⟨188393330408223231310134131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125595553605482154206756087 188393330408223231310134131)
              ·
                refine ⟨282589995612334846965201197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188393330408223231310134131 282589995612334846965201197)
                ·
                  refine ⟨105971248354625567611950449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282589995612334846965201197 105971248354625567611950449)
                  ·
                    refine ⟨79478436265969175708962837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105971248354625567611950449 79478436265969175708962837)
                    ·
                      refine ⟨3725551699967305111357633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79478436265969175708962837 3725551699967305111357633)
                      ·
                        rfl

theorem cell23_7255486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_7255486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255486 prefixEnd_7255486 := by exact prefixLift 7255486
  have htrace : WordTrace (prefixWord ++ tailWord_7255486) baseStart_7255486 baseEnd_7255486 := by
    simpa [prefixWord, tailWord_7255486, baseEnd_7255486] using wordTrace_append hprefix tailTrace_7255486
  have hstable : (prefixWord ++ tailWord_7255486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255486).length < 2 ^ (prefixWord ++ tailWord_7255486).sum := by decide
  have hdescent : baseEnd_7255486 < baseStart_7255486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255503 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 5, 2]
def baseStart_7255503 : Nat := 118140960795 + 7255503 * 2 ^ 59
def prefixEnd_7255503 : Nat := 4983230072969 + 3 ^ 40 * 7255503 * 2
def baseEnd_7255503 : Nat := 3725560429138431544845055

theorem tailTrace_7255503 : CollatzResearch.WordTrace tailWord_7255503 prefixEnd_7255503 3725560429138431544845055 := by
  unfold tailWord_7255503
  simp only [CollatzResearch.WordTrace]
  refine ⟨264629934633559247104435163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176419956422372831402956775 264629934633559247104435163)
  ·
    refine ⟨396944901950338870656652745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264629934633559247104435163 396944901950338870656652745)
    ·
      refine ⟨297708676462754152992489559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396944901950338870656652745 297708676462754152992489559)
      ·
        refine ⟨446563014694131229488734339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297708676462754152992489559 446563014694131229488734339)
        ·
          refine ⟨669844522041196844233101509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446563014694131229488734339 669844522041196844233101509)
          ·
            refine ⟨125595847882724408293706533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 669844522041196844233101509 125595847882724408293706533)
            ·
              refine ⟨23549221478010826555069975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125595847882724408293706533 23549221478010826555069975)
              ·
                refine ⟨35323832217016239832604963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23549221478010826555069975 35323832217016239832604963)
                ·
                  refine ⟨52985748325524359748907445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35323832217016239832604963 52985748325524359748907445)
                  ·
                    refine ⟨4967413905517908726460073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52985748325524359748907445 4967413905517908726460073)
                    ·
                      refine ⟨3725560429138431544845055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967413905517908726460073 3725560429138431544845055)
                      ·
                        rfl

theorem cell23_7255503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 5, 2].length) (baseStart_7255503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255503 prefixEnd_7255503 := by exact prefixLift 7255503
  have htrace : WordTrace (prefixWord ++ tailWord_7255503) baseStart_7255503 baseEnd_7255503 := by
    simpa [prefixWord, tailWord_7255503, baseEnd_7255503] using wordTrace_append hprefix tailTrace_7255503
  have hstable : (prefixWord ++ tailWord_7255503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255503).length < 2 ^ (prefixWord ++ tailWord_7255503).sum := by decide
  have hdescent : baseEnd_7255503 < baseStart_7255503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255513 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_7255513 : Nat := 118140960795 + 7255513 * 2 ^ 59
def prefixEnd_7255513 : Nat := 4983230072969 + 3 ^ 40 * 7255513 * 2
def baseEnd_7255513 : Nat := 1241855187981658835240003

theorem tailTrace_7255513 : CollatzResearch.WordTrace tailWord_7255513 prefixEnd_7255513 1241855187981658835240003 := by
  unfold tailWord_7255513
  simp only [CollatzResearch.WordTrace]
  refine ⟨264630299363523018812299193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176420199575682012541532795 264630299363523018812299193)
  ·
    refine ⟨198472724522642264109224395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264630299363523018812299193 198472724522642264109224395)
    ·
      refine ⟨297709086783963396163836593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198472724522642264109224395 297709086783963396163836593)
      ·
        refine ⟨223281815087972547122877445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297709086783963396163836593 223281815087972547122877445)
        ·
          refine ⟨41865340328994852585539521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223281815087972547122877445 41865340328994852585539521)
          ·
            refine ⟨31399005246746139439154641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41865340328994852585539521 31399005246746139439154641)
            ·
              refine ⟨23549253935059604579365981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31399005246746139439154641 23549253935059604579365981)
              ·
                refine ⟨8830970225647351717262243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23549253935059604579365981 8830970225647351717262243)
                ·
                  refine ⟨13246455338471027575893365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8830970225647351717262243 13246455338471027575893365)
                  ·
                    refine ⟨1241855187981658835240003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13246455338471027575893365 1241855187981658835240003)
                    ·
                      rfl

theorem cell23_7255513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_7255513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255513 prefixEnd_7255513 := by exact prefixLift 7255513
  have htrace : WordTrace (prefixWord ++ tailWord_7255513) baseStart_7255513 baseEnd_7255513 := by
    simpa [prefixWord, tailWord_7255513, baseEnd_7255513] using wordTrace_append hprefix tailTrace_7255513
  have hstable : (prefixWord ++ tailWord_7255513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255513).length < 2 ^ (prefixWord ++ tailWord_7255513).sum := by decide
  have hdescent : baseEnd_7255513 < baseStart_7255513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255527 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7255527 : Nat := 118140960795 + 7255527 * 2 ^ 59
def prefixEnd_7255527 : Nat := 4983230072969 + 3 ^ 40 * 7255527 * 2
def baseEnd_7255527 : Nat := 3725572752674139450944945

theorem tailTrace_7255527 : CollatzResearch.WordTrace tailWord_7255527 prefixEnd_7255527 3725572752674139450944945 := by
  unfold tailWord_7255527
  simp only [CollatzResearch.WordTrace]
  refine ⟨264630809985472299203308835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176420539990314866135539223 264630809985472299203308835)
  ·
    refine ⟨396946214978208448804963253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264630809985472299203308835 396946214978208448804963253)
    ·
      refine ⟨37213707654207042075465305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396946214978208448804963253 37213707654207042075465305)
      ·
        refine ⟨27910280740655281556598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37213707654207042075465305 27910280740655281556598979)
        ·
          refine ⟨41865421110982922334898469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27910280740655281556598979 41865421110982922334898469)
          ·
            refine ⟨7849766458309297937793463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41865421110982922334898469 7849766458309297937793463)
            ·
              refine ⟨11774649687463946906690195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849766458309297937793463 11774649687463946906690195)
              ·
                refine ⟨17661974531195920360035293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774649687463946906690195 17661974531195920360035293)
                ·
                  refine ⟨6623240449198470135013235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17661974531195920360035293 6623240449198470135013235)
                  ·
                    refine ⟨9934860673797705202519853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623240449198470135013235 9934860673797705202519853)
                    ·
                      refine ⟨3725572752674139450944945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9934860673797705202519853 3725572752674139450944945)
                      ·
                        rfl

theorem cell23_7255527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7255527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255527 prefixEnd_7255527 := by exact prefixLift 7255527
  have htrace : WordTrace (prefixWord ++ tailWord_7255527) baseStart_7255527 baseEnd_7255527 := by
    simpa [prefixWord, tailWord_7255527, baseEnd_7255527] using wordTrace_append hprefix tailTrace_7255527
  have hstable : (prefixWord ++ tailWord_7255527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255527).length < 2 ^ (prefixWord ++ tailWord_7255527).sum := by decide
  have hdescent : baseEnd_7255527 < baseStart_7255527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255546 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_7255546 : Nat := 118140960795 + 7255546 * 2 ^ 59
def prefixEnd_7255546 : Nat := 4983230072969 + 3 ^ 40 * 7255546 * 2
def baseEnd_7255546 : Nat := 3725582508806574876607357

theorem tailTrace_7255546 : CollatzResearch.WordTrace tailWord_7255546 prefixEnd_7255546 3725582508806574876607357 := by
  unfold tailWord_7255546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66157875743100866362062623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176421001981602310298833661 66157875743100866362062623)
  ·
    refine ⟨99236813614651299543093935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66157875743100866362062623 99236813614651299543093935)
    ·
      refine ⟨148855220421976949314640903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99236813614651299543093935 148855220421976949314640903)
      ·
        refine ⟨223282830632965423971961355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148855220421976949314640903 223282830632965423971961355)
        ·
          refine ⟨334924245949448135957942033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223282830632965423971961355 334924245949448135957942033)
          ·
            refine ⟨251193184462086101968456525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334924245949448135957942033 251193184462086101968456525)
            ·
              refine ⟨94197444173282288238171197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251193184462086101968456525 94197444173282288238171197)
              ·
                refine ⟨35324041564980858089314199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94197444173282288238171197 35324041564980858089314199)
                ·
                  refine ⟨52986062347471287133971299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35324041564980858089314199 52986062347471287133971299)
                  ·
                    refine ⟨79479093521206930700956949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52986062347471287133971299 79479093521206930700956949)
                    ·
                      refine ⟨3725582508806574876607357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79479093521206930700956949 3725582508806574876607357)
                      ·
                        rfl

theorem cell23_7255546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_7255546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255546 prefixEnd_7255546 := by exact prefixLift 7255546
  have htrace : WordTrace (prefixWord ++ tailWord_7255546) baseStart_7255546 baseEnd_7255546 := by
    simpa [prefixWord, tailWord_7255546, baseEnd_7255546] using wordTrace_append hprefix tailTrace_7255546
  have hstable : (prefixWord ++ tailWord_7255546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255546).length < 2 ^ (prefixWord ++ tailWord_7255546).sum := by decide
  have hdescent : baseEnd_7255546 < baseStart_7255546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255554 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7255554 : Nat := 118140960795 + 7255554 * 2 ^ 59
def prefixEnd_7255554 : Nat := 4983230072969 + 3 ^ 40 * 7255554 * 2
def baseEnd_7255554 : Nat := 3725586616651810845307321

theorem tailTrace_7255554 : CollatzResearch.WordTrace tailWord_7255554 prefixEnd_7255554 3725586616651810845307321 := by
  unfold tailWord_7255554
  simp only [CollatzResearch.WordTrace]
  refine ⟨66157948689093620703635429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176421196504249655209694477 66157948689093620703635429)
  ·
    refine ⟨12404615379205053881931643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66157948689093620703635429 12404615379205053881931643)
    ·
      refine ⟨18606923068807580822897465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12404615379205053881931643 18606923068807580822897465)
      ·
        refine ⟨13955192301605685617173099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606923068807580822897465 13955192301605685617173099)
        ·
          refine ⟨20932788452408528425759649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13955192301605685617173099 20932788452408528425759649)
          ·
            refine ⟨15699591339306396319319737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20932788452408528425759649 15699591339306396319319737)
            ·
              refine ⟨11774693504479797239489803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15699591339306396319319737 11774693504479797239489803)
              ·
                refine ⟨17662040256719695859234705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774693504479797239489803 17662040256719695859234705)
                ·
                  refine ⟨13246530192539771894426029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17662040256719695859234705 13246530192539771894426029)
                  ·
                    refine ⟨4967448822202414460409761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13246530192539771894426029 4967448822202414460409761)
                    ·
                      refine ⟨3725586616651810845307321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967448822202414460409761 3725586616651810845307321)
                      ·
                        rfl

theorem cell23_7255554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7255554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255554 prefixEnd_7255554 := by exact prefixLift 7255554
  have htrace : WordTrace (prefixWord ++ tailWord_7255554) baseStart_7255554 baseEnd_7255554 := by
    simpa [prefixWord, tailWord_7255554, baseEnd_7255554] using wordTrace_append hprefix tailTrace_7255554
  have hstable : (prefixWord ++ tailWord_7255554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255554).length < 2 ^ (prefixWord ++ tailWord_7255554).sum := by decide
  have hdescent : baseEnd_7255554 < baseStart_7255554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255596 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7255596 : Nat := 118140960795 + 7255596 * 2 ^ 59
def prefixEnd_7255596 : Nat := 4983230072969 + 3 ^ 40 * 7255596 * 2
def baseEnd_7255596 : Nat := 3725608182839299680982127

theorem tailTrace_7255596 : CollatzResearch.WordTrace tailWord_7255596 prefixEnd_7255596 3725608182839299680982127 := by
  unfold tailWord_7255596
  simp only [CollatzResearch.WordTrace]
  refine ⟨132316663311111161993785321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176422217748148215991713761 132316663311111161993785321)
  ·
    refine ⟨99237497483333371495338991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132316663311111161993785321 99237497483333371495338991)
    ·
      refine ⟨148856246225000057243008487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99237497483333371495338991 148856246225000057243008487)
      ·
        refine ⟨223284369337500085864512731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148856246225000057243008487 223284369337500085864512731)
        ·
          refine ⟨334926554006250128796769097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223284369337500085864512731 334926554006250128796769097)
          ·
            refine ⟨251194915504687596597576823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334926554006250128796769097 251194915504687596597576823)
            ·
              refine ⟨376792373257031394896365235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251194915504687596597576823 376792373257031394896365235)
              ·
                refine ⟨565188559885547092344547853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376792373257031394896365235 565188559885547092344547853)
                ·
                  refine ⟨211945709957080159629205445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565188559885547092344547853 211945709957080159629205445)
                  ·
                    refine ⟨39739820616952529930476021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211945709957080159629205445 39739820616952529930476021)
                    ·
                      refine ⟨3725608182839299680982127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39739820616952529930476021 3725608182839299680982127)
                      ·
                        rfl

theorem cell23_7255596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7255596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255596 prefixEnd_7255596 := by exact prefixLift 7255596
  have htrace : WordTrace (prefixWord ++ tailWord_7255596) baseStart_7255596 baseEnd_7255596 := by
    simpa [prefixWord, tailWord_7255596, baseEnd_7255596] using wordTrace_append hprefix tailTrace_7255596
  have hstable : (prefixWord ++ tailWord_7255596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255596).length < 2 ^ (prefixWord ++ tailWord_7255596).sum := by decide
  have hdescent : baseEnd_7255596 < baseStart_7255596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255610 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_7255610 : Nat := 118140960795 + 7255610 * 2 ^ 59
def prefixEnd_7255610 : Nat := 4983230072969 + 3 ^ 40 * 7255610 * 2
def baseEnd_7255610 : Nat := 3725615371568462626207063

theorem tailTrace_7255610 : CollatzResearch.WordTrace tailWord_7255610 prefixEnd_7255610 3725615371568462626207063 := by
  unfold tailWord_7255610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66158459311042901094645071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176422558162781069585720189 66158459311042901094645071)
  ·
    refine ⟨99237688966564351641967607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66158459311042901094645071 99237688966564351641967607)
    ·
      refine ⟨148856533449846527462951411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99237688966564351641967607 148856533449846527462951411)
      ·
        refine ⟨223284800174769791194427117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148856533449846527462951411 223284800174769791194427117)
        ·
          refine ⟨83731800065538671697910169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223284800174769791194427117 83731800065538671697910169)
          ·
            refine ⟨62798850049154003773432627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83731800065538671697910169 62798850049154003773432627)
            ·
              refine ⟨94198275073731005660148941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62798850049154003773432627 94198275073731005660148941)
              ·
                refine ⟨35324353152649127122555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94198275073731005660148941 35324353152649127122555853)
                ·
                  refine ⟨13246632432243422670958445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35324353152649127122555853 13246632432243422670958445)
                  ·
                    refine ⟨4967487162091283501609417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13246632432243422670958445 4967487162091283501609417)
                    ·
                      refine ⟨3725615371568462626207063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967487162091283501609417 3725615371568462626207063)
                      ·
                        rfl

theorem cell23_7255610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_7255610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255610 prefixEnd_7255610 := by exact prefixLift 7255610
  have htrace : WordTrace (prefixWord ++ tailWord_7255610) baseStart_7255610 baseEnd_7255610 := by
    simpa [prefixWord, tailWord_7255610, baseEnd_7255610] using wordTrace_append hprefix tailTrace_7255610
  have hstable : (prefixWord ++ tailWord_7255610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255610).length < 2 ^ (prefixWord ++ tailWord_7255610).sum := by decide
  have hdescent : baseEnd_7255610 < baseStart_7255610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255616 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_7255616 : Nat := 118140960795 + 7255616 * 2 ^ 59
def prefixEnd_7255616 : Nat := 4983230072969 + 3 ^ 40 * 7255616 * 2
def baseEnd_7255616 : Nat := 1241872817484129867577345

theorem tailTrace_7255616 : CollatzResearch.WordTrace tailWord_7255616 prefixEnd_7255616 1241872817484129867577345 := by
  unfold tailWord_7255616
  simp only [CollatzResearch.WordTrace]
  refine ⟨132317028041074933701649351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176422704054766578268865801 132317028041074933701649351)
  ·
    refine ⟨198475542061612400552474027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132317028041074933701649351 198475542061612400552474027)
    ·
      refine ⟨297713313092418600828711041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198475542061612400552474027 297713313092418600828711041)
      ·
        refine ⟨223284984819313950621533281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297713313092418600828711041 223284984819313950621533281)
        ·
          refine ⟨167463738614485462966149961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223284984819313950621533281 167463738614485462966149961)
          ·
            refine ⟨125597803960864097224612471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167463738614485462966149961 125597803960864097224612471)
            ·
              refine ⟨188396705941296145836918707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125597803960864097224612471 188396705941296145836918707)
              ·
                refine ⟨282595058911944218755378061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188396705941296145836918707 282595058911944218755378061)
                ·
                  refine ⟨105973147091979082033266773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282595058911944218755378061 105973147091979082033266773)
                  ·
                    refine ⟨1241872817484129867577345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105973147091979082033266773 1241872817484129867577345)
                    ·
                      rfl

theorem cell23_7255616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_7255616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255616 prefixEnd_7255616 := by exact prefixLift 7255616
  have htrace : WordTrace (prefixWord ++ tailWord_7255616) baseStart_7255616 baseEnd_7255616 := by
    simpa [prefixWord, tailWord_7255616, baseEnd_7255616] using wordTrace_append hprefix tailTrace_7255616
  have hstable : (prefixWord ++ tailWord_7255616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255616).length < 2 ^ (prefixWord ++ tailWord_7255616).sum := by decide
  have hdescent : baseEnd_7255616 < baseStart_7255616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255634 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_7255634 : Nat := 118140960795 + 7255634 * 2 ^ 59
def prefixEnd_7255634 : Nat := 4983230072969 + 3 ^ 40 * 7255634 * 2
def baseEnd_7255634 : Nat := 3725627695104170532306953

theorem tailTrace_7255634 : CollatzResearch.WordTrace tailWord_7255634 prefixEnd_7255634 3725627695104170532306953 := by
  unfold tailWord_7255634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66158678149021164119363489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176423141730723104318302637 66158678149021164119363489)
  ·
    refine ⟨49619008611765873089522617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66158678149021164119363489 49619008611765873089522617)
    ·
      refine ⟨37214256458824404817141963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49619008611765873089522617 37214256458824404817141963)
      ·
        refine ⟨55821384688236607225712945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37214256458824404817141963 55821384688236607225712945)
        ·
          refine ⟨41866038516177455419284709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55821384688236607225712945 41866038516177455419284709)
          ·
            refine ⟨7849882221783272891115883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41866038516177455419284709 7849882221783272891115883)
            ·
              refine ⟨11774823332674909336673825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849882221783272891115883 11774823332674909336673825)
              ·
                refine ⟨8831117499506182002505369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774823332674909336673825 8831117499506182002505369)
                ·
                  refine ⟨6623338124629636501879027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831117499506182002505369 6623338124629636501879027)
                  ·
                    refine ⟨9935007186944454752818541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623338124629636501879027 9935007186944454752818541)
                    ·
                      refine ⟨3725627695104170532306953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935007186944454752818541 3725627695104170532306953)
                      ·
                        rfl

theorem cell23_7255634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_7255634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255634 prefixEnd_7255634 := by exact prefixLift 7255634
  have htrace : WordTrace (prefixWord ++ tailWord_7255634) baseStart_7255634 baseEnd_7255634 := by
    simpa [prefixWord, tailWord_7255634, baseEnd_7255634] using wordTrace_append hprefix tailTrace_7255634
  have hstable : (prefixWord ++ tailWord_7255634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255634).length < 2 ^ (prefixWord ++ tailWord_7255634).sum := by decide
  have hdescent : baseEnd_7255634 < baseStart_7255634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255657 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 2, 2, 2]
def baseStart_7255657 : Nat := 118140960795 + 7255657 * 2 ^ 59
def prefixEnd_7255657 : Nat := 4983230072969 + 3 ^ 40 * 7255657 * 2
def baseEnd_7255657 : Nat := 3725639505159223942319347

theorem tailTrace_7255657 : CollatzResearch.WordTrace tailWord_7255657 prefixEnd_7255657 3725639505159223942319347 := by
  unfold tailWord_7255657
  simp only [CollatzResearch.WordTrace]
  refine ⟨264635551475001331405541225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176423700983334220937027483 264635551475001331405541225)
  ·
    refine ⟨198476663606250998554155919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264635551475001331405541225 198476663606250998554155919)
    ·
      refine ⟨297714995409376497831233879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198476663606250998554155919 297714995409376497831233879)
      ·
        refine ⟨446572493114064746746850819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297714995409376497831233879 446572493114064746746850819)
        ·
          refine ⟨669858739671097120120276229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446572493114064746746850819 669858739671097120120276229)
          ·
            refine ⟨125598513688330710022551793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 669858739671097120120276229 125598513688330710022551793)
            ·
              refine ⟨94198885266248032516913845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125598513688330710022551793 94198885266248032516913845)
              ·
                refine ⟨8831145493710753048460673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94198885266248032516913845 8831145493710753048460673)
                ·
                  refine ⟨6623359120283064786345505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831145493710753048460673 6623359120283064786345505)
                  ·
                    refine ⟨4967519340212298589759129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6623359120283064786345505 4967519340212298589759129)
                    ·
                      refine ⟨3725639505159223942319347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967519340212298589759129 3725639505159223942319347)
                      ·
                        rfl

theorem cell23_7255657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2, 2].length) (baseStart_7255657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255657 prefixEnd_7255657 := by exact prefixLift 7255657
  have htrace : WordTrace (prefixWord ++ tailWord_7255657) baseStart_7255657 baseEnd_7255657 := by
    simpa [prefixWord, tailWord_7255657, baseEnd_7255657] using wordTrace_append hprefix tailTrace_7255657
  have hstable : (prefixWord ++ tailWord_7255657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255657).length < 2 ^ (prefixWord ++ tailWord_7255657).sum := by decide
  have hdescent : baseEnd_7255657 < baseStart_7255657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255703 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_7255703 : Nat := 118140960795 + 7255703 * 2 ^ 59
def prefixEnd_7255703 : Nat := 4983230072969 + 3 ^ 40 * 7255703 * 2
def baseEnd_7255703 : Nat := 3725663125269330762344135

theorem tailTrace_7255703 : CollatzResearch.WordTrace tailWord_7255703 prefixEnd_7255703 3725663125269330762344135 := by
  unfold tailWord_7255703
  simp only [CollatzResearch.WordTrace]
  refine ⟨264637229232834681261715763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176424819488556454174477175 264637229232834681261715763)
  ·
    refine ⟨396955843849252021892573645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264637229232834681261715763 396955843849252021892573645)
    ·
      refine ⟨148858441443469508209715117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396955843849252021892573645 148858441443469508209715117)
      ·
        refine ⟨55821915541301065578643169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148858441443469508209715117 55821915541301065578643169)
        ·
          refine ⟨41866436655975799183982377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55821915541301065578643169 41866436655975799183982377)
          ·
            refine ⟨31399827491981849387986783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41866436655975799183982377 31399827491981849387986783)
            ·
              refine ⟨47099741237972774081980175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31399827491981849387986783 47099741237972774081980175)
              ·
                refine ⟨70649611856959161122970263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47099741237972774081980175 70649611856959161122970263)
                ·
                  refine ⟨105974417785438741684455395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70649611856959161122970263 105974417785438741684455395)
                  ·
                    refine ⟨158961626678158112526683093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105974417785438741684455395 158961626678158112526683093)
                    ·
                      refine ⟨3725663125269330762344135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158961626678158112526683093 3725663125269330762344135)
                      ·
                        rfl

theorem cell23_7255703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_7255703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255703 prefixEnd_7255703 := by exact prefixLift 7255703
  have htrace : WordTrace (prefixWord ++ tailWord_7255703) baseStart_7255703 baseEnd_7255703 := by
    simpa [prefixWord, tailWord_7255703, baseEnd_7255703] using wordTrace_append hprefix tailTrace_7255703
  have hstable : (prefixWord ++ tailWord_7255703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255703).length < 2 ^ (prefixWord ++ tailWord_7255703).sum := by decide
  have hdescent : baseEnd_7255703 < baseStart_7255703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255708 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7255708 : Nat := 118140960795 + 7255708 * 2 ^ 59
def prefixEnd_7255708 : Nat := 4983230072969 + 3 ^ 40 * 7255708 * 2
def baseEnd_7255708 : Nat := 3725665692672603242781613

theorem tailTrace_7255708 : CollatzResearch.WordTrace tailWord_7255708 prefixEnd_7255708 3725665692672603242781613 := by
  unfold tailWord_7255708
  simp only [CollatzResearch.WordTrace]
  refine ⟨132318705798908283557823889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176424941065211044743765185 132318705798908283557823889)
  ·
    refine ⟨99239029349181212668367917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132318705798908283557823889 99239029349181212668367917)
    ·
      refine ⟨37214636005942954750637969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99239029349181212668367917 37214636005942954750637969)
      ·
        refine ⟨27910977004457216062978477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37214636005942954750637969 27910977004457216062978477)
        ·
          refine ⟨10466616376671456023616929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27910977004457216062978477 10466616376671456023616929)
          ·
            refine ⟨7849962282503592017712697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10466616376671456023616929 7849962282503592017712697)
            ·
              refine ⟨5887471711877694013284523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7849962282503592017712697 5887471711877694013284523)
              ·
                refine ⟨8831207567816541019926785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887471711877694013284523 8831207567816541019926785)
                ·
                  refine ⟨6623405675862405764945089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831207567816541019926785 6623405675862405764945089)
                  ·
                    refine ⟨4967554256896804323708817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6623405675862405764945089 4967554256896804323708817)
                    ·
                      refine ⟨3725665692672603242781613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967554256896804323708817 3725665692672603242781613)
                      ·
                        rfl

theorem cell23_7255708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7255708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255708 prefixEnd_7255708 := by exact prefixLift 7255708
  have htrace : WordTrace (prefixWord ++ tailWord_7255708) baseStart_7255708 baseEnd_7255708 := by
    simpa [prefixWord, tailWord_7255708, baseEnd_7255708] using wordTrace_append hprefix tailTrace_7255708
  have hstable : (prefixWord ++ tailWord_7255708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255708).length < 2 ^ (prefixWord ++ tailWord_7255708).sum := by decide
  have hdescent : baseEnd_7255708 < baseStart_7255708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255730 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7255730 : Nat := 118140960795 + 7255730 * 2 ^ 59
def prefixEnd_7255730 : Nat := 4983230072969 + 3 ^ 40 * 7255730 * 2
def baseEnd_7255730 : Nat := 3725676989247002156706511

theorem tailTrace_7255730 : CollatzResearch.WordTrace tailWord_7255730 prefixEnd_7255730 3725676989247002156706511 := by
  unfold tailWord_7255730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66159553500934216218237161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176425476002491243248632429 66159553500934216218237161)
  ·
    refine ⟨49619665125700662163677871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66159553500934216218237161 49619665125700662163677871)
    ·
      refine ⟨74429497688550993245516807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49619665125700662163677871 74429497688550993245516807)
      ·
        refine ⟨111644246532826489868275211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74429497688550993245516807 111644246532826489868275211)
        ·
          refine ⟨167466369799239734802412817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111644246532826489868275211 167466369799239734802412817)
          ·
            refine ⟨125599777349429801101809613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167466369799239734802412817 125599777349429801101809613)
            ·
              refine ⟨47099916506036175413178605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125599777349429801101809613 47099916506036175413178605)
              ·
                refine ⟨17662468689763565779941977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47099916506036175413178605 17662468689763565779941977)
                ·
                  refine ⟨13246851517322674334956483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17662468689763565779941977 13246851517322674334956483)
                  ·
                    refine ⟨19870277275984011502434725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13246851517322674334956483 19870277275984011502434725)
                    ·
                      refine ⟨3725676989247002156706511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19870277275984011502434725 3725676989247002156706511)
                      ·
                        rfl

theorem cell23_7255730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7255730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255730 prefixEnd_7255730 := by exact prefixLift 7255730
  have htrace : WordTrace (prefixWord ++ tailWord_7255730) baseStart_7255730 baseEnd_7255730 := by
    simpa [prefixWord, tailWord_7255730, baseEnd_7255730] using wordTrace_append hprefix tailTrace_7255730
  have hstable : (prefixWord ++ tailWord_7255730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255730).length < 2 ^ (prefixWord ++ tailWord_7255730).sum := by decide
  have hdescent : baseEnd_7255730 < baseStart_7255730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255743 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_7255743 : Nat := 118140960795 + 7255743 * 2 ^ 59
def prefixEnd_7255743 : Nat := 4983230072969 + 3 ^ 40 * 7255743 * 2
def baseEnd_7255743 : Nat := 3725683664495510605843951

theorem tailTrace_7255743 : CollatzResearch.WordTrace tailWord_7255743 prefixEnd_7255743 3725683664495510605843951 := by
  unfold tailWord_7255743
  simp only [CollatzResearch.WordTrace]
  refine ⟨264638688152689768093171883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176425792101793178728781255 264638688152689768093171883)
  ·
    refine ⟨396958032229034652139757825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264638688152689768093171883 396958032229034652139757825)
    ·
      refine ⟨297718524171775989104818369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396958032229034652139757825 297718524171775989104818369)
      ·
        refine ⟨223288893128831991828613777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297718524171775989104818369 223288893128831991828613777)
        ·
          refine ⟨167466669846623993871460333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223288893128831991828613777 167466669846623993871460333)
          ·
            refine ⟨62800001192483997701797625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167466669846623993871460333 62800001192483997701797625)
            ·
              refine ⟨47100000894362998276348219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62800001192483997701797625 47100000894362998276348219)
              ·
                refine ⟨70650001341544497414522329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47100000894362998276348219 70650001341544497414522329)
                ·
                  refine ⟨52987501006158373060891747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70650001341544497414522329 52987501006158373060891747)
                  ·
                    refine ⟨79481251509237559591337621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52987501006158373060891747 79481251509237559591337621)
                    ·
                      refine ⟨3725683664495510605843951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79481251509237559591337621 3725683664495510605843951)
                      ·
                        rfl

theorem cell23_7255743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_7255743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255743 prefixEnd_7255743 := by exact prefixLift 7255743
  have htrace : WordTrace (prefixWord ++ tailWord_7255743) baseStart_7255743 baseEnd_7255743 := by
    simpa [prefixWord, tailWord_7255743, baseEnd_7255743] using wordTrace_append hprefix tailTrace_7255743
  have hstable : (prefixWord ++ tailWord_7255743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255743).length < 2 ^ (prefixWord ++ tailWord_7255743).sum := by decide
  have hdescent : baseEnd_7255743 < baseStart_7255743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255764 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7255764 : Nat := 118140960795 + 7255764 * 2 ^ 59
def prefixEnd_7255764 : Nat := 4983230072969 + 3 ^ 40 * 7255764 * 2
def baseEnd_7255764 : Nat := 3725694447589255023681355

theorem tailTrace_7255764 : CollatzResearch.WordTrace tailWord_7255764 prefixEnd_7255764 3725694447589255023681355 := by
  unfold tailWord_7255764
  simp only [CollatzResearch.WordTrace]
  refine ⟨132319727042806844339843173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176426302723742459119790897 132319727042806844339843173)
  ·
    refine ⟨24809948820526283313720595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132319727042806844339843173 24809948820526283313720595)
    ·
      refine ⟨37214923230789424970580893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24809948820526283313720595 37214923230789424970580893)
      ·
        refine ⟨13955596211546034363967835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37214923230789424970580893 13955596211546034363967835)
        ·
          refine ⟨20933394317319051545951753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13955596211546034363967835 20933394317319051545951753)
          ·
            refine ⟨15700045737989288659463815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20933394317319051545951753 15700045737989288659463815)
            ·
              refine ⟨23550068606983932989195723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700045737989288659463815 23550068606983932989195723)
              ·
                refine ⟨35325102910475899483793585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23550068606983932989195723 35325102910475899483793585)
                ·
                  refine ⟨26493827182856924612845189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35325102910475899483793585 26493827182856924612845189)
                  ·
                    refine ⟨4967592596785673364908473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26493827182856924612845189 4967592596785673364908473)
                    ·
                      refine ⟨3725694447589255023681355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967592596785673364908473 3725694447589255023681355)
                      ·
                        rfl

theorem cell23_7255764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7255764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255764 prefixEnd_7255764 := by exact prefixLift 7255764
  have htrace : WordTrace (prefixWord ++ tailWord_7255764) baseStart_7255764 baseEnd_7255764 := by
    simpa [prefixWord, tailWord_7255764, baseEnd_7255764] using wordTrace_append hprefix tailTrace_7255764
  have hstable : (prefixWord ++ tailWord_7255764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255764).length < 2 ^ (prefixWord ++ tailWord_7255764).sum := by decide
  have hdescent : baseEnd_7255764 < baseStart_7255764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255770 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_7255770 : Nat := 118140960795 + 7255770 * 2 ^ 59
def prefixEnd_7255770 : Nat := 4983230072969 + 3 ^ 40 * 7255770 * 2
def baseEnd_7255770 : Nat := 413966392052575777800703

theorem tailTrace_7255770 : CollatzResearch.WordTrace tailWord_7255770 prefixEnd_7255770 413966392052575777800703 := by
  unfold tailWord_7255770
  simp only [CollatzResearch.WordTrace]
  refine ⟨66159918230897987926101191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176426448615727967802936509 66159918230897987926101191)
  ·
    refine ⟨99239877346346981889151787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66159918230897987926101191 99239877346346981889151787)
    ·
      refine ⟨148859816019520472833727681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99239877346346981889151787 148859816019520472833727681)
      ·
        refine ⟨111644862014640354625295761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148859816019520472833727681 111644862014640354625295761)
        ·
          refine ⟨83733646510980265968971821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111644862014640354625295761 83733646510980265968971821)
          ·
            refine ⟨31400117441617599738364433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83733646510980265968971821 31400117441617599738364433)
            ·
              refine ⟨23550088081213199803773325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31400117441617599738364433 23550088081213199803773325)
              ·
                refine ⟨8831283030454949926414997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23550088081213199803773325 8831283030454949926414997)
                ·
                  refine ⟨413966392052575777800703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8831283030454949926414997 413966392052575777800703)
                  ·
                    rfl

theorem cell23_7255770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_7255770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255770 prefixEnd_7255770 := by exact prefixLift 7255770
  have htrace : WordTrace (prefixWord ++ tailWord_7255770) baseStart_7255770 baseEnd_7255770 := by
    simpa [prefixWord, tailWord_7255770, baseEnd_7255770] using wordTrace_append hprefix tailTrace_7255770
  have hstable : (prefixWord ++ tailWord_7255770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255770).length < 2 ^ (prefixWord ++ tailWord_7255770).sum := by decide
  have hdescent : baseEnd_7255770 < baseStart_7255770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255784 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7255784 : Nat := 118140960795 + 7255784 * 2 ^ 59
def prefixEnd_7255784 : Nat := 4983230072969 + 3 ^ 40 * 7255784 * 2
def baseEnd_7255784 : Nat := 3725704717202344945431263

theorem tailTrace_7255784 : CollatzResearch.WordTrace tailWord_7255784 prefixEnd_7255784 3725704717202344945431263 := by
  unfold tailWord_7255784
  simp only [CollatzResearch.WordTrace]
  refine ⟨132320091772770616047707203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176426789030360821396942937 132320091772770616047707203)
  ·
    refine ⟨198480137659155924071560805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132320091772770616047707203 198480137659155924071560805)
    ·
      refine ⟨37215025811091735763417651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198480137659155924071560805 37215025811091735763417651)
      ·
        refine ⟨55822538716637603645126477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37215025811091735763417651 55822538716637603645126477)
        ·
          refine ⟨20933452018739101366922429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55822538716637603645126477 20933452018739101366922429)
          ·
            refine ⟨7850044507027163012595911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20933452018739101366922429 7850044507027163012595911)
            ·
              refine ⟨11775066760540744518893867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850044507027163012595911 11775066760540744518893867)
              ·
                refine ⟨17662600140811116778340801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775066760540744518893867 17662600140811116778340801)
                ·
                  refine ⟨13246950105608337583755601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17662600140811116778340801 13246950105608337583755601)
                  ·
                    refine ⟨9935212579206253187816701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13246950105608337583755601 9935212579206253187816701)
                    ·
                      refine ⟨3725704717202344945431263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935212579206253187816701 3725704717202344945431263)
                      ·
                        rfl

theorem cell23_7255784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7255784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255784 prefixEnd_7255784 := by exact prefixLift 7255784
  have htrace : WordTrace (prefixWord ++ tailWord_7255784) baseStart_7255784 baseEnd_7255784 := by
    simpa [prefixWord, tailWord_7255784, baseEnd_7255784] using wordTrace_append hprefix tailTrace_7255784
  have hstable : (prefixWord ++ tailWord_7255784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255784).length < 2 ^ (prefixWord ++ tailWord_7255784).sum := by decide
  have hdescent : baseEnd_7255784 < baseStart_7255784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255807 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 2, 3, 2]
def baseStart_7255807 : Nat := 118140960795 + 7255807 * 2 ^ 59
def prefixEnd_7255807 : Nat := 4983230072969 + 3 ^ 40 * 7255807 * 2
def baseEnd_7255807 : Nat := 3725716527257398355443657

theorem tailTrace_7255807 : CollatzResearch.WordTrace tailWord_7255807 prefixEnd_7255807 3725716527257398355443657 := by
  unfold tailWord_7255807
  simp only [CollatzResearch.WordTrace]
  refine ⟨264641022424457907023501675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176427348282971938015667783 264641022424457907023501675)
  ·
    refine ⟨396961533636686860535252513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264641022424457907023501675 396961533636686860535252513)
    ·
      refine ⟨297721150227515145401439385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396961533636686860535252513 297721150227515145401439385)
      ·
        refine ⟨223290862670636359051079539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297721150227515145401439385 223290862670636359051079539)
        ·
          refine ⟨334936294005954538576619309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223290862670636359051079539 334936294005954538576619309)
          ·
            refine ⟨125601110252232951966232241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334936294005954538576619309 125601110252232951966232241)
            ·
              refine ⟨94200832689174713974674181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125601110252232951966232241 94200832689174713974674181)
              ·
                refine ⟨17662656129220258870251409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94200832689174713974674181 17662656129220258870251409)
                ·
                  refine ⟨13246992096915194152688557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17662656129220258870251409 13246992096915194152688557)
                  ·
                    refine ⟨4967622036343197807258209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13246992096915194152688557 4967622036343197807258209)
                    ·
                      refine ⟨3725716527257398355443657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967622036343197807258209 3725716527257398355443657)
                      ·
                        rfl

theorem cell23_7255807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_7255807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255807 prefixEnd_7255807 := by exact prefixLift 7255807
  have htrace : WordTrace (prefixWord ++ tailWord_7255807) baseStart_7255807 baseEnd_7255807 := by
    simpa [prefixWord, tailWord_7255807, baseEnd_7255807] using wordTrace_append hprefix tailTrace_7255807
  have hstable : (prefixWord ++ tailWord_7255807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255807).length < 2 ^ (prefixWord ++ tailWord_7255807).sum := by decide
  have hdescent : baseEnd_7255807 < baseStart_7255807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255813 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_7255813 : Nat := 118140960795 + 7255813 * 2 ^ 59
def prefixEnd_7255813 : Nat := 4983230072969 + 3 ^ 40 * 7255813 * 2
def baseEnd_7255813 : Nat := 1241906536047108443989543

theorem tailTrace_7255813 : CollatzResearch.WordTrace tailWord_7255813 prefixEnd_7255813 1241906536047108443989543 := by
  unfold tailWord_7255813
  simp only [CollatzResearch.WordTrace]
  refine ⟨264641241262436170048220093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176427494174957446698813395 264641241262436170048220093)
  ·
    refine ⟨99240465473413563768082535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264641241262436170048220093 99240465473413563768082535)
    ·
      refine ⟨148860698210120345652123803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99240465473413563768082535 148860698210120345652123803)
      ·
        refine ⟨223291047315180518478185705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148860698210120345652123803 223291047315180518478185705)
        ·
          refine ⟨167468285486385388858639279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223291047315180518478185705 167468285486385388858639279)
          ·
            refine ⟨251202428229578083287958919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167468285486385388858639279 251202428229578083287958919)
            ·
              refine ⟨376803642344367124931938379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251202428229578083287958919 376803642344367124931938379)
              ·
                refine ⟨565205463516550687397907569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376803642344367124931938379 565205463516550687397907569)
                ·
                  refine ⟨423904097637413015548430677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565205463516550687397907569 423904097637413015548430677)
                  ·
                    refine ⟨1241906536047108443989543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 423904097637413015548430677 1241906536047108443989543)
                    ·
                      rfl

theorem cell23_7255813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_7255813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255813 prefixEnd_7255813 := by exact prefixLift 7255813
  have htrace : WordTrace (prefixWord ++ tailWord_7255813) baseStart_7255813 baseEnd_7255813 := by
    simpa [prefixWord, tailWord_7255813, baseEnd_7255813] using wordTrace_append hprefix tailTrace_7255813
  have hstable : (prefixWord ++ tailWord_7255813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255813).length < 2 ^ (prefixWord ++ tailWord_7255813).sum := by decide
  have hdescent : baseEnd_7255813 < baseStart_7255813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255820 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7255820 : Nat := 118140960795 + 7255820 * 2 ^ 59
def prefixEnd_7255820 : Nat := 4983230072969 + 3 ^ 40 * 7255820 * 2
def baseEnd_7255820 : Nat := 3725723202505906804581097

theorem tailTrace_7255820 : CollatzResearch.WordTrace tailWord_7255820 prefixEnd_7255820 3725723202505906804581097 := by
  unfold tailWord_7255820
  simp only [CollatzResearch.WordTrace]
  refine ⟨132320748286705405121862457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176427664382273873495816609 132320748286705405121862457)
  ·
    refine ⟨99240561215029053841396843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132320748286705405121862457 99240561215029053841396843)
    ·
      refine ⟨148860841822543580762095265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99240561215029053841396843 148860841822543580762095265)
      ·
        refine ⟨111645631366907685571571449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148860841822543580762095265 111645631366907685571571449)
        ·
          refine ⟨83734223525180764178678587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111645631366907685571571449 83734223525180764178678587)
          ·
            refine ⟨125601335287771146268017881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83734223525180764178678587 125601335287771146268017881)
            ·
              refine ⟨94201001465828359701013411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125601335287771146268017881 94201001465828359701013411)
              ·
                refine ⟨141301502198742539551520117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94201001465828359701013411 141301502198742539551520117)
                ·
                  refine ⟨13247015831132113082955011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141301502198742539551520117 13247015831132113082955011)
                  ·
                    refine ⟨19870523746698169624432517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13247015831132113082955011 19870523746698169624432517)
                    ·
                      refine ⟨3725723202505906804581097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19870523746698169624432517 3725723202505906804581097)
                      ·
                        rfl

theorem cell23_7255820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7255820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255820 prefixEnd_7255820 := by exact prefixLift 7255820
  have htrace : WordTrace (prefixWord ++ tailWord_7255820) baseStart_7255820 baseEnd_7255820 := by
    simpa [prefixWord, tailWord_7255820, baseEnd_7255820] using wordTrace_append hprefix tailTrace_7255820
  have hstable : (prefixWord ++ tailWord_7255820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255820).length < 2 ^ (prefixWord ++ tailWord_7255820).sum := by decide
  have hdescent : baseEnd_7255820 < baseStart_7255820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255840 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7255840 : Nat := 118140960795 + 7255840 * 2 ^ 59
def prefixEnd_7255840 : Nat := 4983230072969 + 3 ^ 40 * 7255840 * 2
def baseEnd_7255840 : Nat := 3725733472118996726331005

theorem tailTrace_7255840 : CollatzResearch.WordTrace tailWord_7255840 prefixEnd_7255840 3725733472118996726331005 := by
  unfold tailWord_7255840
  simp only [CollatzResearch.WordTrace]
  refine ⟨132321113016669176829726487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176428150688892235772968649 132321113016669176829726487)
  ·
    refine ⟨198481669525003765244589731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132321113016669176829726487 198481669525003765244589731)
    ·
      refine ⟨297722504287505647866884597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198481669525003765244589731 297722504287505647866884597)
      ·
        refine ⟨27911484776953654487520431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297722504287505647866884597 27911484776953654487520431)
        ·
          refine ⟨41867227165430481731280647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27911484776953654487520431 41867227165430481731280647)
          ·
            refine ⟨62800840748145722596920971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41867227165430481731280647 62800840748145722596920971)
            ·
              refine ⟨94201261122218583895381457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62800840748145722596920971 94201261122218583895381457)
              ·
                refine ⟨70650945841663937921536093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94201261122218583895381457 70650945841663937921536093)
                ·
                  refine ⟨26494104690623976720576035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70650945841663937921536093 26494104690623976720576035)
                  ·
                    refine ⟨39741157035935965080864053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26494104690623976720576035 39741157035935965080864053)
                    ·
                      refine ⟨3725733472118996726331005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39741157035935965080864053 3725733472118996726331005)
                      ·
                        rfl

theorem cell23_7255840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7255840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255840 prefixEnd_7255840 := by exact prefixLift 7255840
  have htrace : WordTrace (prefixWord ++ tailWord_7255840) baseStart_7255840 baseEnd_7255840 := by
    simpa [prefixWord, tailWord_7255840, baseEnd_7255840] using wordTrace_append hprefix tailTrace_7255840
  have hstable : (prefixWord ++ tailWord_7255840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255840).length < 2 ^ (prefixWord ++ tailWord_7255840).sum := by decide
  have hdescent : baseEnd_7255840 < baseStart_7255840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255848 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7255848 : Nat := 118140960795 + 7255848 * 2 ^ 59
def prefixEnd_7255848 : Nat := 4983230072969 + 3 ^ 40 * 7255848 * 2
def baseEnd_7255848 : Nat := 3725737579964232695030969

theorem tailTrace_7255848 : CollatzResearch.WordTrace tailWord_7255848 prefixEnd_7255848 3725737579964232695030969 := by
  unfold tailWord_7255848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132321258908654685512872099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176428345211539580683829465 132321258908654685512872099)
  ·
    refine ⟨198481888362982028269308149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132321258908654685512872099 198481888362982028269308149)
    ·
      refine ⟨18607677034029565150247639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198481888362982028269308149 18607677034029565150247639)
      ·
        refine ⟨27911515551044347725371459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18607677034029565150247639 27911515551044347725371459)
        ·
          refine ⟨41867273326566521588057189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27911515551044347725371459 41867273326566521588057189)
          ·
            refine ⟨7850113748731222797760723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41867273326566521588057189 7850113748731222797760723)
            ·
              refine ⟨11775170623096834196641085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850113748731222797760723 11775170623096834196641085)
              ·
                refine ⟨4415688983661312823740407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11775170623096834196641085 4415688983661312823740407)
                ·
                  refine ⟨6623533475491969235610611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415688983661312823740407 6623533475491969235610611)
                  ·
                    refine ⟨9935300213237953853415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623533475491969235610611 9935300213237953853415917)
                    ·
                      refine ⟨3725737579964232695030969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935300213237953853415917 3725737579964232695030969)
                      ·
                        rfl

theorem cell23_7255848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7255848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255848 prefixEnd_7255848 := by exact prefixLift 7255848
  have htrace : WordTrace (prefixWord ++ tailWord_7255848) baseStart_7255848 baseEnd_7255848 := by
    simpa [prefixWord, tailWord_7255848, baseEnd_7255848] using wordTrace_append hprefix tailTrace_7255848
  have hstable : (prefixWord ++ tailWord_7255848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255848).length < 2 ^ (prefixWord ++ tailWord_7255848).sum := by decide
  have hdescent : baseEnd_7255848 < baseStart_7255848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255857 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_7255857 : Nat := 118140960795 + 7255857 * 2 ^ 59
def prefixEnd_7255857 : Nat := 4983230072969 + 3 ^ 40 * 7255857 * 2
def baseEnd_7255857 : Nat := 3725742201290123159818427

theorem tailTrace_7255857 : CollatzResearch.WordTrace tailWord_7255857 prefixEnd_7255857 3725742201290123159818427 := by
  unfold tailWord_7255857
  simp only [CollatzResearch.WordTrace]
  refine ⟨264642846074276765562821825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176428564049517843708547883 264642846074276765562821825)
  ·
    refine ⟨198482134555707574172116369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264642846074276765562821825 198482134555707574172116369)
    ·
      refine ⟨148861600916780680629087277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198482134555707574172116369 148861600916780680629087277)
      ·
        refine ⟨55823100343792755235907729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148861600916780680629087277 55823100343792755235907729)
        ·
          refine ⟨41867325257844566426930797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55823100343792755235907729 41867325257844566426930797)
          ·
            refine ⟨15700246971691712410099049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41867325257844566426930797 15700246971691712410099049)
            ·
              refine ⟨11775185228768784307574287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15700246971691712410099049 11775185228768784307574287)
              ·
                refine ⟨17662777843153176461361431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775185228768784307574287 17662777843153176461361431)
                ·
                  refine ⟨26494166764729764692042147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17662777843153176461361431 26494166764729764692042147)
                  ·
                    refine ⟨39741250147094647038063221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26494166764729764692042147 39741250147094647038063221)
                    ·
                      refine ⟨3725742201290123159818427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39741250147094647038063221 3725742201290123159818427)
                      ·
                        rfl

theorem cell23_7255857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_7255857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255857 prefixEnd_7255857 := by exact prefixLift 7255857
  have htrace : WordTrace (prefixWord ++ tailWord_7255857) baseStart_7255857 baseEnd_7255857 := by
    simpa [prefixWord, tailWord_7255857, baseEnd_7255857] using wordTrace_append hprefix tailTrace_7255857
  have hstable : (prefixWord ++ tailWord_7255857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255857).length < 2 ^ (prefixWord ++ tailWord_7255857).sum := by decide
  have hdescent : baseEnd_7255857 < baseStart_7255857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255865 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7255865 : Nat := 118140960795 + 7255865 * 2 ^ 59
def prefixEnd_7255865 : Nat := 4983230072969 + 3 ^ 40 * 7255865 * 2
def baseEnd_7255865 : Nat := 3725746309135359128518391

theorem tailTrace_7255865 : CollatzResearch.WordTrace tailWord_7255865 prefixEnd_7255865 3725746309135359128518391 := by
  unfold tailWord_7255865
  simp only [CollatzResearch.WordTrace]
  refine ⟨264643137858247782929113049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176428758572165188619408699 264643137858247782929113049)
  ·
    refine ⟨198482353393685837196834787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264643137858247782929113049 198482353393685837196834787)
    ·
      refine ⟨297723530090528755795252181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198482353393685837196834787 297723530090528755795252181)
      ·
        refine ⟨6977895236496767713951223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 297723530090528755795252181 6977895236496767713951223)
        ·
          refine ⟨10466842854745151570926835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977895236496767713951223 10466842854745151570926835)
          ·
            refine ⟨15700264282117727356390253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10466842854745151570926835 15700264282117727356390253)
            ·
              refine ⟨5887599105794147758646345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15700264282117727356390253 5887599105794147758646345)
              ·
                refine ⟨4415699329345610818984759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887599105794147758646345 4415699329345610818984759)
                ·
                  refine ⟨6623548994018416228477139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415699329345610818984759 6623548994018416228477139)
                  ·
                    refine ⟨9935323491027624342715709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623548994018416228477139 9935323491027624342715709)
                    ·
                      refine ⟨3725746309135359128518391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935323491027624342715709 3725746309135359128518391)
                      ·
                        rfl

theorem cell23_7255865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7255865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255865 prefixEnd_7255865 := by exact prefixLift 7255865
  have htrace : WordTrace (prefixWord ++ tailWord_7255865) baseStart_7255865 baseEnd_7255865 := by
    simpa [prefixWord, tailWord_7255865, baseEnd_7255865] using wordTrace_append hprefix tailTrace_7255865
  have hstable : (prefixWord ++ tailWord_7255865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255865).length < 2 ^ (prefixWord ++ tailWord_7255865).sum := by decide
  have hdescent : baseEnd_7255865 < baseStart_7255865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255920 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_7255920 : Nat := 118140960795 + 7255920 * 2 ^ 59
def prefixEnd_7255920 : Nat := 4983230072969 + 3 ^ 40 * 7255920 * 2
def baseEnd_7255920 : Nat := 1241924850190452137776879

theorem tailTrace_7255920 : CollatzResearch.WordTrace tailWord_7255920 prefixEnd_7255920 1241924850190452137776879 := by
  unfold tailWord_7255920
  simp only [CollatzResearch.WordTrace]
  refine ⟨132322571936524263661182607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176430095915365684881576809 132322571936524263661182607)
  ·
    refine ⟨198483857904786395491773911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132322571936524263661182607 198483857904786395491773911)
    ·
      refine ⟨297725786857179593237660867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198483857904786395491773911 297725786857179593237660867)
      ·
        refine ⟨446588680285769389856491301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297725786857179593237660867 446588680285769389856491301)
        ·
          refine ⟨83735377553581760598092119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446588680285769389856491301 83735377553581760598092119)
          ·
            refine ⟨125603066330372640897138179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83735377553581760598092119 125603066330372640897138179)
            ·
              refine ⟨188404599495558961345707269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125603066330372640897138179 188404599495558961345707269)
              ·
                refine ⟨35325862405417305252320113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188404599495558961345707269 35325862405417305252320113)
                ·
                  refine ⟨26494396804062978939240085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35325862405417305252320113 26494396804062978939240085)
                  ·
                    refine ⟨1241924850190452137776879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26494396804062978939240085 1241924850190452137776879)
                    ·
                      rfl

theorem cell23_7255920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_7255920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255920 prefixEnd_7255920 := by exact prefixLift 7255920
  have htrace : WordTrace (prefixWord ++ tailWord_7255920) baseStart_7255920 baseEnd_7255920 := by
    simpa [prefixWord, tailWord_7255920, baseEnd_7255920] using wordTrace_append hprefix tailTrace_7255920
  have hstable : (prefixWord ++ tailWord_7255920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255920).length < 2 ^ (prefixWord ++ tailWord_7255920).sum := by decide
  have hdescent : baseEnd_7255920 < baseStart_7255920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255930 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_7255930 : Nat := 118140960795 + 7255930 * 2 ^ 59
def prefixEnd_7255930 : Nat := 4983230072969 + 3 ^ 40 * 7255930 * 2
def baseEnd_7255930 : Nat := 3725779685377901374205591

theorem tailTrace_7255930 : CollatzResearch.WordTrace tailWord_7255930 prefixEnd_7255930 3725779685377901374205591 := by
  unfold tailWord_7255930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66161377150753074757557311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176430339068674866020152829 66161377150753074757557311)
  ·
    refine ⟨99242065726129612136335967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66161377150753074757557311 99242065726129612136335967)
    ·
      refine ⟨148863098589194418204503951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99242065726129612136335967 148863098589194418204503951)
      ·
        refine ⟨223294647883791627306755927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148863098589194418204503951 223294647883791627306755927)
        ·
          refine ⟨334941971825687440960133891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223294647883791627306755927 334941971825687440960133891)
          ·
            refine ⟨502412957738531161440200837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334941971825687440960133891 502412957738531161440200837)
            ·
              refine ⟨94202429575974592770037657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502412957738531161440200837 94202429575974592770037657)
              ·
                refine ⟨70651822181980944577528243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94202429575974592770037657 70651822181980944577528243)
                ·
                  refine ⟨105977733272971416866292365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70651822181980944577528243 105977733272971416866292365)
                  ·
                    refine ⟨39741649977364281324859637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105977733272971416866292365 39741649977364281324859637)
                    ·
                      refine ⟨3725779685377901374205591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39741649977364281324859637 3725779685377901374205591)
                      ·
                        rfl

theorem cell23_7255930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_7255930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255930 prefixEnd_7255930 := by exact prefixLift 7255930
  have htrace : WordTrace (prefixWord ++ tailWord_7255930) baseStart_7255930 baseEnd_7255930 := by
    simpa [prefixWord, tailWord_7255930, baseEnd_7255930] using wordTrace_append hprefix tailTrace_7255930
  have hstable : (prefixWord ++ tailWord_7255930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255930).length < 2 ^ (prefixWord ++ tailWord_7255930).sum := by decide
  have hdescent : baseEnd_7255930 < baseStart_7255930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255980 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_7255980 : Nat := 118140960795 + 7255980 * 2 ^ 59
def prefixEnd_7255980 : Nat := 4983230072969 + 3 ^ 40 * 7255980 * 2
def baseEnd_7255980 : Nat := 1241935119803542059526787

theorem tailTrace_7255980 : CollatzResearch.WordTrace tailWord_7255980 prefixEnd_7255980 1241935119803542059526787 := by
  unfold tailWord_7255980
  simp only [CollatzResearch.WordTrace]
  refine ⟨132323666126415578784774697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176431554835220771713032929 132323666126415578784774697)
  ·
    refine ⟨99242749594811684088581023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132323666126415578784774697 99242749594811684088581023)
    ·
      refine ⟨148864124392217526132871535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99242749594811684088581023 148864124392217526132871535)
      ·
        refine ⟨223296186588326289199307303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148864124392217526132871535 223296186588326289199307303)
        ·
          refine ⟨334944279882489433798960955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223296186588326289199307303 334944279882489433798960955)
          ·
            refine ⟨502416419823734150698441433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334944279882489433798960955 502416419823734150698441433)
            ·
              refine ⟨376812314867800613023831075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502416419823734150698441433 376812314867800613023831075)
              ·
                refine ⟨565218472301700919535746613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376812314867800613023831075 565218472301700919535746613)
                ·
                  refine ⟨52989231778284461206476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 565218472301700919535746613 52989231778284461206476245)
                  ·
                    refine ⟨1241935119803542059526787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52989231778284461206476245 1241935119803542059526787)
                    ·
                      rfl

theorem cell23_7255980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_7255980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255980 prefixEnd_7255980 := by exact prefixLift 7255980
  have htrace : WordTrace (prefixWord ++ tailWord_7255980) baseStart_7255980 baseEnd_7255980 := by
    simpa [prefixWord, tailWord_7255980, baseEnd_7255980] using wordTrace_append hprefix tailTrace_7255980
  have hstable : (prefixWord ++ tailWord_7255980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255980).length < 2 ^ (prefixWord ++ tailWord_7255980).sum := by decide
  have hdescent : baseEnd_7255980 < baseStart_7255980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7255997 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_7255997 : Nat := 118140960795 + 7255997 * 2 ^ 59
def prefixEnd_7255997 : Nat := 4983230072969 + 3 ^ 40 * 7255997 * 2
def baseEnd_7255997 : Nat := 1241938029527250870689261

theorem tailTrace_7255997 : CollatzResearch.WordTrace tailWord_7255997 prefixEnd_7255997 1241938029527250870689261 := by
  unfold tailWord_7255997
  simp only [CollatzResearch.WordTrace]
  refine ⟨264647952293769569472918245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176431968195846379648612163 264647952293769569472918245)
  ·
    refine ⟨49621491055081794276172171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264647952293769569472918245 49621491055081794276172171)
    ·
      refine ⟨74432236582622691414258257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49621491055081794276172171 74432236582622691414258257)
      ·
        refine ⟨55824177436967018560693693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74432236582622691414258257 55824177436967018560693693)
        ·
          refine ⟨20934066538862631960260135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55824177436967018560693693 20934066538862631960260135)
          ·
            refine ⟨31401099808293947940390203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20934066538862631960260135 31401099808293947940390203)
            ·
              refine ⟨47101649712440921910585305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31401099808293947940390203 47101649712440921910585305)
              ·
                refine ⟨35326237284330691432938979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47101649712440921910585305 35326237284330691432938979)
                ·
                  refine ⟨52989355926496037149408469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35326237284330691432938979 52989355926496037149408469)
                  ·
                    refine ⟨1241938029527250870689261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52989355926496037149408469 1241938029527250870689261)
                    ·
                      rfl

theorem cell23_7255997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_7255997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7255997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7255997 prefixEnd_7255997 := by exact prefixLift 7255997
  have htrace : WordTrace (prefixWord ++ tailWord_7255997) baseStart_7255997 baseEnd_7255997 := by
    simpa [prefixWord, tailWord_7255997, baseEnd_7255997] using wordTrace_append hprefix tailTrace_7255997
  have hstable : (prefixWord ++ tailWord_7255997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7255997).length < 2 ^ (prefixWord ++ tailWord_7255997).sum := by decide
  have hdescent : baseEnd_7255997 < baseStart_7255997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7255997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256018 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_7256018 : Nat := 118140960795 + 7256018 * 2 ^ 59
def prefixEnd_7256018 : Nat := 4983230072969 + 3 ^ 40 * 7256018 * 2
def baseEnd_7256018 : Nat := 413980541297277447767243

theorem tailTrace_7256018 : CollatzResearch.WordTrace tailWord_7256018 prefixEnd_7256018 413980541297277447767243 := by
  unfold tailWord_7256018
  simp only [CollatzResearch.WordTrace]
  refine ⟨66162179556673372514858177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176432478817795660039621805 66162179556673372514858177)
  ·
    refine ⟨49621634667505029386143633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66162179556673372514858177 49621634667505029386143633)
    ·
      refine ⟨37216226000628772039607725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49621634667505029386143633 37216226000628772039607725)
      ·
        refine ⟨13956084750235789514852897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37216226000628772039607725 13956084750235789514852897)
        ·
          refine ⟨10467063562676842136139673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13956084750235789514852897 10467063562676842136139673)
          ·
            refine ⟨7850297672007631602104755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10467063562676842136139673 7850297672007631602104755)
            ·
              refine ⟨11775446508011447403157133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850297672007631602104755 11775446508011447403157133)
              ·
                refine ⟨4415792440504292776183925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11775446508011447403157133 4415792440504292776183925)
                ·
                  refine ⟨413980541297277447767243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4415792440504292776183925 413980541297277447767243)
                  ·
                    rfl

theorem cell23_7256018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_7256018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256018 prefixEnd_7256018 := by exact prefixLift 7256018
  have htrace : WordTrace (prefixWord ++ tailWord_7256018) baseStart_7256018 baseEnd_7256018 := by
    simpa [prefixWord, tailWord_7256018, baseEnd_7256018] using wordTrace_append hprefix tailTrace_7256018
  have hstable : (prefixWord ++ tailWord_7256018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256018).length < 2 ^ (prefixWord ++ tailWord_7256018).sum := by decide
  have hdescent : baseEnd_7256018 < baseStart_7256018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256067 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3]
def baseStart_7256067 : Nat := 118140960795 + 7256067 * 2 ^ 59
def prefixEnd_7256067 : Nat := 4983230072969 + 3 ^ 40 * 7256067 * 2
def baseEnd_7256067 : Nat := 3725850032227567338192461

theorem tailTrace_7256067 : CollatzResearch.WordTrace tailWord_7256067 prefixEnd_7256067 3725850032227567338192461 := by
  unfold tailWord_7256067
  simp only [CollatzResearch.WordTrace]
  refine ⟨264650505403515971427966455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176433670269010647618644303 264650505403515971427966455)
  ·
    refine ⟨396975758105273957141949683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264650505403515971427966455 396975758105273957141949683)
    ·
      refine ⟨595463637157910935712924525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396975758105273957141949683 595463637157910935712924525)
      ·
        refine ⟨223298863934216600892346697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595463637157910935712924525 223298863934216600892346697)
        ·
          refine ⟨167474147950662450669260023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223298863934216600892346697 167474147950662450669260023)
          ·
            refine ⟨251211221925993676003890035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167474147950662450669260023 251211221925993676003890035)
            ·
              refine ⟨376816832888990514005835053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251211221925993676003890035 376816832888990514005835053)
              ·
                refine ⟨141306312333371442752188145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376816832888990514005835053 141306312333371442752188145)
                ·
                  refine ⟨105979734250028582064141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141306312333371442752188145 105979734250028582064141109)
                  ·
                    refine ⟨9935600085940179568513229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105979734250028582064141109 9935600085940179568513229)
                    ·
                      refine ⟨3725850032227567338192461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935600085940179568513229 3725850032227567338192461)
                      ·
                        rfl

theorem cell23_7256067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_7256067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256067 prefixEnd_7256067 := by exact prefixLift 7256067
  have htrace : WordTrace (prefixWord ++ tailWord_7256067) baseStart_7256067 baseEnd_7256067 := by
    simpa [prefixWord, tailWord_7256067, baseEnd_7256067] using wordTrace_append hprefix tailTrace_7256067
  have hstable : (prefixWord ++ tailWord_7256067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256067).length < 2 ^ (prefixWord ++ tailWord_7256067).sum := by decide
  have hdescent : baseEnd_7256067 < baseStart_7256067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256068 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7256068 : Nat := 118140960795 + 7256068 * 2 ^ 59
def prefixEnd_7256068 : Nat := 4983230072969 + 3 ^ 40 * 7256068 * 2
def baseEnd_7256068 : Nat := 3725850545708221834279957

theorem tailTrace_7256068 : CollatzResearch.WordTrace tailWord_7256068 prefixEnd_7256068 3725850545708221834279957 := by
  unfold tailWord_7256068
  simp only [CollatzResearch.WordTrace]
  refine ⟨132325270938256174299376429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176433694584341565732501905 132325270938256174299376429)
  ·
    refine ⟨49621976601846065362266161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132325270938256174299376429 49621976601846065362266161)
    ·
      refine ⟨37216482451384549021699621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49621976601846065362266161 37216482451384549021699621)
      ·
        refine ⟨6978090459634602941568679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37216482451384549021699621 6978090459634602941568679)
        ·
          refine ⟨10467135689451904412353019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978090459634602941568679 10467135689451904412353019)
          ·
            refine ⟨15700703534177856618529529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467135689451904412353019 15700703534177856618529529)
            ·
              refine ⟨11775527650633392463897147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15700703534177856618529529 11775527650633392463897147)
              ·
                refine ⟨17663291475950088695845721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775527650633392463897147 17663291475950088695845721)
                ·
                  refine ⟨13247468606962566521884291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17663291475950088695845721 13247468606962566521884291)
                  ·
                    refine ⟨19871202910443849782826437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13247468606962566521884291 19871202910443849782826437)
                    ·
                      refine ⟨3725850545708221834279957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19871202910443849782826437 3725850545708221834279957)
                      ·
                        rfl

theorem cell23_7256068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7256068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256068 prefixEnd_7256068 := by exact prefixLift 7256068
  have htrace : WordTrace (prefixWord ++ tailWord_7256068) baseStart_7256068 baseEnd_7256068 := by
    simpa [prefixWord, tailWord_7256068, baseEnd_7256068] using wordTrace_append hprefix tailTrace_7256068
  have hstable : (prefixWord ++ tailWord_7256068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256068).length < 2 ^ (prefixWord ++ tailWord_7256068).sum := by decide
  have hdescent : baseEnd_7256068 < baseStart_7256068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256071 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7256071 : Nat := 118140960795 + 7256071 * 2 ^ 59
def prefixEnd_7256071 : Nat := 4983230072969 + 3 ^ 40 * 7256071 * 2
def baseEnd_7256071 : Nat := 3725852086150185322542443

theorem tailTrace_7256071 : CollatzResearch.WordTrace tailWord_7256071 prefixEnd_7256071 3725852086150185322542443 := by
  unfold tailWord_7256071
  simp only [CollatzResearch.WordTrace]
  refine ⟨264650651295501480111112067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176433767530334320074074711 264650651295501480111112067)
  ·
    refine ⟨396975976943252220166668101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264650651295501480111112067 396975976943252220166668101)
    ·
      refine ⟨74432995676859791281250269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396975976943252220166668101 74432995676859791281250269)
      ·
        refine ⟨27912373378822421730468851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74432995676859791281250269 27912373378822421730468851)
        ·
          refine ⟨41868560068233632595703277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27912373378822421730468851 41868560068233632595703277)
          ·
            refine ⟨15700710025587612223388729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41868560068233632595703277 15700710025587612223388729)
            ·
              refine ⟨11775532519190709167541547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15700710025587612223388729 11775532519190709167541547)
              ·
                refine ⟨17663298778786063751312321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775532519190709167541547 17663298778786063751312321)
                ·
                  refine ⟨13247474084089547813484241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17663298778786063751312321 13247474084089547813484241)
                  ·
                    refine ⟨9935605563067160860113181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13247474084089547813484241 9935605563067160860113181)
                    ·
                      refine ⟨3725852086150185322542443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935605563067160860113181 3725852086150185322542443)
                      ·
                        rfl

theorem cell23_7256071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7256071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256071 prefixEnd_7256071 := by exact prefixLift 7256071
  have htrace : WordTrace (prefixWord ++ tailWord_7256071) baseStart_7256071 baseEnd_7256071 := by
    simpa [prefixWord, tailWord_7256071, baseEnd_7256071] using wordTrace_append hprefix tailTrace_7256071
  have hstable : (prefixWord ++ tailWord_7256071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256071).length < 2 ^ (prefixWord ++ tailWord_7256071).sum := by decide
  have hdescent : baseEnd_7256071 < baseStart_7256071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256118 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7256118 : Nat := 118140960795 + 7256118 * 2 ^ 59
def prefixEnd_7256118 : Nat := 4983230072969 + 3 ^ 40 * 7256118 * 2
def baseEnd_7256118 : Nat := 3725876219740946638654727

theorem tailTrace_7256118 : CollatzResearch.WordTrace tailWord_7256118 prefixEnd_7256118 3725876219740946638654727 := by
  unfold tailWord_7256118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540772845395700446129563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176434910350887471425382005 16540772845395700446129563)
  ·
    refine ⟨24811159268093550669194345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16540772845395700446129563 24811159268093550669194345)
    ·
      refine ⟨18608369451070163001895759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24811159268093550669194345 18608369451070163001895759)
      ·
        refine ⟨27912554176605244502843639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18608369451070163001895759 27912554176605244502843639)
        ·
          refine ⟨41868831264907866754265459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27912554176605244502843639 41868831264907866754265459)
          ·
            refine ⟨62803246897361800131398189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41868831264907866754265459 62803246897361800131398189)
            ·
              refine ⟨23551217586510675049274321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62803246897361800131398189 23551217586510675049274321)
              ·
                refine ⟨17663413189883006286955741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23551217586510675049274321 17663413189883006286955741)
                ·
                  refine ⟨6623779946206127357608403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17663413189883006286955741 6623779946206127357608403)
                  ·
                    refine ⟨9935669919309191036412605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623779946206127357608403 9935669919309191036412605)
                    ·
                      refine ⟨3725876219740946638654727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935669919309191036412605 3725876219740946638654727)
                      ·
                        rfl

theorem cell23_7256118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7256118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256118 prefixEnd_7256118 := by exact prefixLift 7256118
  have htrace : WordTrace (prefixWord ++ tailWord_7256118) baseStart_7256118 baseEnd_7256118 := by
    simpa [prefixWord, tailWord_7256118, baseEnd_7256118] using wordTrace_append hprefix tailTrace_7256118
  have hstable : (prefixWord ++ tailWord_7256118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256118).length < 2 ^ (prefixWord ++ tailWord_7256118).sum := by decide
  have hdescent : baseEnd_7256118 < baseStart_7256118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256124 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7256124 : Nat := 118140960795 + 7256124 * 2 ^ 59
def prefixEnd_7256124 : Nat := 4983230072969 + 3 ^ 40 * 7256124 * 2
def baseEnd_7256124 : Nat := 3725879300624873615179699

theorem tailTrace_7256124 : CollatzResearch.WordTrace tailWord_7256124 prefixEnd_7256124 3725879300624873615179699 := by
  unfold tailWord_7256124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132326292182154735081395713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176435056242872980108527617 132326292182154735081395713)
  ·
    refine ⟨99244719136616051311046785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132326292182154735081395713 99244719136616051311046785)
    ·
      refine ⟨74433539352462038483285089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99244719136616051311046785 74433539352462038483285089)
      ·
        refine ⟨55825154514346528862463817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74433539352462038483285089 55825154514346528862463817)
        ·
          refine ⟨41868865885759896646847863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55825154514346528862463817 41868865885759896646847863)
          ·
            refine ⟨62803298828639844970271795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41868865885759896646847863 62803298828639844970271795)
            ·
              refine ⟨94204948242959767455407693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62803298828639844970271795 94204948242959767455407693)
              ·
                refine ⟨35326855591109912795777885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94204948242959767455407693 35326855591109912795777885)
                ·
                  refine ⟨13247570846666217298416707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35326855591109912795777885 13247570846666217298416707)
                  ·
                    refine ⟨19871356269999325947625061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13247570846666217298416707 19871356269999325947625061)
                    ·
                      refine ⟨3725879300624873615179699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19871356269999325947625061 3725879300624873615179699)
                      ·
                        rfl

theorem cell23_7256124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7256124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256124 prefixEnd_7256124 := by exact prefixLift 7256124
  have htrace : WordTrace (prefixWord ++ tailWord_7256124) baseStart_7256124 baseEnd_7256124 := by
    simpa [prefixWord, tailWord_7256124, baseEnd_7256124] using wordTrace_append hprefix tailTrace_7256124
  have hstable : (prefixWord ++ tailWord_7256124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256124).length < 2 ^ (prefixWord ++ tailWord_7256124).sum := by decide
  have hdescent : baseEnd_7256124 < baseStart_7256124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256128 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2]
def baseStart_7256128 : Nat := 118140960795 + 7256128 * 2 ^ 59
def prefixEnd_7256128 : Nat := 4983230072969 + 3 ^ 40 * 7256128 * 2
def baseEnd_7256128 : Nat := 3725881354547491599529681

theorem tailTrace_7256128 : CollatzResearch.WordTrace tailWord_7256128 prefixEnd_7256128 3725881354547491599529681 := by
  unfold tailWord_7256128
  simp only [CollatzResearch.WordTrace]
  refine ⟨132326365128147489422968519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176435153504196652563958025 132326365128147489422968519)
  ·
    refine ⟨198489547692221234134452779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132326365128147489422968519 198489547692221234134452779)
    ·
      refine ⟨297734321538331851201679169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198489547692221234134452779 297734321538331851201679169)
      ·
        refine ⟨223300741153748888401259377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297734321538331851201679169 223300741153748888401259377)
        ·
          refine ⟨167475555865311666300944533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223300741153748888401259377 167475555865311666300944533)
          ·
            refine ⟨7850416681186484357856775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167475555865311666300944533 7850416681186484357856775)
            ·
              refine ⟨11775625021779726536785163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850416681186484357856775 11775625021779726536785163)
              ·
                refine ⟨17663437532669589805177745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775625021779726536785163 17663437532669589805177745)
                ·
                  refine ⟨13247578149502192353883309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17663437532669589805177745 13247578149502192353883309)
                  ·
                    refine ⟨4967841806063322132706241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13247578149502192353883309 4967841806063322132706241)
                    ·
                      refine ⟨3725881354547491599529681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967841806063322132706241 3725881354547491599529681)
                      ·
                        rfl

theorem cell23_7256128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_7256128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256128 prefixEnd_7256128 := by exact prefixLift 7256128
  have htrace : WordTrace (prefixWord ++ tailWord_7256128) baseStart_7256128 baseEnd_7256128 := by
    simpa [prefixWord, tailWord_7256128, baseEnd_7256128] using wordTrace_append hprefix tailTrace_7256128
  have hstable : (prefixWord ++ tailWord_7256128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256128).length < 2 ^ (prefixWord ++ tailWord_7256128).sum := by decide
  have hdescent : baseEnd_7256128 < baseStart_7256128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256151 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 2, 4]
def baseStart_7256151 : Nat := 118140960795 + 7256151 * 2 ^ 59
def prefixEnd_7256151 : Nat := 4983230072969 + 3 ^ 40 * 7256151 * 2
def baseEnd_7256151 : Nat := 1241964388200848336514025

theorem tailTrace_7256151 : CollatzResearch.WordTrace tailWord_7256151 prefixEnd_7256151 1241964388200848336514025 := by
  unfold tailWord_7256151
  simp only [CollatzResearch.WordTrace]
  refine ⟨264653569135211653774024307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176435712756807769182682871 264653569135211653774024307)
  ·
    refine ⟨396980353702817480661036461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264653569135211653774024307 396980353702817480661036461)
    ·
      refine ⟨148867632638556555247888673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396980353702817480661036461 148867632638556555247888673)
      ·
        refine ⟨111650724478917416435916505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148867632638556555247888673 111650724478917416435916505)
        ·
          refine ⟨83738043359188062326937379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111650724478917416435916505 83738043359188062326937379)
          ·
            refine ⟨125607065038782093490406069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83738043359188062326937379 125607065038782093490406069)
            ·
              refine ⟨11775662347385821264725569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125607065038782093490406069 11775662347385821264725569)
              ·
                refine ⟨8831746760539365948544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11775662347385821264725569 8831746760539365948544177)
                ·
                  refine ⟨6623810070404524461408133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831746760539365948544177 6623810070404524461408133)
                  ·
                    refine ⟨1241964388200848336514025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6623810070404524461408133 1241964388200848336514025)
                    ·
                      rfl

theorem cell23_7256151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_7256151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256151 prefixEnd_7256151 := by exact prefixLift 7256151
  have htrace : WordTrace (prefixWord ++ tailWord_7256151) baseStart_7256151 baseEnd_7256151 := by
    simpa [prefixWord, tailWord_7256151, baseEnd_7256151] using wordTrace_append hprefix tailTrace_7256151
  have hstable : (prefixWord ++ tailWord_7256151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256151).length < 2 ^ (prefixWord ++ tailWord_7256151).sum := by decide
  have hdescent : baseEnd_7256151 < baseStart_7256151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256178 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7256178 : Nat := 118140960795 + 7256178 * 2 ^ 59
def prefixEnd_7256178 : Nat := 4983230072969 + 3 ^ 40 * 7256178 * 2
def baseEnd_7256178 : Nat := 3725907028580216403904451

theorem tailTrace_7256178 : CollatzResearch.WordTrace tailWord_7256178 prefixEnd_7256178 3725907028580216403904451 := by
  unfold tailWord_7256178
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163638476528459346314297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176436369270742558256838125 66163638476528459346314297)
  ·
    refine ⟨49622728857396344509735723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66163638476528459346314297 49622728857396344509735723)
    ·
      refine ⟨74434093286094516764603585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49622728857396344509735723 74434093286094516764603585)
      ·
        refine ⟨55825569964570887573452689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74434093286094516764603585 55825569964570887573452689)
        ·
          refine ⟨41869177473428165680089517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55825569964570887573452689 41869177473428165680089517)
          ·
            refine ⟨15700941552535562130033569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41869177473428165680089517 15700941552535562130033569)
            ·
              refine ⟨11775706164401671597525177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15700941552535562130033569 11775706164401671597525177)
              ·
                refine ⟨8831779623301253698143883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11775706164401671597525177 8831779623301253698143883)
                ·
                  refine ⟨13247669434951880547215825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8831779623301253698143883 13247669434951880547215825)
                  ·
                    refine ⟨9935752076213910410411869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13247669434951880547215825 9935752076213910410411869)
                    ·
                      refine ⟨3725907028580216403904451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935752076213910410411869 3725907028580216403904451)
                      ·
                        rfl

theorem cell23_7256178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7256178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256178 prefixEnd_7256178 := by exact prefixLift 7256178
  have htrace : WordTrace (prefixWord ++ tailWord_7256178) baseStart_7256178 baseEnd_7256178 := by
    simpa [prefixWord, tailWord_7256178, baseEnd_7256178] using wordTrace_append hprefix tailTrace_7256178
  have hstable : (prefixWord ++ tailWord_7256178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256178).length < 2 ^ (prefixWord ++ tailWord_7256178).sum := by decide
  have hdescent : baseEnd_7256178 < baseStart_7256178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256225 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7256225 : Nat := 118140960795 + 7256225 * 2 ^ 59
def prefixEnd_7256225 : Nat := 4983230072969 + 3 ^ 40 * 7256225 * 2
def baseEnd_7256225 : Nat := 3725931162170977720016735

theorem tailTrace_7256225 : CollatzResearch.WordTrace tailWord_7256225 prefixEnd_7256225 3725931162170977720016735 := by
  unfold tailWord_7256225
  simp only [CollatzResearch.WordTrace]
  refine ⟨264656268136943564412218129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176437512091295709608145419 264656268136943564412218129)
  ·
    refine ⟨198492201102707673309163597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264656268136943564412218129 198492201102707673309163597)
    ·
      refine ⟨74434575413515377490936349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198492201102707673309163597 74434575413515377490936349)
      ·
        refine ⟨27912965780068266559101131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74434575413515377490936349 27912965780068266559101131)
        ·
          refine ⟨41869448670102399838651697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27912965780068266559101131 41869448670102399838651697)
          ·
            refine ⟨31402086502576799878988773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41869448670102399838651697 31402086502576799878988773)
            ·
              refine ⟨5887891219233149977310395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31402086502576799878988773 5887891219233149977310395)
              ·
                refine ⟨8831836828849724965965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887891219233149977310395 8831836828849724965965593)
                ·
                  refine ⟨6623877621637293724474195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831836828849724965965593 6623877621637293724474195)
                  ·
                    refine ⟨9935816432455940586711293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623877621637293724474195 9935816432455940586711293)
                    ·
                      refine ⟨3725931162170977720016735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935816432455940586711293 3725931162170977720016735)
                      ·
                        rfl

theorem cell23_7256225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7256225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256225 prefixEnd_7256225 := by exact prefixLift 7256225
  have htrace : WordTrace (prefixWord ++ tailWord_7256225) baseStart_7256225 baseEnd_7256225 := by
    simpa [prefixWord, tailWord_7256225, baseEnd_7256225] using wordTrace_append hprefix tailTrace_7256225
  have hstable : (prefixWord ++ tailWord_7256225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256225).length < 2 ^ (prefixWord ++ tailWord_7256225).sum := by decide
  have hdescent : baseEnd_7256225 < baseStart_7256225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256252 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_7256252 : Nat := 118140960795 + 7256252 * 2 ^ 59
def prefixEnd_7256252 : Nat := 4983230072969 + 3 ^ 40 * 7256252 * 2
def baseEnd_7256252 : Nat := 3725945026148649114379111

theorem tailTrace_7256252 : CollatzResearch.WordTrace tailWord_7256252 prefixEnd_7256252 3725945026148649114379111 := by
  unfold tailWord_7256252
  simp only [CollatzResearch.WordTrace]
  refine ⟨132328626453922874011725505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176438168605230498682300673 132328626453922874011725505)
  ·
    refine ⟨99246469840442155508794129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132328626453922874011725505 99246469840442155508794129)
    ·
      refine ⟨74434852380331616631595597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99246469840442155508794129 74434852380331616631595597)
      ·
        refine ⟨27913069642624356236848349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74434852380331616631595597 27913069642624356236848349)
        ·
          refine ⟨10467401115984133588818131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27913069642624356236848349 10467401115984133588818131)
          ·
            refine ⟨15701101673976200383227197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467401115984133588818131 15701101673976200383227197)
            ·
              refine ⟨5887913127741075143710199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15701101673976200383227197 5887913127741075143710199)
              ·
                refine ⟨8831869691611612715565299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887913127741075143710199 8831869691611612715565299)
                ·
                  refine ⟨13247804537417419073347949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8831869691611612715565299 13247804537417419073347949)
                  ·
                    refine ⟨4967926701531532152505481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13247804537417419073347949 4967926701531532152505481)
                    ·
                      refine ⟨3725945026148649114379111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4967926701531532152505481 3725945026148649114379111)
                      ·
                        rfl

theorem cell23_7256252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_7256252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256252 prefixEnd_7256252 := by exact prefixLift 7256252
  have htrace : WordTrace (prefixWord ++ tailWord_7256252) baseStart_7256252 baseEnd_7256252 := by
    simpa [prefixWord, tailWord_7256252, baseEnd_7256252] using wordTrace_append hprefix tailTrace_7256252
  have hstable : (prefixWord ++ tailWord_7256252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256252).length < 2 ^ (prefixWord ++ tailWord_7256252).sum := by decide
  have hdescent : baseEnd_7256252 < baseStart_7256252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256271 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 5]
def baseStart_7256271 : Nat := 118140960795 + 7256271 * 2 ^ 59
def prefixEnd_7256271 : Nat := 4983230072969 + 3 ^ 40 * 7256271 * 2
def baseEnd_7256271 : Nat := 413994975809009393337947

theorem tailTrace_7256271 : CollatzResearch.WordTrace tailWord_7256271 prefixEnd_7256271 413994975809009393337947 := by
  unfold tailWord_7256271
  simp only [CollatzResearch.WordTrace]
  refine ⟨264657945894776914268392667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176438630596517942845595111 264657945894776914268392667)
  ·
    refine ⟨396986918842165371402589001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264657945894776914268392667 396986918842165371402589001)
    ·
      refine ⟨297740189131624028551941751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396986918842165371402589001 297740189131624028551941751)
      ·
        refine ⟨446610283697436042827912627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297740189131624028551941751 446610283697436042827912627)
        ·
          refine ⟨669915425546154064241868941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446610283697436042827912627 669915425546154064241868941)
          ·
            refine ⟨251218284579807774090700853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669915425546154064241868941 251218284579807774090700853)
            ·
              refine ⟨23551714179356978821003205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251218284579807774090700853 23551714179356978821003205)
              ·
                refine ⟨4415946408629433528938101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23551714179356978821003205 4415946408629433528938101)
                ·
                  refine ⟨413994975809009393337947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4415946408629433528938101 413994975809009393337947)
                  ·
                    rfl

theorem cell23_7256271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 5].length) (baseStart_7256271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256271 prefixEnd_7256271 := by exact prefixLift 7256271
  have htrace : WordTrace (prefixWord ++ tailWord_7256271) baseStart_7256271 baseEnd_7256271 := by
    simpa [prefixWord, tailWord_7256271, baseEnd_7256271] using wordTrace_append hprefix tailTrace_7256271
  have hstable : (prefixWord ++ tailWord_7256271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256271).length < 2 ^ (prefixWord ++ tailWord_7256271).sum := by decide
  have hdescent : baseEnd_7256271 < baseStart_7256271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256278 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7256278 : Nat := 118140960795 + 7256278 * 2 ^ 59
def prefixEnd_7256278 : Nat := 4983230072969 + 3 ^ 40 * 7256278 * 2
def baseEnd_7256278 : Nat := 3725958376645666012653991

theorem tailTrace_7256278 : CollatzResearch.WordTrace tailWord_7256278 prefixEnd_7256278 3725958376645666012653991 := by
  unfold tailWord_7256278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16541137575359472153993593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176438800803834369642598325 16541137575359472153993593)
  ·
    refine ⟨12405853181519604115495195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16541137575359472153993593 12405853181519604115495195)
    ·
      refine ⟨18608779772279406173242793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405853181519604115495195 18608779772279406173242793)
      ·
        refine ⟨13956584829209554629932095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18608779772279406173242793 13956584829209554629932095)
        ·
          refine ⟨20934877243814331944898143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956584829209554629932095 20934877243814331944898143)
          ·
            refine ⟨31402315865721497917347215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20934877243814331944898143 31402315865721497917347215)
            ·
              refine ⟨47103473798582246876020823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31402315865721497917347215 47103473798582246876020823)
              ·
                refine ⟨70655210697873370314031235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47103473798582246876020823 70655210697873370314031235)
                ·
                  refine ⟨105982816046810055471046853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70655210697873370314031235 105982816046810055471046853)
                  ·
                    refine ⟨19871778008776885400821285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105982816046810055471046853 19871778008776885400821285)
                    ·
                      refine ⟨3725958376645666012653991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19871778008776885400821285 3725958376645666012653991)
                      ·
                        rfl

theorem cell23_7256278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7256278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256278 prefixEnd_7256278 := by exact prefixLift 7256278
  have htrace : WordTrace (prefixWord ++ tailWord_7256278) baseStart_7256278 baseEnd_7256278 := by
    simpa [prefixWord, tailWord_7256278, baseEnd_7256278] using wordTrace_append hprefix tailTrace_7256278
  have hstable : (prefixWord ++ tailWord_7256278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256278).length < 2 ^ (prefixWord ++ tailWord_7256278).sum := by decide
  have hdescent : baseEnd_7256278 < baseStart_7256278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256321 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7256321 : Nat := 118140960795 + 7256321 * 2 ^ 59
def prefixEnd_7256321 : Nat := 4983230072969 + 3 ^ 40 * 7256321 * 2
def baseEnd_7256321 : Nat := 3725980456313809344416293

theorem tailTrace_7256321 : CollatzResearch.WordTrace tailWord_7256321 prefixEnd_7256321 3725980456313809344416293 := by
  unfold tailWord_7256321
  simp only [CollatzResearch.WordTrace]
  refine ⟨264659769544595772807712817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176439846363063848538475211 264659769544595772807712817)
  ·
    refine ⟨198494827158446829605784613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264659769544595772807712817 198494827158446829605784613)
    ·
      refine ⟨37217780092208780551084615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198494827158446829605784613 37217780092208780551084615)
      ·
        refine ⟨55826670138313170826626923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37217780092208780551084615 55826670138313170826626923)
        ·
          refine ⟨83740005207469756239940385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55826670138313170826626923 83740005207469756239940385)
          ·
            refine ⟨62805003905602317179955289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83740005207469756239940385 62805003905602317179955289)
            ·
              refine ⟨47103752929201737884966467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62805003905602317179955289 47103752929201737884966467)
              ·
                refine ⟨70655629393802606827449701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47103752929201737884966467 70655629393802606827449701)
                ·
                  refine ⟨13247930511337988780146819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70655629393802606827449701 13247930511337988780146819)
                  ·
                    refine ⟨19871895767006983170220229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13247930511337988780146819 19871895767006983170220229)
                    ·
                      refine ⟨3725980456313809344416293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19871895767006983170220229 3725980456313809344416293)
                      ·
                        rfl

theorem cell23_7256321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7256321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256321 prefixEnd_7256321 := by exact prefixLift 7256321
  have htrace : WordTrace (prefixWord ++ tailWord_7256321) baseStart_7256321 baseEnd_7256321 := by
    simpa [prefixWord, tailWord_7256321, baseEnd_7256321] using wordTrace_append hprefix tailTrace_7256321
  have hstable : (prefixWord ++ tailWord_7256321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256321).length < 2 ^ (prefixWord ++ tailWord_7256321).sum := by decide
  have hdescent : baseEnd_7256321 < baseStart_7256321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256341 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_7256341 : Nat := 118140960795 + 7256341 * 2 ^ 59
def prefixEnd_7256341 : Nat := 4983230072969 + 3 ^ 40 * 7256341 * 2
def baseEnd_7256341 : Nat := 3725990725926899266166201

theorem tailTrace_7256341 : CollatzResearch.WordTrace tailWord_7256341 prefixEnd_7256341 3725990725926899266166201 := by
  unfold tailWord_7256341
  simp only [CollatzResearch.WordTrace]
  refine ⟨264660499004523316223440877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176440332669682210815627251 264660499004523316223440877)
  ·
    refine ⟨99247687126696243583790329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264660499004523316223440877 99247687126696243583790329)
    ·
      refine ⟨74435765345022182687842747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99247687126696243583790329 74435765345022182687842747)
      ·
        refine ⟨111653648017533274031764121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74435765345022182687842747 111653648017533274031764121)
        ·
          refine ⟨83740236013149955523823091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111653648017533274031764121 83740236013149955523823091)
          ·
            refine ⟨125610354019724933285734637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83740236013149955523823091 125610354019724933285734637)
            ·
              refine ⟨47103882757396849982150489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125610354019724933285734637 47103882757396849982150489)
              ·
                refine ⟨35327912068047637486612867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47103882757396849982150489 35327912068047637486612867)
                ·
                  refine ⟨52991868102071456229919301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35327912068047637486612867 52991868102071456229919301)
                  ·
                    refine ⟨9935975269138398043109869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52991868102071456229919301 9935975269138398043109869)
                    ·
                      refine ⟨3725990725926899266166201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9935975269138398043109869 3725990725926899266166201)
                      ·
                        rfl

theorem cell23_7256341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_7256341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256341 prefixEnd_7256341 := by exact prefixLift 7256341
  have htrace : WordTrace (prefixWord ++ tailWord_7256341) baseStart_7256341 baseEnd_7256341 := by
    simpa [prefixWord, tailWord_7256341, baseEnd_7256341] using wordTrace_append hprefix tailTrace_7256341
  have hstable : (prefixWord ++ tailWord_7256341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256341).length < 2 ^ (prefixWord ++ tailWord_7256341).sum := by decide
  have hdescent : baseEnd_7256341 < baseStart_7256341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256391 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 3, 5]
def baseStart_7256391 : Nat := 118140960795 + 7256391 * 2 ^ 59
def prefixEnd_7256391 : Nat := 4983230072969 + 3 ^ 40 * 7256391 * 2
def baseEnd_7256391 : Nat := 1242005466653208023513657

theorem tailTrace_7256391 : CollatzResearch.WordTrace tailWord_7256391 prefixEnd_7256391 1242005466653208023513657 := by
  unfold tailWord_7256391
  simp only [CollatzResearch.WordTrace]
  refine ⟨264662322654342174762761027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176441548436228116508507351 264662322654342174762761027)
  ·
    refine ⟨396993483981513262144141541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264662322654342174762761027 396993483981513262144141541)
    ·
      refine ⟨74436278246533736652026539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396993483981513262144141541 74436278246533736652026539)
      ·
        refine ⟨111654417369800604978039809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74436278246533736652026539 111654417369800604978039809)
        ·
          refine ⟨83740813027350453733529857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111654417369800604978039809 83740813027350453733529857)
          ·
            refine ⟨62805609770512840300147393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83740813027350453733529857 62805609770512840300147393)
            ·
              refine ⟨47104207327884630225110545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62805609770512840300147393 47104207327884630225110545)
              ·
                refine ⟨35328155495913472668832909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47104207327884630225110545 35328155495913472668832909)
                ·
                  refine ⟨13248058310967552250812341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35328155495913472668832909 13248058310967552250812341)
                  ·
                    refine ⟨1242005466653208023513657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13248058310967552250812341 1242005466653208023513657)
                    ·
                      rfl

theorem cell23_7256391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_7256391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256391 prefixEnd_7256391 := by exact prefixLift 7256391
  have htrace : WordTrace (prefixWord ++ tailWord_7256391) baseStart_7256391 baseEnd_7256391 := by
    simpa [prefixWord, tailWord_7256391, baseEnd_7256391] using wordTrace_append hprefix tailTrace_7256391
  have hstable : (prefixWord ++ tailWord_7256391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256391).length < 2 ^ (prefixWord ++ tailWord_7256391).sum := by decide
  have hdescent : baseEnd_7256391 < baseStart_7256391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256398 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_7256398 : Nat := 118140960795 + 7256398 * 2 ^ 59
def prefixEnd_7256398 : Nat := 4983230072969 + 3 ^ 40 * 7256398 * 2
def baseEnd_7256398 : Nat := 3726019994324205543153439

theorem tailTrace_7256398 : CollatzResearch.WordTrace tailWord_7256398 prefixEnd_7256398 3726019994324205543153439 := by
  unfold tailWord_7256398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33082822245664601869783231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176441718643544543305510565 33082822245664601869783231)
  ·
    refine ⟨49624233368496902804674847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33082822245664601869783231 49624233368496902804674847)
    ·
      refine ⟨74436350052745354207012271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49624233368496902804674847 74436350052745354207012271)
      ·
        refine ⟨111654525079118031310518407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74436350052745354207012271 111654525079118031310518407)
        ·
          refine ⟨167481787618677046965777611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111654525079118031310518407 167481787618677046965777611)
          ·
            refine ⟨251222681428015570448666417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167481787618677046965777611 251222681428015570448666417)
            ·
              refine ⟨188417011071011677836499813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251222681428015570448666417 188417011071011677836499813)
              ·
                refine ⟨35328189575814689594343715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188417011071011677836499813 35328189575814689594343715)
                ·
                  refine ⟨52992284363722034391515573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35328189575814689594343715 52992284363722034391515573)
                  ·
                    refine ⟨4968026659098940724204585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52992284363722034391515573 4968026659098940724204585)
                    ·
                      refine ⟨3726019994324205543153439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968026659098940724204585 3726019994324205543153439)
                      ·
                        rfl

theorem cell23_7256398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_7256398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256398 prefixEnd_7256398 := by exact prefixLift 7256398
  have htrace : WordTrace (prefixWord ++ tailWord_7256398) baseStart_7256398 baseEnd_7256398 := by
    simpa [prefixWord, tailWord_7256398, baseEnd_7256398] using wordTrace_append hprefix tailTrace_7256398
  have hstable : (prefixWord ++ tailWord_7256398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256398).length < 2 ^ (prefixWord ++ tailWord_7256398).sum := by decide
  have hdescent : baseEnd_7256398 < baseStart_7256398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256421 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_7256421 : Nat := 118140960795 + 7256421 * 2 ^ 59
def prefixEnd_7256421 : Nat := 4983230072969 + 3 ^ 40 * 7256421 * 2
def baseEnd_7256421 : Nat := 1242010601459752984388611

theorem tailTrace_7256421 : CollatzResearch.WordTrace tailWord_7256421 prefixEnd_7256421 1242010601459752984388611 := by
  unfold tailWord_7256421
  simp only [CollatzResearch.WordTrace]
  refine ⟨264663416844233489886353117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176442277896155659924235411 264663416844233489886353117)
  ·
    refine ⟨99248781316587558707382419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264663416844233489886353117 99248781316587558707382419)
    ·
      refine ⟨148873171974881338061073629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99248781316587558707382419 148873171974881338061073629)
      ·
        refine ⟨55827439490580501772902611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148873171974881338061073629 55827439490580501772902611)
        ·
          refine ⟨83741159235870752659353917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55827439490580501772902611 83741159235870752659353917)
          ·
            refine ⟨31402934713451532247257719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83741159235870752659353917 31402934713451532247257719)
            ·
              refine ⟨47104402070177298370886579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31402934713451532247257719 47104402070177298370886579)
              ·
                refine ⟨70656603105265947556329869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47104402070177298370886579 70656603105265947556329869)
                ·
                  refine ⟨26496226164474730333623701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70656603105265947556329869 26496226164474730333623701)
                  ·
                    refine ⟨1242010601459752984388611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26496226164474730333623701 1242010601459752984388611)
                    ·
                      rfl

theorem cell23_7256421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_7256421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256421 prefixEnd_7256421 := by exact prefixLift 7256421
  have htrace : WordTrace (prefixWord ++ tailWord_7256421) baseStart_7256421 baseEnd_7256421 := by
    simpa [prefixWord, tailWord_7256421, baseEnd_7256421] using wordTrace_append hprefix tailTrace_7256421
  have hstable : (prefixWord ++ tailWord_7256421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256421).length < 2 ^ (prefixWord ++ tailWord_7256421).sum := by decide
  have hdescent : baseEnd_7256421 < baseStart_7256421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256431 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_7256431 : Nat := 118140960795 + 7256431 * 2 ^ 59
def prefixEnd_7256431 : Nat := 4983230072969 + 3 ^ 40 * 7256431 * 2
def baseEnd_7256431 : Nat := 3726036939185803914040787

theorem tailTrace_7256431 : CollatzResearch.WordTrace tailWord_7256431 prefixEnd_7256431 3726036939185803914040787 := by
  unfold tailWord_7256431
  simp only [CollatzResearch.WordTrace]
  refine ⟨264663781574197261594217147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176442521049464841062811431 264663781574197261594217147)
  ·
    refine ⟨396995672361295892391325721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264663781574197261594217147 396995672361295892391325721)
    ·
      refine ⟨297746754270971919293494291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396995672361295892391325721 297746754270971919293494291)
      ·
        refine ⟨446620131406457878940241437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297746754270971919293494291 446620131406457878940241437)
        ·
          refine ⟨167482549277421704602590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446620131406457878940241437 167482549277421704602590539)
          ·
            refine ⟨251223823916132556903885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167482549277421704602590539 251223823916132556903885809)
            ·
              refine ⟨188417867937099417677914357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251223823916132556903885809 188417867937099417677914357)
              ·
                refine ⟨17664175119103070407304471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188417867937099417677914357 17664175119103070407304471)
                ·
                  refine ⟨26496262678654605610956707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17664175119103070407304471 26496262678654605610956707)
                  ·
                    refine ⟨39744394017981908416435061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26496262678654605610956707 39744394017981908416435061)
                    ·
                      refine ⟨3726036939185803914040787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39744394017981908416435061 3726036939185803914040787)
                      ·
                        rfl

theorem cell23_7256431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_7256431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256431 prefixEnd_7256431 := by exact prefixLift 7256431
  have htrace : WordTrace (prefixWord ++ tailWord_7256431) baseStart_7256431 baseEnd_7256431 := by
    simpa [prefixWord, tailWord_7256431, baseEnd_7256431] using wordTrace_append hprefix tailTrace_7256431
  have hstable : (prefixWord ++ tailWord_7256431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256431).length < 2 ^ (prefixWord ++ tailWord_7256431).sum := by decide
  have hdescent : baseEnd_7256431 < baseStart_7256431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256441 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7256441 : Nat := 118140960795 + 7256441 * 2 ^ 59
def prefixEnd_7256441 : Nat := 4983230072969 + 3 ^ 40 * 7256441 * 2
def baseEnd_7256441 : Nat := 3726042073992348874915741

theorem tailTrace_7256441 : CollatzResearch.WordTrace tailWord_7256441 prefixEnd_7256441 3726042073992348874915741 := by
  unfold tailWord_7256441
  simp only [CollatzResearch.WordTrace]
  refine ⟨264664146304161033302081177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176442764202774022201387451 264664146304161033302081177)
  ·
    refine ⟨198498109728120774976560883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264664146304161033302081177 198498109728120774976560883)
    ·
      refine ⟨297747164592181162464841325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198498109728120774976560883 297747164592181162464841325)
      ·
        refine ⟨111655186722067935924315497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297747164592181162464841325 111655186722067935924315497)
        ·
          refine ⟨83741390041550951943236623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111655186722067935924315497 83741390041550951943236623)
          ·
            refine ⟨125612085062326427914854935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83741390041550951943236623 125612085062326427914854935)
            ·
              refine ⟨188418127593489641872282403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125612085062326427914854935 188418127593489641872282403)
              ·
                refine ⟨282627191390234462808423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188418127593489641872282403 282627191390234462808423605)
                ·
                  refine ⟨26496299192834480888289713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282627191390234462808423605 26496299192834480888289713)
                  ·
                    refine ⟨19872224394625860666217285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26496299192834480888289713 19872224394625860666217285)
                    ·
                      refine ⟨3726042073992348874915741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19872224394625860666217285 3726042073992348874915741)
                      ·
                        rfl

theorem cell23_7256441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7256441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256441 prefixEnd_7256441 := by exact prefixLift 7256441
  have htrace : WordTrace (prefixWord ++ tailWord_7256441) baseStart_7256441 baseEnd_7256441 := by
    simpa [prefixWord, tailWord_7256441, baseEnd_7256441] using wordTrace_append hprefix tailTrace_7256441
  have hstable : (prefixWord ++ tailWord_7256441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256441).length < 2 ^ (prefixWord ++ tailWord_7256441).sum := by decide
  have hdescent : baseEnd_7256441 < baseStart_7256441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256462 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7256462 : Nat := 118140960795 + 7256462 * 2 ^ 59
def prefixEnd_7256462 : Nat := 4983230072969 + 3 ^ 40 * 7256462 * 2
def baseEnd_7256462 : Nat := 3726052857086093292753145

theorem tailTrace_7256462 : CollatzResearch.WordTrace tailWord_7256462 prefixEnd_7256462 3726052857086093292753145 := by
  unfold tailWord_7256462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33083114029635619236074455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176443274824723302592397093 33083114029635619236074455)
  ·
    refine ⟨49624671044453428854111683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33083114029635619236074455 49624671044453428854111683)
    ·
      refine ⟨74437006566680143281167525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49624671044453428854111683 74437006566680143281167525)
      ·
        refine ⟨13956938731252526865218911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74437006566680143281167525 13956938731252526865218911)
        ·
          refine ⟨20935408096878790297828367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956938731252526865218911 20935408096878790297828367)
          ·
            refine ⟨31403112145318185446742551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20935408096878790297828367 31403112145318185446742551)
            ·
              refine ⟨47104668217977278170113827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31403112145318185446742551 47104668217977278170113827)
              ·
                refine ⟨70657002326965917255170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47104668217977278170113827 70657002326965917255170741)
                ·
                  refine ⟨6624093968153054742672257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70657002326965917255170741 6624093968153054742672257)
                  ·
                    refine ⟨4968070476114791057004193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624093968153054742672257 4968070476114791057004193)
                    ·
                      refine ⟨3726052857086093292753145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968070476114791057004193 3726052857086093292753145)
                      ·
                        rfl

theorem cell23_7256462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7256462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256462 prefixEnd_7256462 := by exact prefixLift 7256462
  have htrace : WordTrace (prefixWord ++ tailWord_7256462) baseStart_7256462 baseEnd_7256462 := by
    simpa [prefixWord, tailWord_7256462, baseEnd_7256462] using wordTrace_append hprefix tailTrace_7256462
  have hstable : (prefixWord ++ tailWord_7256462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256462).length < 2 ^ (prefixWord ++ tailWord_7256462).sum := by decide
  have hdescent : baseEnd_7256462 < baseStart_7256462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256479 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7256479 : Nat := 118140960795 + 7256479 * 2 ^ 59
def prefixEnd_7256479 : Nat := 4983230072969 + 3 ^ 40 * 7256479 * 2
def baseEnd_7256479 : Nat := 3726061586257219726240567

theorem tailTrace_7256479 : CollatzResearch.WordTrace tailWord_7256479 prefixEnd_7256479 3726061586257219726240567 := by
  unfold tailWord_7256479
  simp only [CollatzResearch.WordTrace]
  refine ⟨264665532278023365791964491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176443688185348910527976327 264665532278023365791964491)
  ·
    refine ⟨396998298417035048687946737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264665532278023365791964491 396998298417035048687946737)
    ·
      refine ⟨297748723812776286515960053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396998298417035048687946737 297748723812776286515960053)
      ·
        refine ⟨27913942857447776860871255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297748723812776286515960053 27913942857447776860871255)
        ·
          refine ⟨41870914286171665291306883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27913942857447776860871255 41870914286171665291306883)
          ·
            refine ⟨62806371429257497936960325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41870914286171665291306883 62806371429257497936960325)
            ·
              refine ⟨11776194642985780863180061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62806371429257497936960325 11776194642985780863180061)
              ·
                refine ⟨4416072991119667823692523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11776194642985780863180061 4416072991119667823692523)
                ·
                  refine ⟨6624109486679501735538785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416072991119667823692523 6624109486679501735538785)
                  ·
                    refine ⟨4968082115009626301654089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624109486679501735538785 4968082115009626301654089)
                    ·
                      refine ⟨3726061586257219726240567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968082115009626301654089 3726061586257219726240567)
                      ·
                        rfl

theorem cell23_7256479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7256479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256479 prefixEnd_7256479 := by exact prefixLift 7256479
  have htrace : WordTrace (prefixWord ++ tailWord_7256479) baseStart_7256479 baseEnd_7256479 := by
    simpa [prefixWord, tailWord_7256479, baseEnd_7256479] using wordTrace_append hprefix tailTrace_7256479
  have hstable : (prefixWord ++ tailWord_7256479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256479).length < 2 ^ (prefixWord ++ tailWord_7256479).sum := by decide
  have hdescent : baseEnd_7256479 < baseStart_7256479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256522 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_7256522 : Nat := 118140960795 + 7256522 * 2 ^ 59
def prefixEnd_7256522 : Nat := 4983230072969 + 3 ^ 40 * 7256522 * 2
def baseEnd_7256522 : Nat := 3726083665925363058002869

theorem tailTrace_7256522 : CollatzResearch.WordTrace tailWord_7256522 prefixEnd_7256522 3726083665925363058002869 := by
  unfold tailWord_7256522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66166775154216896033944955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176444733744578389423853213 66166775154216896033944955)
  ·
    refine ⟨99250162731325344050917433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66166775154216896033944955 99250162731325344050917433)
    ·
      refine ⟨74437622048494008038188075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99250162731325344050917433 74437622048494008038188075)
      ·
        refine ⟨111656433072741012057282113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74437622048494008038188075 111656433072741012057282113)
        ·
          refine ⟨83742324804555759042961585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111656433072741012057282113 83742324804555759042961585)
          ·
            refine ⟨62806743603416819282221189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83742324804555759042961585 62806743603416819282221189)
            ·
              refine ⟨11776264425640653615416473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62806743603416819282221189 11776264425640653615416473)
              ·
                refine ⟨8832198319230490211562355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11776264425640653615416473 8832198319230490211562355)
                ·
                  refine ⟨13248297478845735317343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832198319230490211562355 13248297478845735317343533)
                  ·
                    refine ⟨4968111554567150744003825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13248297478845735317343533 4968111554567150744003825)
                    ·
                      refine ⟨3726083665925363058002869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968111554567150744003825 3726083665925363058002869)
                      ·
                        rfl

theorem cell23_7256522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_7256522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256522 prefixEnd_7256522 := by exact prefixLift 7256522
  have htrace : WordTrace (prefixWord ++ tailWord_7256522) baseStart_7256522 baseEnd_7256522 := by
    simpa [prefixWord, tailWord_7256522, baseEnd_7256522] using wordTrace_append hprefix tailTrace_7256522
  have hstable : (prefixWord ++ tailWord_7256522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256522).length < 2 ^ (prefixWord ++ tailWord_7256522).sum := by decide
  have hdescent : baseEnd_7256522 < baseStart_7256522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256530 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7256530 : Nat := 118140960795 + 7256530 * 2 ^ 59
def prefixEnd_7256530 : Nat := 4983230072969 + 3 ^ 40 * 7256530 * 2
def baseEnd_7256530 : Nat := 3726087773770599026702833

theorem tailTrace_7256530 : CollatzResearch.WordTrace tailWord_7256530 prefixEnd_7256530 3726087773770599026702833 := by
  unfold tailWord_7256530
  simp only [CollatzResearch.WordTrace]
  refine ⟨66166848100209650375517761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176444928267225734334714029 66166848100209650375517761)
  ·
    refine ⟨49625136075157237781638321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66166848100209650375517761 49625136075157237781638321)
    ·
      refine ⟨37218852056367928336228741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49625136075157237781638321 37218852056367928336228741)
      ·
        refine ⟨6978534760568986563042889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37218852056367928336228741 6978534760568986563042889)
        ·
          refine ⟨5233901070426739922282167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978534760568986563042889 5233901070426739922282167)
          ·
            refine ⟨7850851605640109883423251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233901070426739922282167 7850851605640109883423251)
            ·
              refine ⟨11776277408460164825134877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7850851605640109883423251 11776277408460164825134877)
              ·
                refine ⟨4416104028172561809425579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11776277408460164825134877 4416104028172561809425579)
                ·
                  refine ⟨6624156042258842714138369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416104028172561809425579 6624156042258842714138369)
                  ·
                    refine ⟨4968117031694132035603777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624156042258842714138369 4968117031694132035603777)
                    ·
                      refine ⟨3726087773770599026702833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968117031694132035603777 3726087773770599026702833)
                      ·
                        rfl

theorem cell23_7256530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7256530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256530 prefixEnd_7256530 := by exact prefixLift 7256530
  have htrace : WordTrace (prefixWord ++ tailWord_7256530) baseStart_7256530 baseEnd_7256530 := by
    simpa [prefixWord, tailWord_7256530, baseEnd_7256530] using wordTrace_append hprefix tailTrace_7256530
  have hstable : (prefixWord ++ tailWord_7256530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256530).length < 2 ^ (prefixWord ++ tailWord_7256530).sum := by decide
  have hdescent : baseEnd_7256530 < baseStart_7256530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256538 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_7256538 : Nat := 118140960795 + 7256538 * 2 ^ 59
def prefixEnd_7256538 : Nat := 4983230072969 + 3 ^ 40 * 7256538 * 2
def baseEnd_7256538 : Nat := 3726091881615834995402795

theorem tailTrace_7256538 : CollatzResearch.WordTrace tailWord_7256538 prefixEnd_7256538 3726091881615834995402795 := by
  unfold tailWord_7256538
  simp only [CollatzResearch.WordTrace]
  refine ⟨66166921046202404717090567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176445122789873079245574845 66166921046202404717090567)
  ·
    refine ⟨99250381569303607075635851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66166921046202404717090567 99250381569303607075635851)
    ·
      refine ⟨148875572353955410613453777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99250381569303607075635851 148875572353955410613453777)
      ·
        refine ⟨111656679265466557960090333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148875572353955410613453777 111656679265466557960090333)
        ·
          refine ⟨41871254724549959235033875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111656679265466557960090333 41871254724549959235033875)
          ·
            refine ⟨62806882086824938852550813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41871254724549959235033875 62806882086824938852550813)
            ·
              refine ⟨23552580782559352069706555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62806882086824938852550813 23552580782559352069706555)
              ·
                refine ⟨35328871173839028104559833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23552580782559352069706555 35328871173839028104559833)
                ·
                  refine ⟨26496653380379271078419875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35328871173839028104559833 26496653380379271078419875)
                  ·
                    refine ⟨39744980070568906617629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26496653380379271078419875 39744980070568906617629813)
                    ·
                      refine ⟨3726091881615834995402795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39744980070568906617629813 3726091881615834995402795)
                      ·
                        rfl

theorem cell23_7256538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_7256538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256538 prefixEnd_7256538 := by exact prefixLift 7256538
  have htrace : WordTrace (prefixWord ++ tailWord_7256538) baseStart_7256538 baseEnd_7256538 := by
    simpa [prefixWord, tailWord_7256538, baseEnd_7256538] using wordTrace_append hprefix tailTrace_7256538
  have hstable : (prefixWord ++ tailWord_7256538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256538).length < 2 ^ (prefixWord ++ tailWord_7256538).sum := by decide
  have hdescent : baseEnd_7256538 < baseStart_7256538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256552 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7256552 : Nat := 118140960795 + 7256552 * 2 ^ 59
def prefixEnd_7256552 : Nat := 4983230072969 + 3 ^ 40 * 7256552 * 2
def baseEnd_7256552 : Nat := 3726099070344997940627731

theorem tailTrace_7256552 : CollatzResearch.WordTrace tailWord_7256552 prefixEnd_7256552 3726099070344997940627731 := by
  unfold tailWord_7256552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132334097403379449629685955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176445463204505932839581273 132334097403379449629685955)
  ·
    refine ⟨198501146105069174444528933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132334097403379449629685955 198501146105069174444528933)
    ·
      refine ⟨37218964894700470208349175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198501146105069174444528933 37218964894700470208349175)
      ·
        refine ⟨55828447342050705312523763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37218964894700470208349175 55828447342050705312523763)
        ·
          refine ⟨83742671013076057968785645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55828447342050705312523763 83742671013076057968785645)
          ·
            refine ⟨31403501629903521738294617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83742671013076057968785645 31403501629903521738294617)
            ·
              refine ⟨23552626222427641303720963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31403501629903521738294617 23552626222427641303720963)
              ·
                refine ⟨35328939333641461955581445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23552626222427641303720963 35328939333641461955581445)
                ·
                  refine ⟨6624176125057774116671521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35328939333641461955581445 6624176125057774116671521)
                  ·
                    refine ⟨4968132093793330587503641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624176125057774116671521 4968132093793330587503641)
                    ·
                      refine ⟨3726099070344997940627731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968132093793330587503641 3726099070344997940627731)
                      ·
                        rfl

theorem cell23_7256552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7256552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256552 prefixEnd_7256552 := by exact prefixLift 7256552
  have htrace : WordTrace (prefixWord ++ tailWord_7256552) baseStart_7256552 baseEnd_7256552 := by
    simpa [prefixWord, tailWord_7256552, baseEnd_7256552] using wordTrace_append hprefix tailTrace_7256552
  have hstable : (prefixWord ++ tailWord_7256552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256552).length < 2 ^ (prefixWord ++ tailWord_7256552).sum := by decide
  have hdescent : baseEnd_7256552 < baseStart_7256552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256568 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_7256568 : Nat := 118140960795 + 7256568 * 2 ^ 59
def prefixEnd_7256568 : Nat := 4983230072969 + 3 ^ 40 * 7256568 * 2
def baseEnd_7256568 : Nat := 3726107286035469878027657

theorem tailTrace_7256568 : CollatzResearch.WordTrace tailWord_7256568 prefixEnd_7256568 3726107286035469878027657 := by
  unfold tailWord_7256568
  simp only [CollatzResearch.WordTrace]
  refine ⟨132334389187350466995977179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176445852249800622661302905 132334389187350466995977179)
  ·
    refine ⟨198501583781025700493965769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132334389187350466995977179 198501583781025700493965769)
    ·
      refine ⟨148876187835769275370474327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198501583781025700493965769 148876187835769275370474327)
      ·
        refine ⟨223314281753653913055711491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148876187835769275370474327 223314281753653913055711491)
        ·
          refine ⟨334971422630480869583567237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223314281753653913055711491 334971422630480869583567237)
          ·
            refine ⟨62807141743215163046918857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334971422630480869583567237 62807141743215163046918857)
            ·
              refine ⟨47105356307411372285189143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62807141743215163046918857 47105356307411372285189143)
              ·
                refine ⟨70658034461117058427783715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47105356307411372285189143 70658034461117058427783715)
                ·
                  refine ⟨105987051691675587641675573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70658034461117058427783715 105987051691675587641675573)
                  ·
                    refine ⟨9936286096094586341407085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105987051691675587641675573 9936286096094586341407085)
                    ·
                      refine ⟨3726107286035469878027657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9936286096094586341407085 3726107286035469878027657)
                      ·
                        rfl

theorem cell23_7256568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_7256568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256568 prefixEnd_7256568 := by exact prefixLift 7256568
  have htrace : WordTrace (prefixWord ++ tailWord_7256568) baseStart_7256568 baseEnd_7256568 := by
    simpa [prefixWord, tailWord_7256568, baseEnd_7256568] using wordTrace_append hprefix tailTrace_7256568
  have hstable : (prefixWord ++ tailWord_7256568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256568).length < 2 ^ (prefixWord ++ tailWord_7256568).sum := by decide
  have hdescent : baseEnd_7256568 < baseStart_7256568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256569 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 2, 2, 2]
def baseStart_7256569 : Nat := 118140960795 + 7256569 * 2 ^ 59
def prefixEnd_7256569 : Nat := 4983230072969 + 3 ^ 40 * 7256569 * 2
def baseEnd_7256569 : Nat := 3726107799516124374115153

theorem tailTrace_7256569 : CollatzResearch.WordTrace tailWord_7256569 prefixEnd_7256569 3726107799516124374115153 := by
  unfold tailWord_7256569
  simp only [CollatzResearch.WordTrace]
  refine ⟨264668814847697311162740761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176445876565131540775160507 264668814847697311162740761)
  ·
    refine ⟨198501611135772983372055571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264668814847697311162740761 198501611135772983372055571)
    ·
      refine ⟨297752416703659475058083357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198501611135772983372055571 297752416703659475058083357)
      ·
        refine ⟨111657156263872303146781259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297752416703659475058083357 111657156263872303146781259)
        ·
          refine ⟨167485734395808454720171889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111657156263872303146781259 167485734395808454720171889)
          ·
            refine ⟨125614300796856341040128917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167485734395808454720171889 125614300796856341040128917)
            ·
              refine ⟨5888170349852640986256043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125614300796856341040128917 5888170349852640986256043)
              ·
                refine ⟨8832255524778961479384065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888170349852640986256043 8832255524778961479384065)
                ·
                  refine ⟨6624191643584221109538049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8832255524778961479384065 6624191643584221109538049)
                  ·
                    refine ⟨4968143732688165832153537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624191643584221109538049 4968143732688165832153537)
                    ·
                      refine ⟨3726107799516124374115153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968143732688165832153537 3726107799516124374115153)
                      ·
                        rfl

theorem cell23_7256569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_7256569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256569 prefixEnd_7256569 := by exact prefixLift 7256569
  have htrace : WordTrace (prefixWord ++ tailWord_7256569) baseStart_7256569 baseEnd_7256569 := by
    simpa [prefixWord, tailWord_7256569, baseEnd_7256569] using wordTrace_append hprefix tailTrace_7256569
  have hstable : (prefixWord ++ tailWord_7256569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256569).length < 2 ^ (prefixWord ++ tailWord_7256569).sum := by decide
  have hdescent : baseEnd_7256569 < baseStart_7256569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256605 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_7256605 : Nat := 118140960795 + 7256605 * 2 ^ 59
def prefixEnd_7256605 : Nat := 4983230072969 + 3 ^ 40 * 7256605 * 2
def baseEnd_7256605 : Nat := 1242042094939895411088329

theorem tailTrace_7256605 : CollatzResearch.WordTrace tailWord_7256605 prefixEnd_7256605 1242042094939895411088329 := by
  unfold tailWord_7256605
  simp only [CollatzResearch.WordTrace]
  refine ⟨264670127875566889311051269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176446751917044592874034179 264670127875566889311051269)
  ·
    refine ⟨49625648976668791745822113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264670127875566889311051269 49625648976668791745822113)
    ·
      refine ⟨37219236732501593809366585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49625648976668791745822113 37219236732501593809366585)
      ·
        refine ⟨27914427549376195357024939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37219236732501593809366585 27914427549376195357024939)
        ·
          refine ⟨41871641324064293035537409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27914427549376195357024939 41871641324064293035537409)
          ·
            refine ⟨31403730993048219776653057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41871641324064293035537409 31403730993048219776653057)
            ·
              refine ⟨23552798244786164832489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31403730993048219776653057 23552798244786164832489793)
              ·
                refine ⟨17664598683589623624367345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23552798244786164832489793 17664598683589623624367345)
                ·
                  refine ⟨13248449012692217718275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17664598683589623624367345 13248449012692217718275509)
                  ·
                    refine ⟨1242042094939895411088329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13248449012692217718275509 1242042094939895411088329)
                    ·
                      rfl

theorem cell23_7256605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_7256605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256605 prefixEnd_7256605 := by exact prefixLift 7256605
  have htrace : WordTrace (prefixWord ++ tailWord_7256605) baseStart_7256605 baseEnd_7256605 := by
    simpa [prefixWord, tailWord_7256605, baseEnd_7256605] using wordTrace_append hprefix tailTrace_7256605
  have hstable : (prefixWord ++ tailWord_7256605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256605).length < 2 ^ (prefixWord ++ tailWord_7256605).sum := by decide
  have hdescent : baseEnd_7256605 < baseStart_7256605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256625 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_7256625 : Nat := 118140960795 + 7256625 * 2 ^ 59
def prefixEnd_7256625 : Nat := 4983230072969 + 3 ^ 40 * 7256625 * 2
def baseEnd_7256625 : Nat := 3726136554432776155014895

theorem tailTrace_7256625 : CollatzResearch.WordTrace tailWord_7256625 prefixEnd_7256625 3726136554432776155014895 := by
  unfold tailWord_7256625
  simp only [CollatzResearch.WordTrace]
  refine ⟨264670857335494432726779329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176447238223662955151186219 264670857335494432726779329)
  ·
    refine ⟨198503143001620824545084497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264670857335494432726779329 198503143001620824545084497)
    ·
      refine ⟨148877357251215618408813373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198503143001620824545084497 148877357251215618408813373)
      ·
        refine ⟨55829008969205856903305015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148877357251215618408813373 55829008969205856903305015)
        ·
          refine ⟨83743513453808785354957523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55829008969205856903305015 83743513453808785354957523)
          ·
            refine ⟨125615270180713178032436285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83743513453808785354957523 125615270180713178032436285)
            ·
              refine ⟨47105726317767441762163607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125615270180713178032436285 47105726317767441762163607)
              ·
                refine ⟨70658589476651162643245411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47105726317767441762163607 70658589476651162643245411)
                ·
                  refine ⟨105987884214976743964868117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70658589476651162643245411 105987884214976743964868117)
                  ·
                    refine ⟨4968182072577034873353193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105987884214976743964868117 4968182072577034873353193)
                    ·
                      refine ⟨3726136554432776155014895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968182072577034873353193 3726136554432776155014895)
                      ·
                        rfl

theorem cell23_7256625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_7256625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256625 prefixEnd_7256625 := by exact prefixLift 7256625
  have htrace : WordTrace (prefixWord ++ tailWord_7256625) baseStart_7256625 baseEnd_7256625 := by
    simpa [prefixWord, tailWord_7256625, baseEnd_7256625] using wordTrace_append hprefix tailTrace_7256625
  have hstable : (prefixWord ++ tailWord_7256625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256625).length < 2 ^ (prefixWord ++ tailWord_7256625).sum := by decide
  have hdescent : baseEnd_7256625 < baseStart_7256625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256645 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_7256645 : Nat := 118140960795 + 7256645 * 2 ^ 59
def prefixEnd_7256645 : Nat := 4983230072969 + 3 ^ 40 * 7256645 * 2
def baseEnd_7256645 : Nat := 3726146824045866076764803

theorem tailTrace_7256645 : CollatzResearch.WordTrace tailWord_7256645 prefixEnd_7256645 3726146824045866076764803 := by
  unfold tailWord_7256645
  simp only [CollatzResearch.WordTrace]
  refine ⟨264671586795421976142507389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176447724530281317428338259 264671586795421976142507389)
  ·
    refine ⟨99251845048283241053440271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264671586795421976142507389 99251845048283241053440271)
    ·
      refine ⟨148877767572424861580160407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99251845048283241053440271 148877767572424861580160407)
      ·
        refine ⟨223316651358637292370240611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148877767572424861580160407 223316651358637292370240611)
        ·
          refine ⟨334974977037955938555360917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223316651358637292370240611 334974977037955938555360917)
          ·
            refine ⟨15701952048654184619782543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334974977037955938555360917 15701952048654184619782543)
            ·
              refine ⟨23552928072981276929673815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15701952048654184619782543 23552928072981276929673815)
              ·
                refine ⟨35329392109471915394510723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23552928072981276929673815 35329392109471915394510723)
                ·
                  refine ⟨52994088164207873091766085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35329392109471915394510723 52994088164207873091766085)
                  ·
                    refine ⟨9936391530788976204706141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52994088164207873091766085 9936391530788976204706141)
                    ·
                      refine ⟨3726146824045866076764803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9936391530788976204706141 3726146824045866076764803)
                      ·
                        rfl

theorem cell23_7256645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_7256645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256645 prefixEnd_7256645 := by exact prefixLift 7256645
  have htrace : WordTrace (prefixWord ++ tailWord_7256645) baseStart_7256645 baseEnd_7256645 := by
    simpa [prefixWord, tailWord_7256645, baseEnd_7256645] using wordTrace_append hprefix tailTrace_7256645
  have hstable : (prefixWord ++ tailWord_7256645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256645).length < 2 ^ (prefixWord ++ tailWord_7256645).sum := by decide
  have hdescent : baseEnd_7256645 < baseStart_7256645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256682 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_7256682 : Nat := 118140960795 + 7256682 * 2 ^ 59
def prefixEnd_7256682 : Nat := 4983230072969 + 3 ^ 40 * 7256682 * 2
def baseEnd_7256682 : Nat := 414018424758898048000237

theorem tailTrace_7256682 : CollatzResearch.WordTrace tailWord_7256682 prefixEnd_7256682 414018424758898048000237 := by
  unfold tailWord_7256682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66168234074071982865401075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176448624197525287641069533 66168234074071982865401075)
  ·
    refine ⟨99252351111107974298101613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66168234074071982865401075 99252351111107974298101613)
    ·
      refine ⟨37219631666665490361788105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99252351111107974298101613 37219631666665490361788105)
      ·
        refine ⟨27914723749999117771341079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37219631666665490361788105 27914723749999117771341079)
        ·
          refine ⟨41872085624998676657011619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27914723749999117771341079 41872085624998676657011619)
          ·
            refine ⟨62808128437498014985517429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41872085624998676657011619 62808128437498014985517429)
            ·
              refine ⟨5888262041015438904892259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62808128437498014985517429 5888262041015438904892259)
              ·
                refine ⟨8832393061523158357338389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888262041015438904892259 8832393061523158357338389)
                ·
                  refine ⟨414018424758898048000237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8832393061523158357338389 414018424758898048000237)
                  ·
                    rfl

theorem cell23_7256682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_7256682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256682 prefixEnd_7256682 := by exact prefixLift 7256682
  have htrace : WordTrace (prefixWord ++ tailWord_7256682) baseStart_7256682 baseEnd_7256682 := by
    simpa [prefixWord, tailWord_7256682, baseEnd_7256682] using wordTrace_append hprefix tailTrace_7256682
  have hstable : (prefixWord ++ tailWord_7256682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256682).length < 2 ^ (prefixWord ++ tailWord_7256682).sum := by decide
  have hdescent : baseEnd_7256682 < baseStart_7256682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256695 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 1, 5]
def baseStart_7256695 : Nat := 118140960795 + 7256695 * 2 ^ 59
def prefixEnd_7256695 : Nat := 4983230072969 + 3 ^ 40 * 7256695 * 2
def baseEnd_7256695 : Nat := 1242057499359530293713191

theorem tailTrace_7256695 : CollatzResearch.WordTrace tailWord_7256695 prefixEnd_7256695 1242057499359530293713191 := by
  unfold tailWord_7256695
  simp only [CollatzResearch.WordTrace]
  refine ⟨264673410445240834681827539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176448940296827223121218359 264673410445240834681827539)
  ·
    refine ⟨397010115667861252022741309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264673410445240834681827539 397010115667861252022741309)
    ·
      refine ⟨148878793375447969508527991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397010115667861252022741309 148878793375447969508527991)
      ·
        refine ⟨223318190063171954262791987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148878793375447969508527991 223318190063171954262791987)
        ·
          refine ⟨334977285094757931394187981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223318190063171954262791987 334977285094757931394187981)
          ·
            refine ⟨125616481910534224272820493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334977285094757931394187981 125616481910534224272820493)
            ·
              refine ⟨47106180716450334102307685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125616481910534224272820493 47106180716450334102307685)
              ·
                refine ⟨8832408884334437644182691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47106180716450334102307685 8832408884334437644182691)
                ·
                  refine ⟨13248613326501656466274037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832408884334437644182691 13248613326501656466274037)
                  ·
                    refine ⟨1242057499359530293713191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13248613326501656466274037 1242057499359530293713191)
                    ·
                      rfl

theorem cell23_7256695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_7256695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256695 prefixEnd_7256695 := by exact prefixLift 7256695
  have htrace : WordTrace (prefixWord ++ tailWord_7256695) baseStart_7256695 baseEnd_7256695 := by
    simpa [prefixWord, tailWord_7256695, baseEnd_7256695] using wordTrace_append hprefix tailTrace_7256695
  have hstable : (prefixWord ++ tailWord_7256695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256695).length < 2 ^ (prefixWord ++ tailWord_7256695).sum := by decide
  have hdescent : baseEnd_7256695 < baseStart_7256695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256749 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7256749 : Nat := 118140960795 + 7256749 * 2 ^ 59
def prefixEnd_7256749 : Nat := 4983230072969 + 3 ^ 40 * 7256749 * 2
def baseEnd_7256749 : Nat := 3726200226033933669864325

theorem tailTrace_7256749 : CollatzResearch.WordTrace tailWord_7256749 prefixEnd_7256749 3726200226033933669864325 := by
  unfold tailWord_7256749
  simp only [CollatzResearch.WordTrace]
  refine ⟨264675379987045201904293301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176450253324696801269528867 264675379987045201904293301)
  ·
    refine ⟨24813316873785487678527497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264675379987045201904293301 24813316873785487678527497)
    ·
      refine ⟨18609987655339115758895623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24813316873785487678527497 18609987655339115758895623)
      ·
        refine ⟨27914981483008673638343435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18609987655339115758895623 27914981483008673638343435)
        ·
          refine ⟨41872472224513010457515153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27914981483008673638343435 41872472224513010457515153)
          ·
            refine ⟨31404354168384757843136365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41872472224513010457515153 31404354168384757843136365)
            ·
              refine ⟨11776632813144284191176137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31404354168384757843136365 11776632813144284191176137)
              ·
                refine ⟨8832474609858213143382103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11776632813144284191176137 8832474609858213143382103)
                ·
                  refine ⟨13248711914787319715073155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832474609858213143382103 13248711914787319715073155)
                  ·
                    refine ⟨19873067872180979572609733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13248711914787319715073155 19873067872180979572609733)
                    ·
                      refine ⟨3726200226033933669864325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19873067872180979572609733 3726200226033933669864325)
                      ·
                        rfl

theorem cell23_7256749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7256749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256749 prefixEnd_7256749 := by exact prefixLift 7256749
  have htrace : WordTrace (prefixWord ++ tailWord_7256749) baseStart_7256749 baseEnd_7256749 := by
    simpa [prefixWord, tailWord_7256749, baseEnd_7256749] using wordTrace_append hprefix tailTrace_7256749
  have hstable : (prefixWord ++ tailWord_7256749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256749).length < 2 ^ (prefixWord ++ tailWord_7256749).sum := by decide
  have hdescent : baseEnd_7256749 < baseStart_7256749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256789 : List Nat := [1, 3, 2, 5, 1, 2, 1, 8]
def baseStart_7256789 : Nat := 118140960795 + 7256789 * 2 ^ 59
def prefixEnd_7256789 : Nat := 4983230072969 + 3 ^ 40 * 7256789 * 2
def baseEnd_7256789 : Nat := 138008176491115315309783

theorem tailTrace_7256789 : CollatzResearch.WordTrace tailWord_7256789 prefixEnd_7256789 138008176491115315309783 := by
  unfold tailWord_7256789
  simp only [CollatzResearch.WordTrace]
  refine ⟨264676838906900288735749421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176451225937933525823832947 264676838906900288735749421)
  ·
    refine ⟨99253814590087608275906033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264676838906900288735749421 99253814590087608275906033)
    ·
      refine ⟨74440360942565706206929525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99253814590087608275906033 74440360942565706206929525)
      ·
        refine ⟨6978783838365534956899643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74440360942565706206929525 6978783838365534956899643)
        ·
          refine ⟨10468175757548302435349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978783838365534956899643 10468175757548302435349465)
          ·
            refine ⟨7851131818161226826512099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468175757548302435349465 7851131818161226826512099)
            ·
              refine ⟨11776697727241840239768149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851131818161226826512099 11776697727241840239768149)
              ·
                refine ⟨138008176491115315309783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11776697727241840239768149 138008176491115315309783)
                ·
                  rfl

theorem cell23_7256789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 8].length) (baseStart_7256789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256789 prefixEnd_7256789 := by exact prefixLift 7256789
  have htrace : WordTrace (prefixWord ++ tailWord_7256789) baseStart_7256789 baseEnd_7256789 := by
    simpa [prefixWord, tailWord_7256789, baseEnd_7256789] using wordTrace_append hprefix tailTrace_7256789
  have hstable : (prefixWord ++ tailWord_7256789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256789).length < 2 ^ (prefixWord ++ tailWord_7256789).sum := by decide
  have hdescent : baseEnd_7256789 < baseStart_7256789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256799 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_7256799 : Nat := 118140960795 + 7256799 * 2 ^ 59
def prefixEnd_7256799 : Nat := 4983230072969 + 3 ^ 40 * 7256799 * 2
def baseEnd_7256799 : Nat := 3726225900066658474239095

theorem tailTrace_7256799 : CollatzResearch.WordTrace tailWord_7256799 prefixEnd_7256799 3726225900066658474239095 := by
  unfold tailWord_7256799
  simp only [CollatzResearch.WordTrace]
  refine ⟨264677203636864060443613451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176451469091242706962408967 264677203636864060443613451)
  ·
    refine ⟨397015805455296090665420177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264677203636864060443613451 397015805455296090665420177)
    ·
      refine ⟨297761854091472067999065133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397015805455296090665420177 297761854091472067999065133)
      ·
        refine ⟨111660695284302025499649425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297761854091472067999065133 111660695284302025499649425)
        ·
          refine ⟨83745521463226519124737069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111660695284302025499649425 83745521463226519124737069)
          ·
            refine ⟨31404570548709944671776401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83745521463226519124737069 31404570548709944671776401)
            ·
              refine ⟨23553427911532458503832301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31404570548709944671776401 23553427911532458503832301)
              ·
                refine ⟨8832535466824671938937113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23553427911532458503832301 8832535466824671938937113)
                ·
                  refine ⟨6624401600118503954202835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8832535466824671938937113 6624401600118503954202835)
                  ·
                    refine ⟨9936602400177755931304253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624401600118503954202835 9936602400177755931304253)
                    ·
                      refine ⟨3726225900066658474239095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9936602400177755931304253 3726225900066658474239095)
                      ·
                        rfl

theorem cell23_7256799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_7256799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256799 prefixEnd_7256799 := by exact prefixLift 7256799
  have htrace : WordTrace (prefixWord ++ tailWord_7256799) baseStart_7256799 baseEnd_7256799 := by
    simpa [prefixWord, tailWord_7256799, baseEnd_7256799] using wordTrace_append hprefix tailTrace_7256799
  have hstable : (prefixWord ++ tailWord_7256799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256799).length < 2 ^ (prefixWord ++ tailWord_7256799).sum := by decide
  have hdescent : baseEnd_7256799 < baseStart_7256799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256825 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7256825 : Nat := 118140960795 + 7256825 * 2 ^ 59
def prefixEnd_7256825 : Nat := 4983230072969 + 3 ^ 40 * 7256825 * 2
def baseEnd_7256825 : Nat := 3726239250563675372513975

theorem tailTrace_7256825 : CollatzResearch.WordTrace tailWord_7256825 prefixEnd_7256825 3726239250563675372513975 := by
  unfold tailWord_7256825
  simp only [CollatzResearch.WordTrace]
  refine ⟨264678151934769866884059929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176452101289846577922706619 264678151934769866884059929)
  ·
    refine ⟨198508613951077400163044947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264678151934769866884059929 198508613951077400163044947)
    ·
      refine ⟨297762920926616100244567421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198508613951077400163044947 297762920926616100244567421)
      ·
        refine ⟨111661095347481037591712783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297762920926616100244567421 111661095347481037591712783)
        ·
          refine ⟨167491643021221556387569175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111661095347481037591712783 167491643021221556387569175)
          ·
            refine ⟨251237464531832334581353763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167491643021221556387569175 251237464531832334581353763)
            ·
              refine ⟨376856196797748501872030645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251237464531832334581353763 376856196797748501872030645)
              ·
                refine ⟨35330268449788922050502873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376856196797748501872030645 35330268449788922050502873)
                ·
                  refine ⟨26497701337341691537877155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35330268449788922050502873 26497701337341691537877155)
                  ·
                    refine ⟨39746552006012537306815733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26497701337341691537877155 39746552006012537306815733)
                    ·
                      refine ⟨3726239250563675372513975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39746552006012537306815733 3726239250563675372513975)
                      ·
                        rfl

theorem cell23_7256825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7256825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256825 prefixEnd_7256825 := by exact prefixLift 7256825
  have htrace : WordTrace (prefixWord ++ tailWord_7256825) baseStart_7256825 baseEnd_7256825 := by
    simpa [prefixWord, tailWord_7256825, baseEnd_7256825] using wordTrace_append hprefix tailTrace_7256825
  have hstable : (prefixWord ++ tailWord_7256825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256825).length < 2 ^ (prefixWord ++ tailWord_7256825).sum := by decide
  have hdescent : baseEnd_7256825 < baseStart_7256825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256826 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2]
def baseStart_7256826 : Nat := 118140960795 + 7256826 * 2 ^ 59
def prefixEnd_7256826 : Nat := 4983230072969 + 3 ^ 40 * 7256826 * 2
def baseEnd_7256826 : Nat := 3726239764044329868601471

theorem tailTrace_7256826 : CollatzResearch.WordTrace tailWord_7256826 prefixEnd_7256826 3726239764044329868601471 := by
  unfold tailWord_7256826
  simp only [CollatzResearch.WordTrace]
  refine ⟨66169547101941561013711583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176452125605177496036564221 66169547101941561013711583)
  ·
    refine ⟨99254320652912341520567375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66169547101941561013711583 99254320652912341520567375)
    ·
      refine ⟨148881480979368512280851063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99254320652912341520567375 148881480979368512280851063)
      ·
        refine ⟨223322221469052768421276595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148881480979368512280851063 223322221469052768421276595)
        ·
          refine ⟨334983332203579152631914893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223322221469052768421276595 334983332203579152631914893)
          ·
            refine ⟨125618749576342182236968085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334983332203579152631914893 125618749576342182236968085)
            ·
              refine ⟨5888378886391039792357879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125618749576342182236968085 5888378886391039792357879)
              ·
                refine ⟨8832568329586559688536819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888378886391039792357879 8832568329586559688536819)
                ·
                  refine ⟨13248852494379839532805229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832568329586559688536819 13248852494379839532805229)
                  ·
                    refine ⟨4968319685392439824801961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13248852494379839532805229 4968319685392439824801961)
                    ·
                      refine ⟨3726239764044329868601471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968319685392439824801961 3726239764044329868601471)
                      ·
                        rfl

theorem cell23_7256826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_7256826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256826 prefixEnd_7256826 := by exact prefixLift 7256826
  have htrace : WordTrace (prefixWord ++ tailWord_7256826) baseStart_7256826 baseEnd_7256826 := by
    simpa [prefixWord, tailWord_7256826, baseEnd_7256826] using wordTrace_append hprefix tailTrace_7256826
  have hstable : (prefixWord ++ tailWord_7256826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256826).length < 2 ^ (prefixWord ++ tailWord_7256826).sum := by decide
  have hdescent : baseEnd_7256826 < baseStart_7256826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256850 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7256850 : Nat := 118140960795 + 7256850 * 2 ^ 59
def prefixEnd_7256850 : Nat := 4983230072969 + 3 ^ 40 * 7256850 * 2
def baseEnd_7256850 : Nat := 3726252087580037774701361

theorem tailTrace_7256850 : CollatzResearch.WordTrace tailWord_7256850 prefixEnd_7256850 3726252087580037774701361 := by
  unfold tailWord_7256850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66169765939919824038430001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176452709173119530769146669 66169765939919824038430001)
  ·
    refine ⟨49627324454939868028822501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66169765939919824038430001 49627324454939868028822501)
    ·
      refine ⟨9305123335301225255404219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49627324454939868028822501 9305123335301225255404219)
      ·
        refine ⟨13957685002951837883106329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305123335301225255404219 13957685002951837883106329)
        ·
          refine ⟨10468263752213878412329747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13957685002951837883106329 10468263752213878412329747)
          ·
            refine ⟨15702395628320817618494621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468263752213878412329747 15702395628320817618494621)
            ·
              refine ⟨5888398360620306606935483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15702395628320817618494621 5888398360620306606935483)
              ·
                refine ⟨8832597540930459910403225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888398360620306606935483 8832597540930459910403225)
                ·
                  refine ⟨6624448155697844932802419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8832597540930459910403225 6624448155697844932802419)
                  ·
                    refine ⟨9936672233546767399203629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624448155697844932802419 9936672233546767399203629)
                    ·
                      refine ⟨3726252087580037774701361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9936672233546767399203629 3726252087580037774701361)
                      ·
                        rfl

theorem cell23_7256850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7256850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256850 prefixEnd_7256850 := by exact prefixLift 7256850
  have htrace : WordTrace (prefixWord ++ tailWord_7256850) baseStart_7256850 baseEnd_7256850 := by
    simpa [prefixWord, tailWord_7256850, baseEnd_7256850] using wordTrace_append hprefix tailTrace_7256850
  have hstable : (prefixWord ++ tailWord_7256850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256850).length < 2 ^ (prefixWord ++ tailWord_7256850).sum := by decide
  have hdescent : baseEnd_7256850 < baseStart_7256850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7256915 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_7256915 : Nat := 118140960795 + 7256915 * 2 ^ 59
def prefixEnd_7256915 : Nat := 4983230072969 + 3 ^ 40 * 7256915 * 2
def baseEnd_7256915 : Nat := 3726285463822580020388561

theorem tailTrace_7256915 : CollatzResearch.WordTrace tailWord_7256915 prefixEnd_7256915 3726285463822580020388561 := by
  unfold tailWord_7256915
  simp only [CollatzResearch.WordTrace]
  refine ⟨264681434504443812254836199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176454289669629208169890799 264681434504443812254836199)
  ·
    refine ⟨397022151756665718382254299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264681434504443812254836199 397022151756665718382254299)
    ·
      refine ⟨595533227634998577573381449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397022151756665718382254299 595533227634998577573381449)
      ·
        refine ⟨446649920726248933180036087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595533227634998577573381449 446649920726248933180036087)
        ·
          refine ⟨669974881089373399770054131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446649920726248933180036087 669974881089373399770054131)
          ·
            refine ⟨1004962321634060099655081197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669974881089373399770054131 1004962321634060099655081197)
            ·
              refine ⟨376860870612772537370655449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004962321634060099655081197 376860870612772537370655449)
              ·
                refine ⟨282645652959579403027991587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376860870612772537370655449 282645652959579403027991587)
                ·
                  refine ⟨423968479439369104541987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282645652959579403027991587 423968479439369104541987381)
                  ·
                    refine ⟨39747044947440853550811317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 423968479439369104541987381 39747044947440853550811317)
                    ·
                      refine ⟨3726285463822580020388561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39747044947440853550811317 3726285463822580020388561)
                      ·
                        rfl

theorem cell23_7256915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_7256915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7256915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7256915 prefixEnd_7256915 := by exact prefixLift 7256915
  have htrace : WordTrace (prefixWord ++ tailWord_7256915) baseStart_7256915 baseEnd_7256915 := by
    simpa [prefixWord, tailWord_7256915, baseEnd_7256915] using wordTrace_append hprefix tailTrace_7256915
  have hstable : (prefixWord ++ tailWord_7256915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7256915).length < 2 ^ (prefixWord ++ tailWord_7256915).sum := by decide
  have hdescent : baseEnd_7256915 < baseStart_7256915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7256915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257013 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_7257013 : Nat := 118140960795 + 7257013 * 2 ^ 59
def prefixEnd_7257013 : Nat := 4983230072969 + 3 ^ 40 * 7257013 * 2
def baseEnd_7257013 : Nat := 3726335784926720636963111

theorem tailTrace_7257013 : CollatzResearch.WordTrace tailWord_7257013 prefixEnd_7257013 3726335784926720636963111 := by
  unfold tailWord_7257013
  simp only [CollatzResearch.WordTrace]
  refine ⟨264685008858088774991903693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176456672572059183327935795 264685008858088774991903693)
  ·
    refine ⟨99256878321783290621963885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264685008858088774991903693 99256878321783290621963885)
    ·
      refine ⟨37221329370668733983236457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99256878321783290621963885 37221329370668733983236457)
      ·
        refine ⟨27915997028001550487427343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37221329370668733983236457 27915997028001550487427343)
        ·
          refine ⟨41873995542002325731141015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27915997028001550487427343 41873995542002325731141015)
          ·
            refine ⟨62810993313003488596711523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41873995542002325731141015 62810993313003488596711523)
            ·
              refine ⟨94216489969505232895067285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62810993313003488596711523 94216489969505232895067285)
              ·
                refine ⟨4416397967320557791956279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94216489969505232895067285 4416397967320557791956279)
                ·
                  refine ⟨6624596950980836687934419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416397967320557791956279 6624596950980836687934419)
                  ·
                    refine ⟨9936895426471255031901629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624596950980836687934419 9936895426471255031901629)
                    ·
                      refine ⟨3726335784926720636963111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9936895426471255031901629 3726335784926720636963111)
                      ·
                        rfl

theorem cell23_7257013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_7257013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257013 prefixEnd_7257013 := by exact prefixLift 7257013
  have htrace : WordTrace (prefixWord ++ tailWord_7257013) baseStart_7257013 baseEnd_7257013 := by
    simpa [prefixWord, tailWord_7257013, baseEnd_7257013] using wordTrace_append hprefix tailTrace_7257013
  have hstable : (prefixWord ++ tailWord_7257013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257013).length < 2 ^ (prefixWord ++ tailWord_7257013).sum := by decide
  have hdescent : baseEnd_7257013 < baseStart_7257013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257036 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7257036 : Nat := 118140960795 + 7257036 * 2 ^ 59
def prefixEnd_7257036 : Nat := 4983230072969 + 3 ^ 40 * 7257036 * 2
def baseEnd_7257036 : Nat := 3726347594981774046975505

theorem tailTrace_7257036 : CollatzResearch.WordTrace tailWord_7257036 prefixEnd_7257036 3726347594981774046975505 := by
  unfold tailWord_7257036
  simp only [CollatzResearch.WordTrace]
  refine ⟨132342923868502724959995481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176457231824670299946660641 132342923868502724959995481)
  ·
    refine ⟨99257192901377043719996611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132342923868502724959995481 99257192901377043719996611)
    ·
      refine ⟨148885789352065565579994917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99257192901377043719996611 148885789352065565579994917)
      ·
        refine ⟨27916085503512293546249047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148885789352065565579994917 27916085503512293546249047)
        ·
          refine ⟨41874128255268440319373571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27916085503512293546249047 41874128255268440319373571)
          ·
            refine ⟨62811192382902660479060357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41874128255268440319373571 62811192382902660479060357)
            ·
              refine ⟨11777098571794248839823817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62811192382902660479060357 11777098571794248839823817)
              ·
                refine ⟨8832823928845686629867863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11777098571794248839823817 8832823928845686629867863)
                ·
                  refine ⟨13249235893268529944801795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832823928845686629867863 13249235893268529944801795)
                  ·
                    refine ⟨19873853839902794917202693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13249235893268529944801795 19873853839902794917202693)
                    ·
                      refine ⟨3726347594981774046975505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19873853839902794917202693 3726347594981774046975505)
                      ·
                        rfl

theorem cell23_7257036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7257036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257036 prefixEnd_7257036 := by exact prefixLift 7257036
  have htrace : WordTrace (prefixWord ++ tailWord_7257036) baseStart_7257036 baseEnd_7257036 := by
    simpa [prefixWord, tailWord_7257036, baseEnd_7257036] using wordTrace_append hprefix tailTrace_7257036
  have hstable : (prefixWord ++ tailWord_7257036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257036).length < 2 ^ (prefixWord ++ tailWord_7257036).sum := by decide
  have hdescent : baseEnd_7257036 < baseStart_7257036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257072 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_7257072 : Nat := 118140960795 + 7257072 * 2 ^ 59
def prefixEnd_7257072 : Nat := 4983230072969 + 3 ^ 40 * 7257072 * 2
def baseEnd_7257072 : Nat := 1242122026761778635375113

theorem tailTrace_7257072 : CollatzResearch.WordTrace tailWord_7257072 prefixEnd_7257072 1242122026761778635375113 := by
  unfold tailWord_7257072
  simp only [CollatzResearch.WordTrace]
  refine ⟨132343580382437514034150735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176458107176583352045534313 132343580382437514034150735)
  ·
    refine ⟨198515370573656271051226103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132343580382437514034150735 198515370573656271051226103)
    ·
      refine ⟨297773055860484406576839155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198515370573656271051226103 297773055860484406576839155)
      ·
        refine ⟨446659583790726609865258733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297773055860484406576839155 446659583790726609865258733)
        ·
          refine ⟨167497343921522478699472025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446659583790726609865258733 167497343921522478699472025)
          ·
            refine ⟨125623007941141859024604019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167497343921522478699472025 125623007941141859024604019)
            ·
              refine ⟨188434511911712788536906029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125623007941141859024604019 188434511911712788536906029)
              ·
                refine ⟨70662941966892295701339761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188434511911712788536906029 70662941966892295701339761)
                ·
                  refine ⟨52997206475169221776004821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70662941966892295701339761 52997206475169221776004821)
                  ·
                    refine ⟨1242122026761778635375113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52997206475169221776004821 1242122026761778635375113)
                    ·
                      rfl

theorem cell23_7257072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_7257072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257072 prefixEnd_7257072 := by exact prefixLift 7257072
  have htrace : WordTrace (prefixWord ++ tailWord_7257072) baseStart_7257072 baseEnd_7257072 := by
    simpa [prefixWord, tailWord_7257072, baseEnd_7257072] using wordTrace_append hprefix tailTrace_7257072
  have hstable : (prefixWord ++ tailWord_7257072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257072).length < 2 ^ (prefixWord ++ tailWord_7257072).sum := by decide
  have hdescent : baseEnd_7257072 < baseStart_7257072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257090 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7257090 : Nat := 118140960795 + 7257090 * 2 ^ 59
def prefixEnd_7257090 : Nat := 4983230072969 + 3 ^ 40 * 7257090 * 2
def baseEnd_7257090 : Nat := 3726375322937116835700257

theorem tailTrace_7257090 : CollatzResearch.WordTrace tailWord_7257090 prefixEnd_7257090 3726375322937116835700257 := by
  unfold tailWord_7257090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66171954319702454285614181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176458544852539878094971149 66171954319702454285614181)
  ·
    refine ⟨12407241434944210178552659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66171954319702454285614181 12407241434944210178552659)
    ·
      refine ⟨18610862152416315267828989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407241434944210178552659 18610862152416315267828989)
      ·
        refine ⟨6979073307156118225435871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18610862152416315267828989 6979073307156118225435871)
        ·
          refine ⟨10468609960734177338153807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979073307156118225435871 10468609960734177338153807)
          ·
            refine ⟨15702914941101266007230711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468609960734177338153807 15702914941101266007230711)
            ·
              refine ⟨23554372411651899010846067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15702914941101266007230711 23554372411651899010846067)
              ·
                refine ⟨35331558617477848516269101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23554372411651899010846067 35331558617477848516269101)
                ·
                  refine ⟨13249334481554193193600913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35331558617477848516269101 13249334481554193193600913)
                  ·
                    refine ⟨9937000861165644895200685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13249334481554193193600913 9937000861165644895200685)
                    ·
                      refine ⟨3726375322937116835700257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9937000861165644895200685 3726375322937116835700257)
                      ·
                        rfl

theorem cell23_7257090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7257090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257090 prefixEnd_7257090 := by exact prefixLift 7257090
  have htrace : WordTrace (prefixWord ++ tailWord_7257090) baseStart_7257090 baseEnd_7257090 := by
    simpa [prefixWord, tailWord_7257090, baseEnd_7257090] using wordTrace_append hprefix tailTrace_7257090
  have hstable : (prefixWord ++ tailWord_7257090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257090).length < 2 ^ (prefixWord ++ tailWord_7257090).sum := by decide
  have hdescent : baseEnd_7257090 < baseStart_7257090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257149 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 9]
def baseStart_7257149 : Nat := 118140960795 + 7257149 * 2 ^ 59
def prefixEnd_7257149 : Nat := 4983230072969 + 3 ^ 40 * 7257149 * 2
def baseEnd_7257149 : Nat := 414045068699525789429165

theorem tailTrace_7257149 : CollatzResearch.WordTrace tailWord_7257149 prefixEnd_7257149 414045068699525789429165 := by
  unfold tailWord_7257149
  simp only [CollatzResearch.WordTrace]
  refine ⟨264689969185596070218854501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176459979457064046812569667 264689969185596070218854501)
  ·
    refine ⟨49629369222299263166035219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264689969185596070218854501 49629369222299263166035219)
    ·
      refine ⟨74444053833448894749052829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49629369222299263166035219 74444053833448894749052829)
      ·
        refine ⟨27916520187543335530894811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74444053833448894749052829 27916520187543335530894811)
        ·
          refine ⟨41874780281315003296342217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27916520187543335530894811 41874780281315003296342217)
          ·
            refine ⟨31406085210986252472256663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41874780281315003296342217 31406085210986252472256663)
            ·
              refine ⟨47109127816479378708384995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31406085210986252472256663 47109127816479378708384995)
              ·
                refine ⟨70663691724719068062577493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47109127816479378708384995 70663691724719068062577493)
                ·
                  refine ⟨414045068699525789429165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70663691724719068062577493 414045068699525789429165)
                  ·
                    rfl

theorem cell23_7257149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_7257149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257149 prefixEnd_7257149 := by exact prefixLift 7257149
  have htrace : WordTrace (prefixWord ++ tailWord_7257149) baseStart_7257149 baseEnd_7257149 := by
    simpa [prefixWord, tailWord_7257149, baseEnd_7257149] using wordTrace_append hprefix tailTrace_7257149
  have hstable : (prefixWord ++ tailWord_7257149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257149).length < 2 ^ (prefixWord ++ tailWord_7257149).sum := by decide
  have hdescent : baseEnd_7257149 < baseStart_7257149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257189 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7257189 : Nat := 118140960795 + 7257189 * 2 ^ 59
def prefixEnd_7257189 : Nat := 4983230072969 + 3 ^ 40 * 7257189 * 2
def baseEnd_7257189 : Nat := 3726426157521911948362301

theorem tailTrace_7257189 : CollatzResearch.WordTrace tailWord_7257189 prefixEnd_7257189 3726426157521911948362301 := by
  unfold tailWord_7257189
  simp only [CollatzResearch.WordTrace]
  refine ⟨264691428105451157050310621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176460952070300771366873747 264691428105451157050310621)
  ·
    refine ⟨99259285539544183893866483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264691428105451157050310621 99259285539544183893866483)
    ·
      refine ⟨148888928309316275840799725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99259285539544183893866483 148888928309316275840799725)
      ·
        refine ⟨55833348115993603440299897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148888928309316275840799725 55833348115993603440299897)
        ·
          refine ⟨41875011086995202580224923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55833348115993603440299897 41875011086995202580224923)
          ·
            refine ⟨62812516630492803870337385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41875011086995202580224923 62812516630492803870337385)
            ·
              refine ⟨47109387472869602902753039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62812516630492803870337385 47109387472869602902753039)
              ·
                refine ⟨70664081209304404354129559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47109387472869602902753039 70664081209304404354129559)
                ·
                  refine ⟨105996121813956606531194339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70664081209304404354129559 105996121813956606531194339)
                  ·
                    refine ⟨158994182720934909796791509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105996121813956606531194339 158994182720934909796791509)
                    ·
                      refine ⟨3726426157521911948362301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158994182720934909796791509 3726426157521911948362301)
                      ·
                        rfl

theorem cell23_7257189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7257189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257189 prefixEnd_7257189 := by exact prefixLift 7257189
  have htrace : WordTrace (prefixWord ++ tailWord_7257189) baseStart_7257189 baseEnd_7257189 := by
    simpa [prefixWord, tailWord_7257189, baseEnd_7257189] using wordTrace_append hprefix tailTrace_7257189
  have hstable : (prefixWord ++ tailWord_7257189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257189).length < 2 ^ (prefixWord ++ tailWord_7257189).sum := by decide
  have hdescent : baseEnd_7257189 < baseStart_7257189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257199 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_7257199 : Nat := 118140960795 + 7257199 * 2 ^ 59
def prefixEnd_7257199 : Nat := 4983230072969 + 3 ^ 40 * 7257199 * 2
def baseEnd_7257199 : Nat := 3726431292328456909237255

theorem tailTrace_7257199 : CollatzResearch.WordTrace tailWord_7257199 prefixEnd_7257199 3726431292328456909237255 := by
  unfold tailWord_7257199
  simp only [CollatzResearch.WordTrace]
  refine ⟨264691792835414928758174651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176461195223609952505449767 264691792835414928758174651)
  ·
    refine ⟨397037689253122393137261977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264691792835414928758174651 397037689253122393137261977)
    ·
      refine ⟨297778266939841794852946483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397037689253122393137261977 297778266939841794852946483)
      ·
        refine ⟨446667400409762692279419725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297778266939841794852946483 446667400409762692279419725)
        ·
          refine ⟨167500275153661009604782397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446667400409762692279419725 167500275153661009604782397)
          ·
            refine ⟨62812603182622878601793399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167500275153661009604782397 62812603182622878601793399)
            ·
              refine ⟨94218904773934317902690099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62812603182622878601793399 94218904773934317902690099)
              ·
                refine ⟨141328357160901476854035149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94218904773934317902690099 141328357160901476854035149)
                ·
                  refine ⟨52998133935338053820263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141328357160901476854035149 52998133935338053820263181)
                  ·
                    refine ⟨19874300225751770182598693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52998133935338053820263181 19874300225751770182598693)
                    ·
                      refine ⟨3726431292328456909237255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19874300225751770182598693 3726431292328456909237255)
                      ·
                        rfl

theorem cell23_7257199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_7257199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257199 prefixEnd_7257199 := by exact prefixLift 7257199
  have htrace : WordTrace (prefixWord ++ tailWord_7257199) baseStart_7257199 baseEnd_7257199 := by
    simpa [prefixWord, tailWord_7257199, baseEnd_7257199] using wordTrace_append hprefix tailTrace_7257199
  have hstable : (prefixWord ++ tailWord_7257199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257199).length < 2 ^ (prefixWord ++ tailWord_7257199).sum := by decide
  have hdescent : baseEnd_7257199 < baseStart_7257199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257216 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2]
def baseStart_7257216 : Nat := 118140960795 + 7257216 * 2 ^ 59
def prefixEnd_7257216 : Nat := 4983230072969 + 3 ^ 40 * 7257216 * 2
def baseEnd_7257216 : Nat := 3726440021499583342724677

theorem tailTrace_7257216 : CollatzResearch.WordTrace tailWord_7257216 prefixEnd_7257216 3726440021499583342724677 := by
  unfold tailWord_7257216
  simp only [CollatzResearch.WordTrace]
  refine ⟨132346206438176670330771751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176461608584235560441029001 132346206438176670330771751)
  ·
    refine ⟨198519309657265005496157627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132346206438176670330771751 198519309657265005496157627)
    ·
      refine ⟨297778964485897508244236441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198519309657265005496157627 297778964485897508244236441)
      ·
        refine ⟨223334223364423131183177331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297778964485897508244236441 223334223364423131183177331)
        ·
          refine ⟨335001335046634696774765997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223334223364423131183177331 335001335046634696774765997)
          ·
            refine ⟨125625500642488011290537249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335001335046634696774765997 125625500642488011290537249)
            ·
              refine ⟨94219125481866008467902937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125625500642488011290537249 94219125481866008467902937)
              ·
                refine ⟨70664344111399506350927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94219125481866008467902937 70664344111399506350927203)
                ·
                  refine ⟨105996516167099259526390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70664344111399506350927203 105996516167099259526390805)
                  ·
                    refine ⟨4968586695332777790299569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105996516167099259526390805 4968586695332777790299569)
                    ·
                      refine ⟨3726440021499583342724677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968586695332777790299569 3726440021499583342724677)
                      ·
                        rfl

theorem cell23_7257216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_7257216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257216 prefixEnd_7257216 := by exact prefixLift 7257216
  have htrace : WordTrace (prefixWord ++ tailWord_7257216) baseStart_7257216 baseEnd_7257216 := by
    simpa [prefixWord, tailWord_7257216, baseEnd_7257216] using wordTrace_append hprefix tailTrace_7257216
  have hstable : (prefixWord ++ tailWord_7257216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257216).length < 2 ^ (prefixWord ++ tailWord_7257216).sum := by decide
  have hdescent : baseEnd_7257216 < baseStart_7257216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257294 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_7257294 : Nat := 118140960795 + 7257294 * 2 ^ 59
def prefixEnd_7257294 : Nat := 4983230072969 + 3 ^ 40 * 7257294 * 2
def baseEnd_7257294 : Nat := 1242160024330211345849773

theorem tailTrace_7257294 : CollatzResearch.WordTrace tailWord_7257294 prefixEnd_7257294 1242160024330211345849773 := by
  unfold tailWord_7257294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086907221258844997860367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176463505180047173321921957 33086907221258844997860367)
  ·
    refine ⟨49630360831888267496790551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086907221258844997860367 49630360831888267496790551)
    ·
      refine ⟨74445541247832401245185827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49630360831888267496790551 74445541247832401245185827)
      ·
        refine ⟨111668311871748601867778741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74445541247832401245185827 111668311871748601867778741)
        ·
          refine ⟨10468904237976431425104257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111668311871748601867778741 10468904237976431425104257)
          ·
            refine ⟨7851678178482323568828193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468904237976431425104257 7851678178482323568828193)
            ·
              refine ⟨5888758633861742676621145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7851678178482323568828193 5888758633861742676621145)
              ·
                refine ⟨4416568975396307007465859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888758633861742676621145 4416568975396307007465859)
                ·
                  refine ⟨6624853463094460511198789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416568975396307007465859 6624853463094460511198789)
                  ·
                    refine ⟨1242160024330211345849773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6624853463094460511198789 1242160024330211345849773)
                    ·
                      rfl

theorem cell23_7257294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_7257294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257294 prefixEnd_7257294 := by exact prefixLift 7257294
  have htrace : WordTrace (prefixWord ++ tailWord_7257294) baseStart_7257294 baseEnd_7257294 := by
    simpa [prefixWord, tailWord_7257294, baseEnd_7257294] using wordTrace_append hprefix tailTrace_7257294
  have hstable : (prefixWord ++ tailWord_7257294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257294).length < 2 ^ (prefixWord ++ tailWord_7257294).sum := by decide
  have hdescent : baseEnd_7257294 < baseStart_7257294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257316 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_7257316 : Nat := 118140960795 + 7257316 * 2 ^ 59
def prefixEnd_7257316 : Nat := 4983230072969 + 3 ^ 40 * 7257316 * 2
def baseEnd_7257316 : Nat := 1242163789855010983824739

theorem tailTrace_7257316 : CollatzResearch.WordTrace tailWord_7257316 prefixEnd_7257316 1242163789855010983824739 := by
  unfold tailWord_7257316
  simp only [CollatzResearch.WordTrace]
  refine ⟨132348030087995528870091901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176464040117327371826789201 132348030087995528870091901)
  ·
    refine ⟨49630511282998323326284463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132348030087995528870091901 49630511282998323326284463)
    ·
      refine ⟨74445766924497484989426695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49630511282998323326284463 74445766924497484989426695)
      ·
        refine ⟨111668650386746227484140043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74445766924497484989426695 111668650386746227484140043)
        ·
          refine ⟨167502975580119341226210065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111668650386746227484140043 167502975580119341226210065)
          ·
            refine ⟨125627231685089505919657549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167502975580119341226210065 125627231685089505919657549)
            ·
              refine ⟨47110211881908564719871581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125627231685089505919657549 47110211881908564719871581)
              ·
                refine ⟨17666329455715711769951843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47110211881908564719871581 17666329455715711769951843)
                ·
                  refine ⟨26499494183573567654927765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17666329455715711769951843 26499494183573567654927765)
                  ·
                    refine ⟨1242163789855010983824739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26499494183573567654927765 1242163789855010983824739)
                    ·
                      rfl

theorem cell23_7257316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_7257316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257316 prefixEnd_7257316 := by exact prefixLift 7257316
  have htrace : WordTrace (prefixWord ++ tailWord_7257316) baseStart_7257316 baseEnd_7257316 := by
    simpa [prefixWord, tailWord_7257316, baseEnd_7257316] using wordTrace_append hprefix tailTrace_7257316
  have hstable : (prefixWord ++ tailWord_7257316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257316).length < 2 ^ (prefixWord ++ tailWord_7257316).sum := by decide
  have hdescent : baseEnd_7257316 < baseStart_7257316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257327 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 2, 3, 2]
def baseStart_7257327 : Nat := 118140960795 + 7257327 * 2 ^ 59
def prefixEnd_7257327 : Nat := 4983230072969 + 3 ^ 40 * 7257327 * 2
def baseEnd_7257327 : Nat := 3726497017852232408436667

theorem tailTrace_7257327 : CollatzResearch.WordTrace tailWord_7257327 prefixEnd_7257327 3726497017852232408436667 := by
  unfold tailWord_7257327
  simp only [CollatzResearch.WordTrace]
  refine ⟨264696461378951206618834235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176464307585967471079222823 264696461378951206618834235)
  ·
    refine ⟨397044692068426809928251353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264696461378951206618834235 397044692068426809928251353)
    ·
      refine ⟨297783519051320107446188515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397044692068426809928251353 297783519051320107446188515)
      ·
        refine ⟨446675278576980161169282773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297783519051320107446188515 446675278576980161169282773)
        ·
          refine ⟨10468951841647972527405065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 446675278576980161169282773 10468951841647972527405065)
          ·
            refine ⟨7851713881235979395553799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468951841647972527405065 7851713881235979395553799)
            ·
              refine ⟨11777570821853969093330699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851713881235979395553799 11777570821853969093330699)
              ·
                refine ⟨17666356232780953639996049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777570821853969093330699 17666356232780953639996049)
                ·
                  refine ⟨13249767174585715229997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17666356232780953639996049 13249767174585715229997037)
                  ·
                    refine ⟨4968662690469643211248889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13249767174585715229997037 4968662690469643211248889)
                    ·
                      refine ⟨3726497017852232408436667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968662690469643211248889 3726497017852232408436667)
                      ·
                        rfl

theorem cell23_7257327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 3, 2].length) (baseStart_7257327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257327 prefixEnd_7257327 := by exact prefixLift 7257327
  have htrace : WordTrace (prefixWord ++ tailWord_7257327) baseStart_7257327 baseEnd_7257327 := by
    simpa [prefixWord, tailWord_7257327, baseEnd_7257327] using wordTrace_append hprefix tailTrace_7257327
  have hstable : (prefixWord ++ tailWord_7257327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257327).length < 2 ^ (prefixWord ++ tailWord_7257327).sum := by decide
  have hdescent : baseEnd_7257327 < baseStart_7257327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257340 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_7257340 : Nat := 118140960795 + 7257340 * 2 ^ 59
def prefixEnd_7257340 : Nat := 4983230072969 + 3 ^ 40 * 7257340 * 2
def baseEnd_7257340 : Nat := 3726503693100740857574107

theorem tailTrace_7257340 : CollatzResearch.WordTrace tailWord_7257340 prefixEnd_7257340 3726503693100740857574107 := by
  unfold tailWord_7257340
  simp only [CollatzResearch.WordTrace]
  refine ⟨132348467763952054919528737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176464623685269406559371649 132348467763952054919528737)
  ·
    refine ⟨99261350822964041189646553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132348467763952054919528737 99261350822964041189646553)
    ·
      refine ⟨74446013117223030892234915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99261350822964041189646553 74446013117223030892234915)
      ·
        refine ⟨111669019675834546338352373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74446013117223030892234915 111669019675834546338352373)
        ·
          refine ⟨10468970594609488719220535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111669019675834546338352373 10468970594609488719220535)
          ·
            refine ⟨15703455891914233078830803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468970594609488719220535 15703455891914233078830803)
            ·
              refine ⟨23555183837871349618246205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15703455891914233078830803 23555183837871349618246205)
              ·
                refine ⟨8833193939201756106842327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23555183837871349618246205 8833193939201756106842327)
                ·
                  refine ⟨13249790908802634160263491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833193939201756106842327 13249790908802634160263491)
                  ·
                    refine ⟨19874686363203951240395237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13249790908802634160263491 19874686363203951240395237)
                    ·
                      refine ⟨3726503693100740857574107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19874686363203951240395237 3726503693100740857574107)
                      ·
                        rfl

theorem cell23_7257340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_7257340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257340 prefixEnd_7257340 := by exact prefixLift 7257340
  have htrace : WordTrace (prefixWord ++ tailWord_7257340) baseStart_7257340 baseEnd_7257340 := by
    simpa [prefixWord, tailWord_7257340, baseEnd_7257340] using wordTrace_append hprefix tailTrace_7257340
  have hstable : (prefixWord ++ tailWord_7257340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257340).length < 2 ^ (prefixWord ++ tailWord_7257340).sum := by decide
  have hdescent : baseEnd_7257340 < baseStart_7257340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257370 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_7257370 : Nat := 118140960795 + 7257370 * 2 ^ 59
def prefixEnd_7257370 : Nat := 4983230072969 + 3 ^ 40 * 7257370 * 2
def baseEnd_7257370 : Nat := 3726519097520375740198969

theorem tailTrace_7257370 : CollatzResearch.WordTrace tailWord_7257370 prefixEnd_7257370 3726519097520375740198969 := by
  unfold tailWord_7257370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66174507429448856240662391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176465353145196949975099709 66174507429448856240662391)
  ·
    refine ⟨99261761144173284360993587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66174507429448856240662391 99261761144173284360993587)
    ·
      refine ⟨148892641716259926541490381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99261761144173284360993587 148892641716259926541490381)
      ·
        refine ⟨55834740643597472453058893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148892641716259926541490381 55834740643597472453058893)
        ·
          refine ⟨20938027741349052169897085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55834740643597472453058893 20938027741349052169897085)
          ·
            refine ⟨7851760403005894563711407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20938027741349052169897085 7851760403005894563711407)
            ·
              refine ⟨11777640604508841845567111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851760403005894563711407 11777640604508841845567111)
              ·
                refine ⟨17666460906763262768350667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777640604508841845567111 17666460906763262768350667)
                ·
                  refine ⟨26499691360144894152526001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17666460906763262768350667 26499691360144894152526001)
                  ·
                    refine ⟨19874768520108670614394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26499691360144894152526001 19874768520108670614394501)
                    ·
                      refine ⟨3726519097520375740198969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19874768520108670614394501 3726519097520375740198969)
                      ·
                        rfl

theorem cell23_7257370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_7257370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257370 prefixEnd_7257370 := by exact prefixLift 7257370
  have htrace : WordTrace (prefixWord ++ tailWord_7257370) baseStart_7257370 baseEnd_7257370 := by
    simpa [prefixWord, tailWord_7257370, baseEnd_7257370] using wordTrace_append hprefix tailTrace_7257370
  have hstable : (prefixWord ++ tailWord_7257370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257370).length < 2 ^ (prefixWord ++ tailWord_7257370).sum := by decide
  have hdescent : baseEnd_7257370 < baseStart_7257370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257374 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7257374 : Nat := 118140960795 + 7257374 * 2 ^ 59
def prefixEnd_7257374 : Nat := 4983230072969 + 3 ^ 40 * 7257374 * 2
def baseEnd_7257374 : Nat := 3726521151442993724548951

theorem tailTrace_7257374 : CollatzResearch.WordTrace tailWord_7257374 prefixEnd_7257374 3726521151442993724548951 := by
  unfold tailWord_7257374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087271951222616705724397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176465450406520622430530117 33087271951222616705724397)
  ·
    refine ⟨12407726981708481264646649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33087271951222616705724397 12407726981708481264646649)
    ·
      refine ⟨9305795236281360948484987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12407726981708481264646649 9305795236281360948484987)
      ·
        refine ⟨13958692854422041422727481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305795236281360948484987 13958692854422041422727481)
        ·
          refine ⟨10469019640816531067045611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958692854422041422727481 10469019640816531067045611)
          ·
            refine ⟨15703529461224796600568417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469019640816531067045611 15703529461224796600568417)
            ·
              refine ⟨11777647095918597450426313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15703529461224796600568417 11777647095918597450426313)
              ·
                refine ⟨8833235321938948087819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11777647095918597450426313 8833235321938948087819735)
                ·
                  refine ⟨13249852982908422131729603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833235321938948087819735 13249852982908422131729603)
                  ·
                    refine ⟨19874779474362633197594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13249852982908422131729603 19874779474362633197594405)
                    ·
                      refine ⟨3726521151442993724548951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19874779474362633197594405 3726521151442993724548951)
                      ·
                        rfl

theorem cell23_7257374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7257374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257374 prefixEnd_7257374 := by exact prefixLift 7257374
  have htrace : WordTrace (prefixWord ++ tailWord_7257374) baseStart_7257374 baseEnd_7257374 := by
    simpa [prefixWord, tailWord_7257374, baseEnd_7257374] using wordTrace_append hprefix tailTrace_7257374
  have hstable : (prefixWord ++ tailWord_7257374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257374).length < 2 ^ (prefixWord ++ tailWord_7257374).sum := by decide
  have hdescent : baseEnd_7257374 < baseStart_7257374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257416 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7257416 : Nat := 118140960795 + 7257416 * 2 ^ 59
def prefixEnd_7257416 : Nat := 4983230072969 + 3 ^ 40 * 7257416 * 2
def baseEnd_7257416 : Nat := 3726542717630482560223757

theorem tailTrace_7257416 : CollatzResearch.WordTrace tailWord_7257416 prefixEnd_7257416 3726542717630482560223757 := by
  unfold tailWord_7257416
  simp only [CollatzResearch.WordTrace]
  refine ⟨132349853737814387409412051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176466471650419183212549401 132349853737814387409412051)
  ·
    refine ⟨198524780606721581114118077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132349853737814387409412051 198524780606721581114118077)
    ·
      refine ⟨74446792727520592917794279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198524780606721581114118077 74446792727520592917794279)
      ·
        refine ⟨111670189091280889376691419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74446792727520592917794279 111670189091280889376691419)
        ·
          refine ⟨167505283636921334065037129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111670189091280889376691419 167505283636921334065037129)
          ·
            refine ⟨125628962727691000548777847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167505283636921334065037129 125628962727691000548777847)
            ·
              refine ⟨188443444091536500823166771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125628962727691000548777847 188443444091536500823166771)
              ·
                refine ⟨282665166137304751234750157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188443444091536500823166771 282665166137304751234750157)
                ·
                  refine ⟨105999437301489281713031309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282665166137304751234750157 105999437301489281713031309)
                  ·
                    refine ⟨39749788988058480642386741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105999437301489281713031309 39749788988058480642386741)
                    ·
                      refine ⟨3726542717630482560223757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39749788988058480642386741 3726542717630482560223757)
                      ·
                        rfl

theorem cell23_7257416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7257416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257416 prefixEnd_7257416 := by exact prefixLift 7257416
  have htrace : WordTrace (prefixWord ++ tailWord_7257416) baseStart_7257416 baseEnd_7257416 := by
    simpa [prefixWord, tailWord_7257416, baseEnd_7257416] using wordTrace_append hprefix tailTrace_7257416
  have hstable : (prefixWord ++ tailWord_7257416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257416).length < 2 ^ (prefixWord ++ tailWord_7257416).sum := by decide
  have hdescent : baseEnd_7257416 < baseStart_7257416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257447 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_7257447 : Nat := 118140960795 + 7257447 * 2 ^ 59
def prefixEnd_7257447 : Nat := 4983230072969 + 3 ^ 40 * 7257447 * 2
def baseEnd_7257447 : Nat := 3726558635530771938936115

theorem tailTrace_7257447 : CollatzResearch.WordTrace tailWord_7257447 prefixEnd_7257447 3726558635530771938936115 := by
  unfold tailWord_7257447
  simp only [CollatzResearch.WordTrace]
  refine ⟨264700838138516467113202595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176467225425677644742135063 264700838138516467113202595)
  ·
    refine ⟨397051257207774700669803893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264700838138516467113202595 397051257207774700669803893)
    ·
      refine ⟨37223555363228878187794115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397051257207774700669803893 37223555363228878187794115)
      ·
        refine ⟨55835333044843317281691173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37223555363228878187794115 55835333044843317281691173)
        ·
          refine ⟨10469124945908121990317095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55835333044843317281691173 10469124945908121990317095)
          ·
            refine ⟨15703687418862182985475643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469124945908121990317095 15703687418862182985475643)
            ·
              refine ⟨23555531128293274478213465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15703687418862182985475643 23555531128293274478213465)
              ·
                refine ⟨17666648346219955858660099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23555531128293274478213465 17666648346219955858660099)
                ·
                  refine ⟨26499972519329933787990149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17666648346219955858660099 26499972519329933787990149)
                  ·
                    refine ⟨4968744847374362585248153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26499972519329933787990149 4968744847374362585248153)
                    ·
                      refine ⟨3726558635530771938936115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968744847374362585248153 3726558635530771938936115)
                      ·
                        rfl

theorem cell23_7257447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_7257447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257447 prefixEnd_7257447 := by exact prefixLift 7257447
  have htrace : WordTrace (prefixWord ++ tailWord_7257447) baseStart_7257447 baseEnd_7257447 := by
    simpa [prefixWord, tailWord_7257447, baseEnd_7257447] using wordTrace_append hprefix tailTrace_7257447
  have hstable : (prefixWord ++ tailWord_7257447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257447).length < 2 ^ (prefixWord ++ tailWord_7257447).sum := by decide
  have hdescent : baseEnd_7257447 < baseStart_7257447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257463 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_7257463 : Nat := 118140960795 + 7257463 * 2 ^ 59
def prefixEnd_7257463 : Nat := 4983230072969 + 3 ^ 40 * 7257463 * 2
def baseEnd_7257463 : Nat := 3726566851221243876336041

theorem tailTrace_7257463 : CollatzResearch.WordTrace tailWord_7257463 prefixEnd_7257463 3726566851221243876336041 := by
  unfold tailWord_7257463
  simp only [CollatzResearch.WordTrace]
  refine ⟨264701421706458501845785043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176467614470972334563856695 264701421706458501845785043)
  ·
    refine ⟨397052132559687752768677565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264701421706458501845785043 397052132559687752768677565)
    ·
      refine ⟨148894549709882907288254087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397052132559687752768677565 148894549709882907288254087)
      ·
        refine ⟨223341824564824360932381131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148894549709882907288254087 223341824564824360932381131)
        ·
          refine ⟨335012736847236541398571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223341824564824360932381131 335012736847236541398571697)
          ·
            refine ⟨251259552635427406048928773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335012736847236541398571697 251259552635427406048928773)
            ·
              refine ⟨47111166119142638634174145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251259552635427406048928773 47111166119142638634174145)
              ·
                refine ⟨35333374589356978975630609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47111166119142638634174145 35333374589356978975630609)
                ·
                  refine ⟨26500030942017734231722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35333374589356978975630609 26500030942017734231722957)
                  ·
                    refine ⟨9937511603256650336896109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26500030942017734231722957 9937511603256650336896109)
                    ·
                      refine ⟨3726566851221243876336041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9937511603256650336896109 3726566851221243876336041)
                      ·
                        rfl

theorem cell23_7257463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_7257463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257463 prefixEnd_7257463 := by exact prefixLift 7257463
  have htrace : WordTrace (prefixWord ++ tailWord_7257463) baseStart_7257463 baseEnd_7257463 := by
    simpa [prefixWord, tailWord_7257463, baseEnd_7257463] using wordTrace_append hprefix tailTrace_7257463
  have hstable : (prefixWord ++ tailWord_7257463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257463).length < 2 ^ (prefixWord ++ tailWord_7257463).sum := by decide
  have hdescent : baseEnd_7257463 < baseStart_7257463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257480 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_7257480 : Nat := 118140960795 + 7257480 * 2 ^ 59
def prefixEnd_7257480 : Nat := 4983230072969 + 3 ^ 40 * 7257480 * 2
def baseEnd_7257480 : Nat := 3726575580392370309823463

theorem tailTrace_7257480 : CollatzResearch.WordTrace tailWord_7257480 prefixEnd_7257480 3726575580392370309823463 := by
  unfold tailWord_7257480
  simp only [CollatzResearch.WordTrace]
  refine ⟨132351020873698456874576947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176468027831597942499435929 132351020873698456874576947)
  ·
    refine ⟨198526531310547685311865421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132351020873698456874576947 198526531310547685311865421)
    ·
      refine ⟨74447449241455381991949533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198526531310547685311865421 74447449241455381991949533)
      ·
        refine ⟨27917793465545768246981075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74447449241455381991949533 27917793465545768246981075)
        ·
          refine ⟨41876690198318652370471613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27917793465545768246981075 41876690198318652370471613)
          ·
            refine ⟨15703758824369494638926855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41876690198318652370471613 15703758824369494638926855)
            ·
              refine ⟨23555638236554241958390283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15703758824369494638926855 23555638236554241958390283)
              ·
                refine ⟨35333457354831362937585425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23555638236554241958390283 35333457354831362937585425)
                ·
                  refine ⟨26500093016123522203189069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35333457354831362937585425 26500093016123522203189069)
                  ·
                    refine ⟨9937534881046320826195901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26500093016123522203189069 9937534881046320826195901)
                    ·
                      refine ⟨3726575580392370309823463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9937534881046320826195901 3726575580392370309823463)
                      ·
                        rfl

theorem cell23_7257480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_7257480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257480 prefixEnd_7257480 := by exact prefixLift 7257480
  have htrace : WordTrace (prefixWord ++ tailWord_7257480) baseStart_7257480 baseEnd_7257480 := by
    simpa [prefixWord, tailWord_7257480, baseEnd_7257480] using wordTrace_append hprefix tailTrace_7257480
  have hstable : (prefixWord ++ tailWord_7257480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257480).length < 2 ^ (prefixWord ++ tailWord_7257480).sum := by decide
  have hdescent : baseEnd_7257480 < baseStart_7257480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257533 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7257533 : Nat := 118140960795 + 7257533 * 2 ^ 59
def prefixEnd_7257533 : Nat := 4983230072969 + 3 ^ 40 * 7257533 * 2
def baseEnd_7257533 : Nat := 3726602794867058602460719

theorem tailTrace_7257533 : CollatzResearch.WordTrace tailWord_7257533 prefixEnd_7257533 3726602794867058602460719 := by
  unfold tailWord_7257533
  simp only [CollatzResearch.WordTrace]
  refine ⟨264703974816204903800833253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176469316544136602533888835 264703974816204903800833253)
  ·
    refine ⟨49631995278038419462656235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264703974816204903800833253 49631995278038419462656235)
    ·
      refine ⟨74447992917057629193984353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49631995278038419462656235 74447992917057629193984353)
      ·
        refine ⟨55835994687793221895488265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74447992917057629193984353 55835994687793221895488265)
        ·
          refine ⟨41876996015844916421616199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55835994687793221895488265 41876996015844916421616199)
          ·
            refine ⟨62815494023767374632424299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41876996015844916421616199 62815494023767374632424299)
            ·
              refine ⟨94223241035651061948636449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62815494023767374632424299 94223241035651061948636449)
              ·
                refine ⟨70667430776738296461477337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94223241035651061948636449 70667430776738296461477337)
                ·
                  refine ⟨53000573082553722346108003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70667430776738296461477337 53000573082553722346108003)
                  ·
                    refine ⟨79500859623830583519162005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53000573082553722346108003 79500859623830583519162005)
                    ·
                      refine ⟨3726602794867058602460719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79500859623830583519162005 3726602794867058602460719)
                      ·
                        rfl

theorem cell23_7257533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7257533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257533 prefixEnd_7257533 := by exact prefixLift 7257533
  have htrace : WordTrace (prefixWord ++ tailWord_7257533) baseStart_7257533 baseEnd_7257533 := by
    simpa [prefixWord, tailWord_7257533, baseEnd_7257533] using wordTrace_append hprefix tailTrace_7257533
  have hstable : (prefixWord ++ tailWord_7257533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257533).length < 2 ^ (prefixWord ++ tailWord_7257533).sum := by decide
  have hdescent : baseEnd_7257533 < baseStart_7257533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257580 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_7257580 : Nat := 118140960795 + 7257580 * 2 ^ 59
def prefixEnd_7257580 : Nat := 4983230072969 + 3 ^ 40 * 7257580 * 2
def baseEnd_7257580 : Nat := 3726626928457819918573003

theorem tailTrace_7257580 : CollatzResearch.WordTrace tailWord_7257580 prefixEnd_7257580 3726626928457819918573003 := by
  unfold tailWord_7257580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132352844523517315413897097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176470459364689753885196129 132352844523517315413897097)
  ·
    refine ⟨99264633392637986560422823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132352844523517315413897097 99264633392637986560422823)
    ·
      refine ⟨148896950088956979840634235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99264633392637986560422823 148896950088956979840634235)
      ·
        refine ⟨223345425133435469760951353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148896950088956979840634235 223345425133435469760951353)
        ·
          refine ⟨167509068850076602320713515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223345425133435469760951353 167509068850076602320713515)
          ·
            refine ⟨251263603275114903481070273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167509068850076602320713515 251263603275114903481070273)
            ·
              refine ⟨188447702456336177610802705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251263603275114903481070273 188447702456336177610802705)
              ·
                refine ⟨141335776842252133208102029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188447702456336177610802705 141335776842252133208102029)
                ·
                  refine ⟨53000916315844549953038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141335776842252133208102029 53000916315844549953038261)
                  ·
                    refine ⟨4968835904610426558097337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53000916315844549953038261 4968835904610426558097337)
                    ·
                      refine ⟨3726626928457819918573003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968835904610426558097337 3726626928457819918573003)
                      ·
                        rfl

theorem cell23_7257580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_7257580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257580 prefixEnd_7257580 := by exact prefixLift 7257580
  have htrace : WordTrace (prefixWord ++ tailWord_7257580) baseStart_7257580 baseEnd_7257580 := by
    simpa [prefixWord, tailWord_7257580, baseEnd_7257580] using wordTrace_append hprefix tailTrace_7257580
  have hstable : (prefixWord ++ tailWord_7257580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257580).length < 2 ^ (prefixWord ++ tailWord_7257580).sum := by decide
  have hdescent : baseEnd_7257580 < baseStart_7257580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257581 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_7257581 : Nat := 118140960795 + 7257581 * 2 ^ 59
def prefixEnd_7257581 : Nat := 4983230072969 + 3 ^ 40 * 7257581 * 2
def baseEnd_7257581 : Nat := 1242209147312824804886833

theorem tailTrace_7257581 : CollatzResearch.WordTrace tailWord_7257581 prefixEnd_7257581 1242209147312824804886833 := by
  unfold tailWord_7257581
  simp only [CollatzResearch.WordTrace]
  refine ⟨264705725520031007998580597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176470483680020671999053731 264705725520031007998580597)
  ·
    refine ⟨24816161767502906999866931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264705725520031007998580597 24816161767502906999866931)
    ·
      refine ⟨37224242651254360499800397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816161767502906999866931 37224242651254360499800397)
      ·
        refine ⟨13959090994220385187425149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37224242651254360499800397 13959090994220385187425149)
        ·
          refine ⟨5234659122832644445284431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13959090994220385187425149 5234659122832644445284431)
          ·
            refine ⟨7851988684248966667926647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234659122832644445284431 7851988684248966667926647)
            ·
              refine ⟨11777983026373450001889971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851988684248966667926647 11777983026373450001889971)
              ·
                refine ⟨17666974539560175002834957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777983026373450001889971 17666974539560175002834957)
                ·
                  refine ⟨6625115452335065626063109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17666974539560175002834957 6625115452335065626063109)
                  ·
                    refine ⟨1242209147312824804886833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625115452335065626063109 1242209147312824804886833)
                    ·
                      rfl

theorem cell23_7257581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_7257581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257581 prefixEnd_7257581 := by exact prefixLift 7257581
  have htrace : WordTrace (prefixWord ++ tailWord_7257581) baseStart_7257581 baseEnd_7257581 := by
    simpa [prefixWord, tailWord_7257581, baseEnd_7257581] using wordTrace_append hprefix tailTrace_7257581
  have hstable : (prefixWord ++ tailWord_7257581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257581).length < 2 ^ (prefixWord ++ tailWord_7257581).sum := by decide
  have hdescent : baseEnd_7257581 < baseStart_7257581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257593 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7257593 : Nat := 118140960795 + 7257593 * 2 ^ 59
def prefixEnd_7257593 : Nat := 4983230072969 + 3 ^ 40 * 7257593 * 2
def baseEnd_7257593 : Nat := 3726633603706328367710443

theorem tailTrace_7257593 : CollatzResearch.WordTrace tailWord_7257593 prefixEnd_7257593 3726633603706328367710443 := by
  unfold tailWord_7257593
  simp only [CollatzResearch.WordTrace]
  refine ⟨264706163195987534048017433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176470775463991689365344955 264706163195987534048017433)
  ·
    refine ⟨198529622396990650536013075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264706163195987534048017433 198529622396990650536013075)
    ·
      refine ⟨297794433595485975804019613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198529622396990650536013075 297794433595485975804019613)
      ·
        refine ⟨111672912598307240926507355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297794433595485975804019613 111672912598307240926507355)
        ·
          refine ⟨167509368897460861389761033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111672912598307240926507355 167509368897460861389761033)
          ·
            refine ⟨125632026673095646042320775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167509368897460861389761033 125632026673095646042320775)
            ·
              refine ⟨188448040009643469063481163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125632026673095646042320775 188448040009643469063481163)
              ·
                refine ⟨282672060014465203595221745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188448040009643469063481163 282672060014465203595221745)
                ·
                  refine ⟨212004045010848902696416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282672060014465203595221745 212004045010848902696416309)
                  ·
                    refine ⟨19875379219767084627789029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212004045010848902696416309 19875379219767084627789029)
                    ·
                      refine ⟨3726633603706328367710443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19875379219767084627789029 3726633603706328367710443)
                      ·
                        rfl

theorem cell23_7257593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7257593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257593 prefixEnd_7257593 := by exact prefixLift 7257593
  have htrace : WordTrace (prefixWord ++ tailWord_7257593) baseStart_7257593 baseEnd_7257593 := by
    simpa [prefixWord, tailWord_7257593, baseEnd_7257593] using wordTrace_append hprefix tailTrace_7257593
  have hstable : (prefixWord ++ tailWord_7257593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257593).length < 2 ^ (prefixWord ++ tailWord_7257593).sum := by decide
  have hdescent : baseEnd_7257593 < baseStart_7257593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257607 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 1, 5]
def baseStart_7257607 : Nat := 118140960795 + 7257607 * 2 ^ 59
def prefixEnd_7257607 : Nat := 4983230072969 + 3 ^ 40 * 7257607 * 2
def baseEnd_7257607 : Nat := 1242213597478497104311793

theorem tailTrace_7257607 : CollatzResearch.WordTrace tailWord_7257607 prefixEnd_7257607 1242213597478497104311793 := by
  unfold tailWord_7257607
  simp only [CollatzResearch.WordTrace]
  refine ⟨264706673817936814439027075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176471115878624542959351383 264706673817936814439027075)
  ·
    refine ⟨397060010726905221658540613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264706673817936814439027075 397060010726905221658540613)
    ·
      refine ⟨74448752011294729060976365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397060010726905221658540613 74448752011294729060976365)
      ·
        refine ⟨27918282004235523397866137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74448752011294729060976365 27918282004235523397866137)
        ·
          refine ⟨20938711503176642548399603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27918282004235523397866137 20938711503176642548399603)
          ·
            refine ⟨31408067254764963822599405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20938711503176642548399603 31408067254764963822599405)
            ·
              refine ⟨11778025220536861433474777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31408067254764963822599405 11778025220536861433474777)
              ·
                refine ⟨8833518915402646075106083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11778025220536861433474777 8833518915402646075106083)
                ·
                  refine ⟨13250278373103969112659125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833518915402646075106083 13250278373103969112659125)
                  ·
                    refine ⟨1242213597478497104311793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13250278373103969112659125 1242213597478497104311793)
                    ·
                      rfl

theorem cell23_7257607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_7257607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257607 prefixEnd_7257607 := by exact prefixLift 7257607
  have htrace : WordTrace (prefixWord ++ tailWord_7257607) baseStart_7257607 baseEnd_7257607 := by
    simpa [prefixWord, tailWord_7257607, baseEnd_7257607] using wordTrace_append hprefix tailTrace_7257607
  have hstable : (prefixWord ++ tailWord_7257607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257607).length < 2 ^ (prefixWord ++ tailWord_7257607).sum := by decide
  have hdescent : baseEnd_7257607 < baseStart_7257607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257624 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_7257624 : Nat := 118140960795 + 7257624 * 2 ^ 59
def prefixEnd_7257624 : Nat := 4983230072969 + 3 ^ 40 * 7257624 * 2
def baseEnd_7257624 : Nat := 1242216507202205915474267

theorem tailTrace_7257624 : CollatzResearch.WordTrace tailWord_7257624 prefixEnd_7257624 1242216507202205915474267 := by
  unfold tailWord_7257624
  simp only [CollatzResearch.WordTrace]
  refine ⟨132353646929437613171197963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176471529239250150894930617 132353646929437613171197963)
  ·
    refine ⟨198530470394156419756796945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132353646929437613171197963 198530470394156419756796945)
    ·
      refine ⟨148897852795617314817597709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198530470394156419756796945 148897852795617314817597709)
      ·
        refine ⟨55836694798356493056599141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148897852795617314817597709 55836694798356493056599141)
        ·
          refine ⟨10469380274691842448112339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55836694798356493056599141 10469380274691842448112339)
          ·
            refine ⟨15704070412037763672168509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469380274691842448112339 15704070412037763672168509)
            ·
              refine ⟨5889026404514161377063191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15704070412037763672168509 5889026404514161377063191)
              ·
                refine ⟨8833539606771242065594787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889026404514161377063191 8833539606771242065594787)
                ·
                  refine ⟨13250309410156863098392181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833539606771242065594787 13250309410156863098392181)
                  ·
                    refine ⟨1242216507202205915474267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13250309410156863098392181 1242216507202205915474267)
                    ·
                      rfl

theorem cell23_7257624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_7257624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257624 prefixEnd_7257624 := by exact prefixLift 7257624
  have htrace : WordTrace (prefixWord ++ tailWord_7257624) baseStart_7257624 baseEnd_7257624 := by
    simpa [prefixWord, tailWord_7257624, baseEnd_7257624] using wordTrace_append hprefix tailTrace_7257624
  have hstable : (prefixWord ++ tailWord_7257624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257624).length < 2 ^ (prefixWord ++ tailWord_7257624).sum := by decide
  have hdescent : baseEnd_7257624 < baseStart_7257624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257633 : List Nat := [1, 2, 3, 2, 2, 13]
def baseStart_7257633 : Nat := 118140960795 + 7257633 * 2 ^ 59
def prefixEnd_7257633 : Nat := 4983230072969 + 3 ^ 40 * 7257633 * 2
def baseEnd_7257633 : Nat := 15336025279557646959713

theorem tailTrace_7257633 : CollatzResearch.WordTrace tailWord_7257633 prefixEnd_7257633 15336025279557646959713 := by
  unfold tailWord_7257633
  simp only [CollatzResearch.WordTrace]
  refine ⟨264707622115842620879473553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176471748077228413919649035 264707622115842620879473553)
  ·
    refine ⟨198530716586881965659605165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264707622115842620879473553 198530716586881965659605165)
    ·
      refine ⟨74449018720080737122351937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198530716586881965659605165 74449018720080737122351937)
      ·
        refine ⟨55836764040060552841763953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74449018720080737122351937 55836764040060552841763953)
        ·
          refine ⟨41877573030045414631322965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55836764040060552841763953 41877573030045414631322965)
          ·
            refine ⟨15336025279557646959713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41877573030045414631322965 15336025279557646959713)
            ·
              rfl

theorem cell23_7257633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 13].length) (baseStart_7257633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257633 prefixEnd_7257633 := by exact prefixLift 7257633
  have htrace : WordTrace (prefixWord ++ tailWord_7257633) baseStart_7257633 baseEnd_7257633 := by
    simpa [prefixWord, tailWord_7257633, baseEnd_7257633] using wordTrace_append hprefix tailTrace_7257633
  have hstable : (prefixWord ++ tailWord_7257633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257633).length < 2 ^ (prefixWord ++ tailWord_7257633).sum := by decide
  have hdescent : baseEnd_7257633 < baseStart_7257633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257654 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7257654 : Nat := 118140960795 + 7257654 * 2 ^ 59
def prefixEnd_7257654 : Nat := 4983230072969 + 3 ^ 40 * 7257654 * 2
def baseEnd_7257654 : Nat := 1242221642008750876349221

theorem tailTrace_7257654 : CollatzResearch.WordTrace tailWord_7257654 prefixEnd_7257654 1242221642008750876349221 := by
  unfold tailWord_7257654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544274253047908841624251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176472258699177694310658677 16544274253047908841624251)
  ·
    refine ⟨24816411379571863262436377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16544274253047908841624251 24816411379571863262436377)
    ·
      refine ⟨18612308534678897446827283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24816411379571863262436377 18612308534678897446827283)
      ·
        refine ⟨27918462802018346170240925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18612308534678897446827283 27918462802018346170240925)
        ·
          refine ⟨10469423550756879813840347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27918462802018346170240925 10469423550756879813840347)
          ·
            refine ⟨15704135326135319720760521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469423550756879813840347 15704135326135319720760521)
            ·
              refine ⟨11778101494601489790570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15704135326135319720760521 11778101494601489790570391)
              ·
                refine ⟨17667152241902234685855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778101494601489790570391 17667152241902234685855587)
                ·
                  refine ⟨26500728362853352028783381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17667152241902234685855587 26500728362853352028783381)
                  ·
                    refine ⟨1242221642008750876349221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26500728362853352028783381 1242221642008750876349221)
                    ·
                      rfl

theorem cell23_7257654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7257654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257654 prefixEnd_7257654 := by exact prefixLift 7257654
  have htrace : WordTrace (prefixWord ++ tailWord_7257654) baseStart_7257654 baseEnd_7257654 := by
    simpa [prefixWord, tailWord_7257654, baseEnd_7257654] using wordTrace_append hprefix tailTrace_7257654
  have hstable : (prefixWord ++ tailWord_7257654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257654).length < 2 ^ (prefixWord ++ tailWord_7257654).sum := by decide
  have hdescent : baseEnd_7257654 < baseStart_7257654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257657 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7257657 : Nat := 118140960795 + 7257657 * 2 ^ 59
def prefixEnd_7257657 : Nat := 4983230072969 + 3 ^ 40 * 7257657 * 2
def baseEnd_7257657 : Nat := 3726666466468216117310149

theorem tailTrace_7257657 : CollatzResearch.WordTrace tailWord_7257657 prefixEnd_7257657 3726666466468216117310149 := by
  unfold tailWord_7257657
  simp only [CollatzResearch.WordTrace]
  refine ⟨264708497467755672978347225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176472331645170448652231483 264708497467755672978347225)
  ·
    refine ⟨198531373100816754733760419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264708497467755672978347225 198531373100816754733760419)
    ·
      refine ⟨297797059651225132100640629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198531373100816754733760419 297797059651225132100640629)
      ·
        refine ⟨27918474342302356134435059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297797059651225132100640629 27918474342302356134435059)
        ·
          refine ⟨41877711513453534201652589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27918474342302356134435059 41877711513453534201652589)
          ·
            refine ⟨15704141817545075325619721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41877711513453534201652589 15704141817545075325619721)
            ·
              refine ⟨11778106363158806494214791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15704141817545075325619721 11778106363158806494214791)
              ·
                refine ⟨17667159544738209741322187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778106363158806494214791 17667159544738209741322187)
                ·
                  refine ⟨26500739317107314611983281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17667159544738209741322187 26500739317107314611983281)
                  ·
                    refine ⟨19875554487830485958987461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26500739317107314611983281 19875554487830485958987461)
                    ·
                      refine ⟨3726666466468216117310149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19875554487830485958987461 3726666466468216117310149)
                      ·
                        rfl

theorem cell23_7257657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7257657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257657 prefixEnd_7257657 := by exact prefixLift 7257657
  have htrace : WordTrace (prefixWord ++ tailWord_7257657) baseStart_7257657 baseEnd_7257657 := by
    simpa [prefixWord, tailWord_7257657, baseEnd_7257657] using wordTrace_append hprefix tailTrace_7257657
  have hstable : (prefixWord ++ tailWord_7257657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257657).length < 2 ^ (prefixWord ++ tailWord_7257657).sum := by decide
  have hdescent : baseEnd_7257657 < baseStart_7257657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257661 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_7257661 : Nat := 118140960795 + 7257661 * 2 ^ 59
def prefixEnd_7257661 : Nat := 4983230072969 + 3 ^ 40 * 7257661 * 2
def baseEnd_7257661 : Nat := 3726668520390834101660131

theorem tailTrace_7257661 : CollatzResearch.WordTrace tailWord_7257661 prefixEnd_7257661 3726668520390834101660131 := by
  unfold tailWord_7257661
  simp only [CollatzResearch.WordTrace]
  refine ⟨264708643359741181661492837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176472428906494121107661891 264708643359741181661492837)
  ·
    refine ⟨49632870629951471561529907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264708643359741181661492837 49632870629951471561529907)
    ·
      refine ⟨74449305944927207342294861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49632870629951471561529907 74449305944927207342294861)
      ·
        refine ⟨27918489729347702753360573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74449305944927207342294861 27918489729347702753360573)
        ·
          refine ⟨10469433648505388532510215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27918489729347702753360573 10469433648505388532510215)
          ·
            refine ⟨15704150472758082798765323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469433648505388532510215 15704150472758082798765323)
            ·
              refine ⟨23556225709137124198147985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15704150472758082798765323 23556225709137124198147985)
              ·
                refine ⟨17667169281852843148610989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23556225709137124198147985 17667169281852843148610989)
                ·
                  refine ⟨6625188480694816180729121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17667169281852843148610989 6625188480694816180729121)
                  ·
                    refine ⟨4968891360521112135546841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6625188480694816180729121 4968891360521112135546841)
                    ·
                      refine ⟨3726668520390834101660131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968891360521112135546841 3726668520390834101660131)
                      ·
                        rfl

theorem cell23_7257661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_7257661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257661 prefixEnd_7257661 := by exact prefixLift 7257661
  have htrace : WordTrace (prefixWord ++ tailWord_7257661) baseStart_7257661 baseEnd_7257661 := by
    simpa [prefixWord, tailWord_7257661, baseEnd_7257661] using wordTrace_append hprefix tailTrace_7257661
  have hstable : (prefixWord ++ tailWord_7257661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257661).length < 2 ^ (prefixWord ++ tailWord_7257661).sum := by decide
  have hdescent : baseEnd_7257661 < baseStart_7257661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257683 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_7257683 : Nat := 118140960795 + 7257683 * 2 ^ 59
def prefixEnd_7257683 : Nat := 4983230072969 + 3 ^ 40 * 7257683 * 2
def baseEnd_7257683 : Nat := 3726679816965233015585029

theorem tailTrace_7257683 : CollatzResearch.WordTrace tailWord_7257683 prefixEnd_7257683 3726679816965233015585029 := by
  unfold tailWord_7257683
  simp only [CollatzResearch.WordTrace]
  refine ⟨264709445765661479418793703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176472963843774319612529135 264709445765661479418793703)
  ·
    refine ⟨397064168648492219128190555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264709445765661479418793703 397064168648492219128190555)
    ·
      refine ⟨595596252972738328692285833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397064168648492219128190555 595596252972738328692285833)
      ·
        refine ⟨446697189729553746519214375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595596252972738328692285833 446697189729553746519214375)
        ·
          refine ⟨670045784594330619778821563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446697189729553746519214375 670045784594330619778821563)
          ·
            refine ⟨1005068676891495929668232345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670045784594330619778821563 1005068676891495929668232345)
            ·
              refine ⟨753801507668621947251174259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005068676891495929668232345 753801507668621947251174259)
              ·
                refine ⟨1130702261502932920876761389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753801507668621947251174259 1130702261502932920876761389)
                ·
                  refine ⟨424013348063599845328785521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130702261502932920876761389 424013348063599845328785521)
                  ·
                    refine ⟨318010011047699883996589141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424013348063599845328785521 318010011047699883996589141)
                    ·
                      refine ⟨3726679816965233015585029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 318010011047699883996589141 3726679816965233015585029)
                      ·
                        rfl

theorem cell23_7257683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_7257683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257683 prefixEnd_7257683 := by exact prefixLift 7257683
  have htrace : WordTrace (prefixWord ++ tailWord_7257683) baseStart_7257683 baseEnd_7257683 := by
    simpa [prefixWord, tailWord_7257683, baseEnd_7257683] using wordTrace_append hprefix tailTrace_7257683
  have hstable : (prefixWord ++ tailWord_7257683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257683).length < 2 ^ (prefixWord ++ tailWord_7257683).sum := by decide
  have hdescent : baseEnd_7257683 < baseStart_7257683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257762 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7257762 : Nat := 118140960795 + 7257762 * 2 ^ 59
def prefixEnd_7257762 : Nat := 4983230072969 + 3 ^ 40 * 7257762 * 2
def baseEnd_7257762 : Nat := 3726720381936938206497167

theorem tailTrace_7257762 : CollatzResearch.WordTrace tailWord_7257762 prefixEnd_7257762 3726720381936938206497167 := by
  unfold tailWord_7257762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178081783093818977729885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176474884754916850607279693 66178081783093818977729885)
  ·
    refine ⟨24816780668660182116648707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66178081783093818977729885 24816780668660182116648707)
    ·
      refine ⟨37225171002990273174973061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816780668660182116648707 37225171002990273174973061)
      ·
        refine ⟨6979719563060676220307449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37225171002990273174973061 6979719563060676220307449)
        ·
          refine ⟨5234789672295507165230587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979719563060676220307449 5234789672295507165230587)
          ·
            refine ⟨7852184508443260747845881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234789672295507165230587 7852184508443260747845881)
            ·
              refine ⟨5889138381332445560884411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852184508443260747845881 5889138381332445560884411)
              ·
                refine ⟨8833707571998668341326617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889138381332445560884411 8833707571998668341326617)
                ·
                  refine ⟨6625280678999001255994963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8833707571998668341326617 6625280678999001255994963)
                  ·
                    refine ⟨9937921018498501883992445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6625280678999001255994963 9937921018498501883992445)
                    ·
                      refine ⟨3726720381936938206497167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9937921018498501883992445 3726720381936938206497167)
                      ·
                        rfl

theorem cell23_7257762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7257762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257762 prefixEnd_7257762 := by exact prefixLift 7257762
  have htrace : WordTrace (prefixWord ++ tailWord_7257762) baseStart_7257762 baseEnd_7257762 := by
    simpa [prefixWord, tailWord_7257762, baseEnd_7257762] using wordTrace_append hprefix tailTrace_7257762
  have hstable : (prefixWord ++ tailWord_7257762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257762).length < 2 ^ (prefixWord ++ tailWord_7257762).sum := by decide
  have hdescent : baseEnd_7257762 < baseStart_7257762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257807 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 6, 2]
def baseStart_7257807 : Nat := 118140960795 + 7257807 * 2 ^ 59
def prefixEnd_7257807 : Nat := 4983230072969 + 3 ^ 40 * 7257807 * 2
def baseEnd_7257807 : Nat := 3726743488566390530434459

theorem tailTrace_7257807 : CollatzResearch.WordTrace tailWord_7257807 prefixEnd_7257807 3726743488566390530434459 := by
  unfold tailWord_7257807
  simp only [CollatzResearch.WordTrace]
  refine ⟨264713968417212248596307675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176475978944808165730871783 264713968417212248596307675)
  ·
    refine ⟨397070952625818372894461513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264713968417212248596307675 397070952625818372894461513)
    ·
      refine ⟨297803214469363779670846135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397070952625818372894461513 297803214469363779670846135)
      ·
        refine ⟨446704821704045669506269203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297803214469363779670846135 446704821704045669506269203)
        ·
          refine ⟨670057232556068504259403805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446704821704045669506269203 670057232556068504259403805)
          ·
            refine ⟨251271462208525689097276427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670057232556068504259403805 251271462208525689097276427)
            ·
              refine ⟨376907193312788533645914641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251271462208525689097276427 376907193312788533645914641)
              ·
                refine ⟨282680394984591400234435981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376907193312788533645914641 282680394984591400234435981)
                ·
                  refine ⟨106005148119221775087913493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282680394984591400234435981 106005148119221775087913493)
                  ·
                    refine ⟨4968991318088520707245945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106005148119221775087913493 4968991318088520707245945)
                    ·
                      refine ⟨3726743488566390530434459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4968991318088520707245945 3726743488566390530434459)
                      ·
                        rfl

theorem cell23_7257807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6, 2].length) (baseStart_7257807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257807 prefixEnd_7257807 := by exact prefixLift 7257807
  have htrace : WordTrace (prefixWord ++ tailWord_7257807) baseStart_7257807 baseEnd_7257807 := by
    simpa [prefixWord, tailWord_7257807, baseEnd_7257807] using wordTrace_append hprefix tailTrace_7257807
  have hstable : (prefixWord ++ tailWord_7257807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257807).length < 2 ^ (prefixWord ++ tailWord_7257807).sum := by decide
  have hdescent : baseEnd_7257807 < baseStart_7257807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257884 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7257884 : Nat := 118140960795 + 7257884 * 2 ^ 59
def prefixEnd_7257884 : Nat := 4983230072969 + 3 ^ 40 * 7257884 * 2
def baseEnd_7257884 : Nat := 3726783026576786729171605

theorem tailTrace_7257884 : CollatzResearch.WordTrace tailWord_7257884 prefixEnd_7257884 3726783026576786729171605 := by
  unfold tailWord_7257884
  simp only [CollatzResearch.WordTrace]
  refine ⟨132358388418966645373430353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176477851225288860497907137 132358388418966645373430353)
  ·
    refine ⟨99268791314224984030072765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132358388418966645373430353 99268791314224984030072765)
    ·
      refine ⟨37225796742834369011277287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99268791314224984030072765 37225796742834369011277287)
      ·
        refine ⟨55838695114251553516915931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37225796742834369011277287 55838695114251553516915931)
        ·
          refine ⟨83758042671377330275373897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55838695114251553516915931 83758042671377330275373897)
          ·
            refine ⟨62818532003532997706530423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83758042671377330275373897 62818532003532997706530423)
            ·
              refine ⟨94227798005299496559795635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62818532003532997706530423 94227798005299496559795635)
              ·
                refine ⟨141341697007949244839693453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94227798005299496559795635 141341697007949244839693453)
                ·
                  refine ⟨53003136377980966814885045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141341697007949244839693453 53003136377980966814885045)
                  ·
                    refine ⟨4969044035435715638895473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53003136377980966814885045 4969044035435715638895473)
                    ·
                      refine ⟨3726783026576786729171605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969044035435715638895473 3726783026576786729171605)
                      ·
                        rfl

theorem cell23_7257884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7257884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257884 prefixEnd_7257884 := by exact prefixLift 7257884
  have htrace : WordTrace (prefixWord ++ tailWord_7257884) baseStart_7257884 baseEnd_7257884 := by
    simpa [prefixWord, tailWord_7257884, baseEnd_7257884] using wordTrace_append hprefix tailTrace_7257884
  have hstable : (prefixWord ++ tailWord_7257884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257884).length < 2 ^ (prefixWord ++ tailWord_7257884).sum := by decide
  have hdescent : baseEnd_7257884 < baseStart_7257884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257902 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7257902 : Nat := 118140960795 + 7257902 * 2 ^ 59
def prefixEnd_7257902 : Nat := 4983230072969 + 3 ^ 40 * 7257902 * 2
def baseEnd_7257902 : Nat := 1242264089742855886248841

theorem tailTrace_7257902 : CollatzResearch.WordTrace tailWord_7257902 prefixEnd_7257902 1242264089742855886248841 := by
  unfold tailWord_7257902
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089679168983509977626995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176478288901245386547343973 33089679168983509977626995)
  ·
    refine ⟨49634518753475264966440493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33089679168983509977626995 49634518753475264966440493)
    ·
      refine ⟨18612944532553224362415185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49634518753475264966440493 18612944532553224362415185)
      ·
        refine ⟨13959708399414918271811389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18612944532553224362415185 13959708399414918271811389)
        ·
          refine ⟨5234890649780594351929271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13959708399414918271811389 5234890649780594351929271)
          ·
            refine ⟨7852335974670891527893907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234890649780594351929271 7852335974670891527893907)
            ·
              refine ⟨11778503962006337291840861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852335974670891527893907 11778503962006337291840861)
              ·
                refine ⟨4416938985752376484440323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11778503962006337291840861 4416938985752376484440323)
                ·
                  refine ⟨6625408478628564726660485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416938985752376484440323 6625408478628564726660485)
                  ·
                    refine ⟨1242264089742855886248841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625408478628564726660485 1242264089742855886248841)
                    ·
                      rfl

theorem cell23_7257902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7257902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257902 prefixEnd_7257902 := by exact prefixLift 7257902
  have htrace : WordTrace (prefixWord ++ tailWord_7257902) baseStart_7257902 baseEnd_7257902 := by
    simpa [prefixWord, tailWord_7257902, baseEnd_7257902] using wordTrace_append hprefix tailTrace_7257902
  have hstable : (prefixWord ++ tailWord_7257902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257902).length < 2 ^ (prefixWord ++ tailWord_7257902).sum := by decide
  have hdescent : baseEnd_7257902 < baseStart_7257902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257918 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_7257918 : Nat := 118140960795 + 7257918 * 2 ^ 59
def prefixEnd_7257918 : Nat := 4983230072969 + 3 ^ 40 * 7257918 * 2
def baseEnd_7257918 : Nat := 3726800484919039596146449

theorem tailTrace_7257918 : CollatzResearch.WordTrace tailWord_7257918 prefixEnd_7257918 3726800484919039596146449 := by
  unfold tailWord_7257918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089752114976264319199801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176478677946540076369065605 33089752114976264319199801)
  ·
    refine ⟨24817314086232198239399851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33089752114976264319199801 24817314086232198239399851)
    ·
      refine ⟨37225971129348297359099777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24817314086232198239399851 37225971129348297359099777)
      ·
        refine ⟨27919478347011223019324833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37225971129348297359099777 27919478347011223019324833)
        ·
          refine ⟨20939608760258417264493625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27919478347011223019324833 20939608760258417264493625)
          ·
            refine ⟨15704706570193812948370219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20939608760258417264493625 15704706570193812948370219)
            ·
              refine ⟨23557059855290719422555329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15704706570193812948370219 23557059855290719422555329)
              ·
                refine ⟨17667794891468039566916497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23557059855290719422555329 17667794891468039566916497)
                ·
                  refine ⟨13250846168601029675187373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17667794891468039566916497 13250846168601029675187373)
                  ·
                    refine ⟨4969067313225386128195265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13250846168601029675187373 4969067313225386128195265)
                    ·
                      refine ⟨3726800484919039596146449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969067313225386128195265 3726800484919039596146449)
                      ·
                        rfl

theorem cell23_7257918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_7257918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257918 prefixEnd_7257918 := by exact prefixLift 7257918
  have htrace : WordTrace (prefixWord ++ tailWord_7257918) baseStart_7257918 baseEnd_7257918 := by
    simpa [prefixWord, tailWord_7257918, baseEnd_7257918] using wordTrace_append hprefix tailTrace_7257918
  have hstable : (prefixWord ++ tailWord_7257918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257918).length < 2 ^ (prefixWord ++ tailWord_7257918).sum := by decide
  have hdescent : baseEnd_7257918 < baseStart_7257918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257927 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_7257927 : Nat := 118140960795 + 7257927 * 2 ^ 59
def prefixEnd_7257927 : Nat := 4983230072969 + 3 ^ 40 * 7257927 * 2
def baseEnd_7257927 : Nat := 3726805106244930060933907

theorem tailTrace_7257927 : CollatzResearch.WordTrace tailWord_7257927 prefixEnd_7257927 3726805106244930060933907 := by
  unfold tailWord_7257927
  simp only [CollatzResearch.WordTrace]
  refine ⟨264718345176777509090676035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176478896784518339393784023 264718345176777509090676035)
  ·
    refine ⟨397077517765166263636014053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264718345176777509090676035 397077517765166263636014053)
    ·
      refine ⟨74452034580968674431752635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397077517765166263636014053 74452034580968674431752635)
      ·
        refine ⟨111678051871453011647628953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74452034580968674431752635 111678051871453011647628953)
        ·
          refine ⟨83758538903589758735721715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111678051871453011647628953 83758538903589758735721715)
          ·
            refine ⟨125637808355384638103582573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83758538903589758735721715 125637808355384638103582573)
            ·
              refine ⟨47114178133269239288843465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125637808355384638103582573 47114178133269239288843465)
              ·
                refine ⟨35335633599951929466632599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47114178133269239288843465 35335633599951929466632599)
                ·
                  refine ⟨53003450399927894199948899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35335633599951929466632599 53003450399927894199948899)
                  ·
                    refine ⟨79505175599891841299923349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53003450399927894199948899 79505175599891841299923349)
                    ·
                      refine ⟨3726805106244930060933907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79505175599891841299923349 3726805106244930060933907)
                      ·
                        rfl

theorem cell23_7257927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_7257927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257927 prefixEnd_7257927 := by exact prefixLift 7257927
  have htrace : WordTrace (prefixWord ++ tailWord_7257927) baseStart_7257927 baseEnd_7257927 := by
    simpa [prefixWord, tailWord_7257927, baseEnd_7257927] using wordTrace_append hprefix tailTrace_7257927
  have hstable : (prefixWord ++ tailWord_7257927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257927).length < 2 ^ (prefixWord ++ tailWord_7257927).sum := by decide
  have hdescent : baseEnd_7257927 < baseStart_7257927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257937 : List Nat := [1, 2, 2, 1, 5, 1, 1, 10]
def baseStart_7257937 : Nat := 118140960795 + 7257937 * 2 ^ 59
def prefixEnd_7257937 : Nat := 4983230072969 + 3 ^ 40 * 7257937 * 2
def baseEnd_7257937 : Nat := 138030008927832408215143

theorem tailTrace_7257937 : CollatzResearch.WordTrace tailWord_7257937 prefixEnd_7257937 138030008927832408215143 := by
  unfold tailWord_7257937
  simp only [CollatzResearch.WordTrace]
  refine ⟨264718709906741280798540065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176479139937827520532360043 264718709906741280798540065)
  ·
    refine ⟨198539032430055960598905049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264718709906741280798540065 198539032430055960598905049)
    ·
      refine ⟨148904274322541970449178787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198539032430055960598905049 148904274322541970449178787)
      ·
        refine ⟨223356411483812955673768181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148904274322541970449178787 223356411483812955673768181)
        ·
          refine ⟨20939663576607464594415767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223356411483812955673768181 20939663576607464594415767)
          ·
            refine ⟨31409495364911196891623651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20939663576607464594415767 31409495364911196891623651)
            ·
              refine ⟨47114243047366795337435477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31409495364911196891623651 47114243047366795337435477)
              ·
                refine ⟨138030008927832408215143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47114243047366795337435477 138030008927832408215143)
                ·
                  rfl

theorem cell23_7257937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 10].length) (baseStart_7257937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257937 prefixEnd_7257937 := by exact prefixLift 7257937
  have htrace : WordTrace (prefixWord ++ tailWord_7257937) baseStart_7257937 baseEnd_7257937 := by
    simpa [prefixWord, tailWord_7257937, baseEnd_7257937] using wordTrace_append hprefix tailTrace_7257937
  have hstable : (prefixWord ++ tailWord_7257937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257937).length < 2 ^ (prefixWord ++ tailWord_7257937).sum := by decide
  have hdescent : baseEnd_7257937 < baseStart_7257937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257941 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_7257941 : Nat := 118140960795 + 7257941 * 2 ^ 59
def prefixEnd_7257941 : Nat := 4983230072969 + 3 ^ 40 * 7257941 * 2
def baseEnd_7257941 : Nat := 1242270764991364335386281

theorem tailTrace_7257941 : CollatzResearch.WordTrace tailWord_7257941 prefixEnd_7257941 1242270764991364335386281 := by
  unfold tailWord_7257941
  simp only [CollatzResearch.WordTrace]
  refine ⟨264718855798726789481685677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176479237199151192987790451 264718855798726789481685677)
  ·
    refine ⟨99269570924522546055632129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264718855798726789481685677 99269570924522546055632129)
    ·
      refine ⟨74452178193391909541724097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99269570924522546055632129 74452178193391909541724097)
      ·
        refine ⟨55839133645043932156293073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74452178193391909541724097 55839133645043932156293073)
        ·
          refine ⟨41879350233782949117219805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55839133645043932156293073 41879350233782949117219805)
          ·
            refine ⟨15704756337668605918957427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41879350233782949117219805 15704756337668605918957427)
            ·
              refine ⟨23557134506502908878436141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15704756337668605918957427 23557134506502908878436141)
              ·
                refine ⟨8833925439938590829413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23557134506502908878436141 8833925439938590829413553)
                ·
                  refine ⟨6625444079953943122060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8833925439938590829413553 6625444079953943122060165)
                  ·
                    refine ⟨1242270764991364335386281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625444079953943122060165 1242270764991364335386281)
                    ·
                      rfl

theorem cell23_7257941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_7257941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257941 prefixEnd_7257941 := by exact prefixLift 7257941
  have htrace : WordTrace (prefixWord ++ tailWord_7257941) baseStart_7257941 baseEnd_7257941 := by
    simpa [prefixWord, tailWord_7257941, baseEnd_7257941] using wordTrace_append hprefix tailTrace_7257941
  have hstable : (prefixWord ++ tailWord_7257941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257941).length < 2 ^ (prefixWord ++ tailWord_7257941).sum := by decide
  have hdescent : baseEnd_7257941 < baseStart_7257941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3]
def baseStart_7257947 : Nat := 118140960795 + 7257947 * 2 ^ 59
def prefixEnd_7257947 : Nat := 4983230072969 + 3 ^ 40 * 7257947 * 2
def baseEnd_7257947 : Nat := 3726815375858019982683815

theorem tailTrace_7257947 : CollatzResearch.WordTrace tailWord_7257947 prefixEnd_7257947 3726815375858019982683815 := by
  unfold tailWord_7257947
  simp only [CollatzResearch.WordTrace]
  refine ⟨264719074636705052506404095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176479383091136701670936063 264719074636705052506404095)
  ·
    refine ⟨397078611955057578759606143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264719074636705052506404095 397078611955057578759606143)
    ·
      refine ⟨595617917932586368139409215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397078611955057578759606143 595617917932586368139409215)
      ·
        refine ⟨893426876898879552209113823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595617917932586368139409215 893426876898879552209113823)
        ·
          refine ⟨1340140315348319328313670735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893426876898879552209113823 1340140315348319328313670735)
          ·
            refine ⟨2010210473022478992470506103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340140315348319328313670735 2010210473022478992470506103)
            ·
              refine ⟨3015315709533718488705759155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010210473022478992470506103 3015315709533718488705759155)
              ·
                refine ⟨4522973564300577733058638733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015315709533718488705759155 4522973564300577733058638733)
                ·
                  refine ⟨1696115086612716649896989525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4522973564300577733058638733 1696115086612716649896989525)
                  ·
                    refine ⟨9938174335621386620490173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1696115086612716649896989525 9938174335621386620490173)
                    ·
                      refine ⟨3726815375858019982683815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938174335621386620490173 3726815375858019982683815)
                      ·
                        rfl

theorem cell23_7257947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].length) (baseStart_7257947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257947 prefixEnd_7257947 := by exact prefixLift 7257947
  have htrace : WordTrace (prefixWord ++ tailWord_7257947) baseStart_7257947 baseEnd_7257947 := by
    simpa [prefixWord, tailWord_7257947, baseEnd_7257947] using wordTrace_append hprefix tailTrace_7257947
  have hstable : (prefixWord ++ tailWord_7257947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257947).length < 2 ^ (prefixWord ++ tailWord_7257947).sum := by decide
  have hdescent : baseEnd_7257947 < baseStart_7257947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257951 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_7257951 : Nat := 118140960795 + 7257951 * 2 ^ 59
def prefixEnd_7257951 : Nat := 4983230072969 + 3 ^ 40 * 7257951 * 2
def baseEnd_7257951 : Nat := 3726817429780637967033797

theorem tailTrace_7257951 : CollatzResearch.WordTrace tailWord_7257951 prefixEnd_7257951 3726817429780637967033797 := by
  unfold tailWord_7257951
  simp only [CollatzResearch.WordTrace]
  refine ⟨264719220528690561189549707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176479480352460374126366471 264719220528690561189549707)
  ·
    refine ⟨397078830793035841784324561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264719220528690561189549707 397078830793035841784324561)
    ·
      refine ⟨297809123094776881338243421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397078830793035841784324561 297809123094776881338243421)
      ·
        refine ⟨111678421160541330501841283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297809123094776881338243421 111678421160541330501841283)
        ·
          refine ⟨167517631740811995752761925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111678421160541330501841283 167517631740811995752761925)
          ·
            refine ⟨31409555951402249203642861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167517631740811995752761925 31409555951402249203642861)
            ·
              refine ⟨11778583481775843451366073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31409555951402249203642861 11778583481775843451366073)
              ·
                refine ⟨8833937611331882588524555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11778583481775843451366073 8833937611331882588524555)
                ·
                  refine ⟨13250906416997823882786833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833937611331882588524555 13250906416997823882786833)
                  ·
                    refine ⟨9938179812748367912090125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13250906416997823882786833 9938179812748367912090125)
                    ·
                      refine ⟨3726817429780637967033797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938179812748367912090125 3726817429780637967033797)
                      ·
                        rfl

theorem cell23_7257951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_7257951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257951 prefixEnd_7257951 := by exact prefixLift 7257951
  have htrace : WordTrace (prefixWord ++ tailWord_7257951) baseStart_7257951 baseEnd_7257951 := by
    simpa [prefixWord, tailWord_7257951, baseEnd_7257951] using wordTrace_append hprefix tailTrace_7257951
  have hstable : (prefixWord ++ tailWord_7257951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257951).length < 2 ^ (prefixWord ++ tailWord_7257951).sum := by decide
  have hdescent : baseEnd_7257951 < baseStart_7257951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257954 : List Nat := [3, 3, 2, 1, 2, 1, 2, 9]
def baseStart_7257954 : Nat := 118140960795 + 7257954 * 2 ^ 59
def prefixEnd_7257954 : Nat := 4983230072969 + 3 ^ 40 * 7257954 * 2
def baseEnd_7257954 : Nat := 138030332230466720566529

theorem tailTrace_7257954 : CollatzResearch.WordTrace tailWord_7257954 prefixEnd_7257954 138030332230466720566529 := by
  unfold tailWord_7257954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66179832486919923175477229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176479553298453128467939277 66179832486919923175477229)
  ·
    refine ⟨24817437182594971190803961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66179832486919923175477229 24817437182594971190803961)
    ·
      refine ⟨18613077886946228393102971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24817437182594971190803961 18613077886946228393102971)
      ·
        refine ⟨27919616830419342589654457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18613077886946228393102971 27919616830419342589654457)
        ·
          refine ⟨20939712622814506942240843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27919616830419342589654457 20939712622814506942240843)
          ·
            refine ⟨31409568934221760413361265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20939712622814506942240843 31409568934221760413361265)
            ·
              refine ⟨23557176700666320310020949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31409568934221760413361265 23557176700666320310020949)
              ·
                refine ⟨138030332230466720566529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23557176700666320310020949 138030332230466720566529)
                ·
                  rfl

theorem cell23_7257954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_7257954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257954 prefixEnd_7257954 := by exact prefixLift 7257954
  have htrace : WordTrace (prefixWord ++ tailWord_7257954) baseStart_7257954 baseEnd_7257954 := by
    simpa [prefixWord, tailWord_7257954, baseEnd_7257954] using wordTrace_append hprefix tailTrace_7257954
  have hstable : (prefixWord ++ tailWord_7257954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257954).length < 2 ^ (prefixWord ++ tailWord_7257954).sum := by decide
  have hdescent : baseEnd_7257954 < baseStart_7257954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7257964 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_7257964 : Nat := 118140960795 + 7257964 * 2 ^ 59
def prefixEnd_7257964 : Nat := 4983230072969 + 3 ^ 40 * 7257964 * 2
def baseEnd_7257964 : Nat := 3726824105029146416171237

theorem tailTrace_7257964 : CollatzResearch.WordTrace tailWord_7257964 prefixEnd_7257964 3726824105029146416171237 := by
  unfold tailWord_7257964
  simp only [CollatzResearch.WordTrace]
  refine ⟨132359847338821732204886473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176479796451762309606515297 132359847338821732204886473)
  ·
    refine ⟨99269885504116299153664855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132359847338821732204886473 99269885504116299153664855)
    ·
      refine ⟨148904828256174448730497283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99269885504116299153664855 148904828256174448730497283)
      ·
        refine ⟨223357242384261673095745925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148904828256174448730497283 223357242384261673095745925)
        ·
          refine ⟨41879482947049063705452361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223357242384261673095745925 41879482947049063705452361)
          ·
            refine ⟨31409612210286797779089271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41879482947049063705452361 31409612210286797779089271)
            ·
              refine ⟨47114418315430196668633907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31409612210286797779089271 47114418315430196668633907)
              ·
                refine ⟨70671627473145295002950861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47114418315430196668633907 70671627473145295002950861)
                ·
                  refine ⟨26501860302429485626106573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70671627473145295002950861 26501860302429485626106573)
                  ·
                    refine ⟨9938197613411057109789965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26501860302429485626106573 9938197613411057109789965)
                    ·
                      refine ⟨3726824105029146416171237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938197613411057109789965 3726824105029146416171237)
                      ·
                        rfl

theorem cell23_7257964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_7257964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7257964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7257964 prefixEnd_7257964 := by exact prefixLift 7257964
  have htrace : WordTrace (prefixWord ++ tailWord_7257964) baseStart_7257964 baseEnd_7257964 := by
    simpa [prefixWord, tailWord_7257964, baseEnd_7257964] using wordTrace_append hprefix tailTrace_7257964
  have hstable : (prefixWord ++ tailWord_7257964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7257964).length < 2 ^ (prefixWord ++ tailWord_7257964).sum := by decide
  have hdescent : baseEnd_7257964 < baseStart_7257964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7257964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258084 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_7258084 : Nat := 118140960795 + 7258084 * 2 ^ 59
def prefixEnd_7258084 : Nat := 4983230072969 + 3 ^ 40 * 7258084 * 2
def baseEnd_7258084 : Nat := 3726885722707685946670685

theorem tailTrace_7258084 : CollatzResearch.WordTrace tailWord_7258084 prefixEnd_7258084 3726885722707685946670685 := by
  unfold tailWord_7258084
  simp only [CollatzResearch.WordTrace]
  refine ⟨132362035718604362452070653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176482714291472483269427537 132362035718604362452070653)
  ·
    refine ⟨49635763394476635919526495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132362035718604362452070653 49635763394476635919526495)
    ·
      refine ⟨74453645091714953879289743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49635763394476635919526495 74453645091714953879289743)
      ·
        refine ⟨111680467637572430818934615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74453645091714953879289743 111680467637572430818934615)
        ·
          refine ⟨167520701456358646228401923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111680467637572430818934615 167520701456358646228401923)
          ·
            refine ⟨251281052184537969342602885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167520701456358646228401923 251281052184537969342602885)
            ·
              refine ⟨47115197284600869251738041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251281052184537969342602885 47115197284600869251738041)
              ·
                refine ⟨35336397963450651938803531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47115197284600869251738041 35336397963450651938803531)
                ·
                  refine ⟨53004596945175977908205297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35336397963450651938803531 53004596945175977908205297)
                  ·
                    refine ⟨39753447708881983431153973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53004596945175977908205297 39753447708881983431153973)
                    ·
                      refine ⟨3726885722707685946670685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39753447708881983431153973 3726885722707685946670685)
                      ·
                        rfl

theorem cell23_7258084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_7258084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258084 prefixEnd_7258084 := by exact prefixLift 7258084
  have htrace : WordTrace (prefixWord ++ tailWord_7258084) baseStart_7258084 baseEnd_7258084 := by
    simpa [prefixWord, tailWord_7258084, baseEnd_7258084] using wordTrace_append hprefix tailTrace_7258084
  have hstable : (prefixWord ++ tailWord_7258084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258084).length < 2 ^ (prefixWord ++ tailWord_7258084).sum := by decide
  have hdescent : baseEnd_7258084 < baseStart_7258084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258111 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 4, 2]
def baseStart_7258111 : Nat := 118140960795 + 7258111 * 2 ^ 59
def prefixEnd_7258111 : Nat := 4983230072969 + 3 ^ 40 * 7258111 * 2
def baseEnd_7258111 : Nat := 3726899586685357341033061

theorem tailTrace_7258111 : CollatzResearch.WordTrace tailWord_7258111 prefixEnd_7258111 3726899586685357341033061 := by
  unfold tailWord_7258111
  simp only [CollatzResearch.WordTrace]
  refine ⟨264725056208110908515374187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176483370805407272343582791 264725056208110908515374187)
  ·
    refine ⟨397087584312166362773061281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264725056208110908515374187 397087584312166362773061281)
    ·
      refine ⟨297815688234124772079795961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397087584312166362773061281 297815688234124772079795961)
      ·
        refine ⟨223361766175593579059846971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297815688234124772079795961 223361766175593579059846971)
        ·
          refine ⟨335042649263390368589770457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223361766175593579059846971 335042649263390368589770457)
          ·
            refine ⟨251281986947542776442327843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335042649263390368589770457 251281986947542776442327843)
            ·
              refine ⟨376922980421314164663491765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251281986947542776442327843 376922980421314164663491765)
              ·
                refine ⟨35336529414498202937202353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376922980421314164663491765 35336529414498202937202353)
                ·
                  refine ⟨26502397060873652202901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35336529414498202937202353 26502397060873652202901765)
                  ·
                    refine ⟨4969199448913809788044081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26502397060873652202901765 4969199448913809788044081)
                    ·
                      refine ⟨3726899586685357341033061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969199448913809788044081 3726899586685357341033061)
                      ·
                        rfl

theorem cell23_7258111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_7258111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258111 prefixEnd_7258111 := by exact prefixLift 7258111
  have htrace : WordTrace (prefixWord ++ tailWord_7258111) baseStart_7258111 baseEnd_7258111 := by
    simpa [prefixWord, tailWord_7258111, baseEnd_7258111] using wordTrace_append hprefix tailTrace_7258111
  have hstable : (prefixWord ++ tailWord_7258111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258111).length < 2 ^ (prefixWord ++ tailWord_7258111).sum := by decide
  have hdescent : baseEnd_7258111 < baseStart_7258111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258131 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3]
def baseStart_7258131 : Nat := 118140960795 + 7258131 * 2 ^ 59
def prefixEnd_7258131 : Nat := 4983230072969 + 3 ^ 40 * 7258131 * 2
def baseEnd_7258131 : Nat := 3726909856298447262782969

theorem tailTrace_7258131 : CollatzResearch.WordTrace tailWord_7258131 prefixEnd_7258131 3726909856298447262782969 := by
  unfold tailWord_7258131
  simp only [CollatzResearch.WordTrace]
  refine ⟨264725785668038451931102247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176483857112025634620734831 264725785668038451931102247)
  ·
    refine ⟨397088678502057677896653371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264725785668038451931102247 397088678502057677896653371)
    ·
      refine ⟨595633017753086516844980057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397088678502057677896653371 595633017753086516844980057)
      ·
        refine ⟨446724763314814887633735043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595633017753086516844980057 446724763314814887633735043)
        ·
          refine ⟨670087144972222331450602565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446724763314814887633735043 670087144972222331450602565)
          ·
            refine ⟨125641339682291687146987981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670087144972222331450602565 125641339682291687146987981)
            ·
              refine ⟨47115502380859382680120493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125641339682291687146987981 47115502380859382680120493)
              ·
                refine ⟨17668313392822268505045185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47115502380859382680120493 17668313392822268505045185)
                ·
                  refine ⟨13251235044616701378783889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17668313392822268505045185 13251235044616701378783889)
                  ·
                    refine ⟨9938426283462526034087917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13251235044616701378783889 9938426283462526034087917)
                    ·
                      refine ⟨3726909856298447262782969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938426283462526034087917 3726909856298447262782969)
                      ·
                        rfl

theorem cell23_7258131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_7258131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258131 prefixEnd_7258131 := by exact prefixLift 7258131
  have htrace : WordTrace (prefixWord ++ tailWord_7258131) baseStart_7258131 baseEnd_7258131 := by
    simpa [prefixWord, tailWord_7258131, baseEnd_7258131] using wordTrace_append hprefix tailTrace_7258131
  have hstable : (prefixWord ++ tailWord_7258131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258131).length < 2 ^ (prefixWord ++ tailWord_7258131).sum := by decide
  have hdescent : baseEnd_7258131 < baseStart_7258131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258171 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 5, 2]
def baseStart_7258171 : Nat := 118140960795 + 7258171 * 2 ^ 59
def prefixEnd_7258171 : Nat := 4983230072969 + 3 ^ 40 * 7258171 * 2
def baseEnd_7258171 : Nat := 3726930395524627106282785

theorem tailTrace_7258171 : CollatzResearch.WordTrace tailWord_7258171 prefixEnd_7258171 3726930395524627106282785 := by
  unfold tailWord_7258171
  simp only [CollatzResearch.WordTrace]
  refine ⟨264727244587893538762558367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176484829725262359175038911 264727244587893538762558367)
  ·
    refine ⟨397090866881840308143837551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264727244587893538762558367 397090866881840308143837551)
    ·
      refine ⟨595636300322760462215756327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397090866881840308143837551 595636300322760462215756327)
      ·
        refine ⟨893454450484140693323634491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595636300322760462215756327 893454450484140693323634491)
        ·
          refine ⟨1340181675726211039985451737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893454450484140693323634491 1340181675726211039985451737)
          ·
            refine ⟨1005136256794658279989088803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340181675726211039985451737 1005136256794658279989088803)
            ·
              refine ⟨1507704385191987419983633205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005136256794658279989088803 1507704385191987419983633205)
              ·
                refine ⟨141347286111748820623465613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507704385191987419983633205 141347286111748820623465613)
                ·
                  refine ⟨53005232291905807733799605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141347286111748820623465613 53005232291905807733799605)
                  ·
                    refine ⟨4969240527366169475043713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53005232291905807733799605 4969240527366169475043713)
                    ·
                      refine ⟨3726930395524627106282785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969240527366169475043713 3726930395524627106282785)
                      ·
                        rfl

theorem cell23_7258171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5, 2].length) (baseStart_7258171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258171 prefixEnd_7258171 := by exact prefixLift 7258171
  have htrace : WordTrace (prefixWord ++ tailWord_7258171) baseStart_7258171 baseEnd_7258171 := by
    simpa [prefixWord, tailWord_7258171, baseEnd_7258171] using wordTrace_append hprefix tailTrace_7258171
  have hstable : (prefixWord ++ tailWord_7258171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258171).length < 2 ^ (prefixWord ++ tailWord_7258171).sum := by decide
  have hdescent : baseEnd_7258171 < baseStart_7258171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258181 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_7258181 : Nat := 118140960795 + 7258181 * 2 ^ 59
def prefixEnd_7258181 : Nat := 4983230072969 + 3 ^ 40 * 7258181 * 2
def baseEnd_7258181 : Nat := 1242311843443724022385913

theorem tailTrace_7258181 : CollatzResearch.WordTrace tailWord_7258181 prefixEnd_7258181 1242311843443724022385913 := by
  unfold tailWord_7258181
  simp only [CollatzResearch.WordTrace]
  refine ⟨264727609317857310470422397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176485072878571540313614931 264727609317857310470422397)
  ·
    refine ⟨99272853494196491426408399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264727609317857310470422397 99272853494196491426408399)
    ·
      refine ⟨148909280241294737139612599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99272853494196491426408399 148909280241294737139612599)
      ·
        refine ⟨223363920361942105709418899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148909280241294737139612599 223363920361942105709418899)
        ·
          refine ⟨335045880542913158564128349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223363920361942105709418899 335045880542913158564128349)
          ·
            refine ⟨125642205203592434461548131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335045880542913158564128349 125642205203592434461548131)
            ·
              refine ⟨188463307805388651692322197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125642205203592434461548131 188463307805388651692322197)
              ·
                refine ⟨8834217553377593048077603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188463307805388651692322197 8834217553377593048077603)
                ·
                  refine ⟨13251326330066389572116405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834217553377593048077603 13251326330066389572116405)
                  ·
                    refine ⟨1242311843443724022385913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13251326330066389572116405 1242311843443724022385913)
                    ·
                      rfl

theorem cell23_7258181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_7258181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258181 prefixEnd_7258181 := by exact prefixLift 7258181
  have htrace : WordTrace (prefixWord ++ tailWord_7258181) baseStart_7258181 baseEnd_7258181 := by
    simpa [prefixWord, tailWord_7258181, baseEnd_7258181] using wordTrace_append hprefix tailTrace_7258181
  have hstable : (prefixWord ++ tailWord_7258181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258181).length < 2 ^ (prefixWord ++ tailWord_7258181).sum := by decide
  have hdescent : baseEnd_7258181 < baseStart_7258181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258231 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_7258231 : Nat := 118140960795 + 7258231 * 2 ^ 59
def prefixEnd_7258231 : Nat := 4983230072969 + 3 ^ 40 * 7258231 * 2
def baseEnd_7258231 : Nat := 3726961204363896871532509

theorem tailTrace_7258231 : CollatzResearch.WordTrace tailWord_7258231 prefixEnd_7258231 3726961204363896871532509 := by
  unfold tailWord_7258231
  simp only [CollatzResearch.WordTrace]
  refine ⟨264729432967676169009742547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176486288645117446006495031 264729432967676169009742547)
  ·
    refine ⟨397094149451514253514613821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264729432967676169009742547 397094149451514253514613821)
    ·
      refine ⟨148910306044317845067980183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397094149451514253514613821 148910306044317845067980183)
      ·
        refine ⟨223365459066476767601970275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148910306044317845067980183 223365459066476767601970275)
        ·
          refine ⟨335048188599715151402955413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223365459066476767601970275 335048188599715151402955413)
          ·
            refine ⟨15705383840611647722013535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335048188599715151402955413 15705383840611647722013535)
            ·
              refine ⟨23558075760917471583020303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15705383840611647722013535 23558075760917471583020303)
              ·
                refine ⟨35337113641376207374530455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23558075760917471583020303 35337113641376207374530455)
                ·
                  refine ⟨53005670462064311061795683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35337113641376207374530455 53005670462064311061795683)
                  ·
                    refine ⟨79508505693096466592693525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53005670462064311061795683 79508505693096466592693525)
                    ·
                      refine ⟨3726961204363896871532509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79508505693096466592693525 3726961204363896871532509)
                      ·
                        rfl

theorem cell23_7258231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_7258231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258231 prefixEnd_7258231 := by exact prefixLift 7258231
  have htrace : WordTrace (prefixWord ++ tailWord_7258231) baseStart_7258231 baseEnd_7258231 := by
    simpa [prefixWord, tailWord_7258231, baseEnd_7258231] using wordTrace_append hprefix tailTrace_7258231
  have hstable : (prefixWord ++ tailWord_7258231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258231).length < 2 ^ (prefixWord ++ tailWord_7258231).sum := by decide
  have hdescent : baseEnd_7258231 < baseStart_7258231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258279 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 2, 4]
def baseStart_7258279 : Nat := 118140960795 + 7258279 * 2 ^ 59
def prefixEnd_7258279 : Nat := 4983230072969 + 3 ^ 40 * 7258279 * 2
def baseEnd_7258279 : Nat := 1242328617145104227910763

theorem tailTrace_7258279 : CollatzResearch.WordTrace tailWord_7258279 prefixEnd_7258279 1242328617145104227910763 := by
  unfold tailWord_7258279
  simp only [CollatzResearch.WordTrace]
  refine ⟨264731183671502273207489891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176487455781001515471659927 264731183671502273207489891)
  ·
    refine ⟨397096775507253409811234837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264731183671502273207489891 397096775507253409811234837)
    ·
      refine ⟨18613911351902503584901633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 397096775507253409811234837 18613911351902503584901633)
      ·
        refine ⟨13960433513926877688676225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18613911351902503584901633 13960433513926877688676225)
        ·
          refine ⟨10470325135445158266507169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13960433513926877688676225 10470325135445158266507169)
          ·
            refine ⟨7852743851583868699880377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10470325135445158266507169 7852743851583868699880377)
            ·
              refine ⟨5889557888687901524910283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852743851583868699880377 5889557888687901524910283)
              ·
                refine ⟨8834336833031852287365425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889557888687901524910283 8834336833031852287365425)
                ·
                  refine ⟨6625752624773889215524069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8834336833031852287365425 6625752624773889215524069)
                  ·
                    refine ⟨1242328617145104227910763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6625752624773889215524069 1242328617145104227910763)
                    ·
                      rfl

theorem cell23_7258279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_7258279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258279 prefixEnd_7258279 := by exact prefixLift 7258279
  have htrace : WordTrace (prefixWord ++ tailWord_7258279) baseStart_7258279 baseEnd_7258279 := by
    simpa [prefixWord, tailWord_7258279, baseEnd_7258279] using wordTrace_append hprefix tailTrace_7258279
  have hstable : (prefixWord ++ tailWord_7258279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258279).length < 2 ^ (prefixWord ++ tailWord_7258279).sum := by decide
  have hdescent : baseEnd_7258279 < baseStart_7258279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258286 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7258286 : Nat := 118140960795 + 7258286 * 2 ^ 59
def prefixEnd_7258286 : Nat := 4983230072969 + 3 ^ 40 * 7258286 * 2
def baseEnd_7258286 : Nat := 3726989445799894156344757

theorem tailTrace_7258286 : CollatzResearch.WordTrace tailWord_7258286 prefixEnd_7258286 3726989445799894156344757 := by
  unfold tailWord_7258286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33091429872809614175374339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176487625988317942268663141 33091429872809614175374339)
  ·
    refine ⟨49637144809214421263061509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33091429872809614175374339 49637144809214421263061509)
    ·
      refine ⟨9306964651727703986824033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49637144809214421263061509 9306964651727703986824033)
      ·
        refine ⟨6980223488795777990118025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9306964651727703986824033 6980223488795777990118025)
        ·
          refine ⟨5235167616596833492588519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6980223488795777990118025 5235167616596833492588519)
          ·
            refine ⟨7852751424895250238882779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235167616596833492588519 7852751424895250238882779)
            ·
              refine ⟨11779127137342875358324169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852751424895250238882779 11779127137342875358324169)
              ·
                refine ⟨8834345353007156518743127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11779127137342875358324169 8834345353007156518743127)
                ·
                  refine ⟨13251518029510734778114691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834345353007156518743127 13251518029510734778114691)
                  ·
                    refine ⟨19877277044266102167172037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13251518029510734778114691 19877277044266102167172037)
                    ·
                      refine ⟨3726989445799894156344757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19877277044266102167172037 3726989445799894156344757)
                      ·
                        rfl

theorem cell23_7258286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7258286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258286 prefixEnd_7258286 := by exact prefixLift 7258286
  have htrace : WordTrace (prefixWord ++ tailWord_7258286) baseStart_7258286 baseEnd_7258286 := by
    simpa [prefixWord, tailWord_7258286, baseEnd_7258286] using wordTrace_append hprefix tailTrace_7258286
  have hstable : (prefixWord ++ tailWord_7258286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258286).length < 2 ^ (prefixWord ++ tailWord_7258286).sum := by decide
  have hdescent : baseEnd_7258286 < baseStart_7258286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258289 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7258289 : Nat := 118140960795 + 7258289 * 2 ^ 59
def prefixEnd_7258289 : Nat := 4983230072969 + 3 ^ 40 * 7258289 * 2
def baseEnd_7258289 : Nat := 3726990986241857644607243

theorem tailTrace_7258289 : CollatzResearch.WordTrace tailWord_7258289 prefixEnd_7258289 3726990986241857644607243 := by
  unfold tailWord_7258289
  simp only [CollatzResearch.WordTrace]
  refine ⟨264731548401466044915353921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176487698934310696610235947 264731548401466044915353921)
  ·
    refine ⟨198548661301099533686515441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264731548401466044915353921 198548661301099533686515441)
    ·
      refine ⟨148911495975824650264886581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198548661301099533686515441 148911495975824650264886581)
      ·
        refine ⟨13960452747733560962333117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148911495975824650264886581 13960452747733560962333117)
        ·
          refine ⟨5235169780400085360874919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13960452747733560962333117 5235169780400085360874919)
          ·
            refine ⟨7852754670600128041312379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235169780400085360874919 7852754670600128041312379)
            ·
              refine ⟨11779132005900192061968569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852754670600128041312379 11779132005900192061968569)
              ·
                refine ⟨8834349004425144046476427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11779132005900192061968569 8834349004425144046476427)
                ·
                  refine ⟨13251523506637716069714641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834349004425144046476427 13251523506637716069714641)
                  ·
                    refine ⟨9938642629978287052285981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13251523506637716069714641 9938642629978287052285981)
                    ·
                      refine ⟨3726990986241857644607243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938642629978287052285981 3726990986241857644607243)
                      ·
                        rfl

theorem cell23_7258289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7258289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258289 prefixEnd_7258289 := by exact prefixLift 7258289
  have htrace : WordTrace (prefixWord ++ tailWord_7258289) baseStart_7258289 baseEnd_7258289 := by
    simpa [prefixWord, tailWord_7258289, baseEnd_7258289] using wordTrace_append hprefix tailTrace_7258289
  have hstable : (prefixWord ++ tailWord_7258289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258289).length < 2 ^ (prefixWord ++ tailWord_7258289).sum := by decide
  have hdescent : baseEnd_7258289 < baseStart_7258289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258295 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_7258295 : Nat := 118140960795 + 7258295 * 2 ^ 59
def prefixEnd_7258295 : Nat := 4983230072969 + 3 ^ 40 * 7258295 * 2
def baseEnd_7258295 : Nat := 3726994067125784621132215

theorem tailTrace_7258295 : CollatzResearch.WordTrace tailWord_7258295 prefixEnd_7258295 3726994067125784621132215 := by
  unfold tailWord_7258295
  simp only [CollatzResearch.WordTrace]
  refine ⟨264731767239444307940072339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176487844826296205293381559 264731767239444307940072339)
  ·
    refine ⟨397097650859166461910108509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264731767239444307940072339 397097650859166461910108509)
    ·
      refine ⟨148911619072187423216290691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397097650859166461910108509 148911619072187423216290691)
      ·
        refine ⟨223367428608281134824436037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148911619072187423216290691 223367428608281134824436037)
        ·
          refine ⟨41881392864052712779581757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223367428608281134824436037 41881392864052712779581757)
          ·
            refine ⟨15705522324019767292343159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41881392864052712779581757 15705522324019767292343159)
            ·
              refine ⟨23558283486029650938514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15705522324019767292343159 23558283486029650938514739)
              ·
                refine ⟨35337425229044476407772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23558283486029650938514739 35337425229044476407772109)
                ·
                  refine ⟨13251534460891678652914541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35337425229044476407772109 13251534460891678652914541)
                  ·
                    refine ⟨4969325422834379494842953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13251534460891678652914541 4969325422834379494842953)
                    ·
                      refine ⟨3726994067125784621132215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969325422834379494842953 3726994067125784621132215)
                      ·
                        rfl

theorem cell23_7258295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_7258295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258295 prefixEnd_7258295 := by exact prefixLift 7258295
  have htrace : WordTrace (prefixWord ++ tailWord_7258295) baseStart_7258295 baseEnd_7258295 := by
    simpa [prefixWord, tailWord_7258295, baseEnd_7258295] using wordTrace_append hprefix tailTrace_7258295
  have hstable : (prefixWord ++ tailWord_7258295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258295).length < 2 ^ (prefixWord ++ tailWord_7258295).sum := by decide
  have hdescent : baseEnd_7258295 < baseStart_7258295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258301 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_7258301 : Nat := 118140960795 + 7258301 * 2 ^ 59
def prefixEnd_7258301 : Nat := 4983230072969 + 3 ^ 40 * 7258301 * 2
def baseEnd_7258301 : Nat := 1242332382669903865885729

theorem tailTrace_7258301 : CollatzResearch.WordTrace tailWord_7258301 prefixEnd_7258301 1242332382669903865885729 := by
  unfold tailWord_7258301
  simp only [CollatzResearch.WordTrace]
  refine ⟨264731986077422570964790757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176487990718281713976527171 264731986077422570964790757)
  ·
    refine ⟨49637247389516732055898267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264731986077422570964790757 49637247389516732055898267)
    ·
      refine ⟨74455871084275098083847401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49637247389516732055898267 74455871084275098083847401)
      ·
        refine ⟨55841903313206323562885551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74455871084275098083847401 55841903313206323562885551)
        ·
          refine ⟨83762854969809485344328327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55841903313206323562885551 83762854969809485344328327)
          ·
            refine ⟨125644282454714228016492491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83762854969809485344328327 125644282454714228016492491)
            ·
              refine ⟨188466423682071342024738737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125644282454714228016492491 188466423682071342024738737)
              ·
                refine ⟨141349817761553506518554053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188466423682071342024738737 141349817761553506518554053)
                ·
                  refine ⟨26503090830291282472228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141349817761553506518554053 26503090830291282472228885)
                  ·
                    refine ⟨1242332382669903865885729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26503090830291282472228885 1242332382669903865885729)
                    ·
                      rfl

theorem cell23_7258301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_7258301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258301 prefixEnd_7258301 := by exact prefixLift 7258301
  have htrace : WordTrace (prefixWord ++ tailWord_7258301) baseStart_7258301 baseEnd_7258301 := by
    simpa [prefixWord, tailWord_7258301, baseEnd_7258301] using wordTrace_append hprefix tailTrace_7258301
  have hstable : (prefixWord ++ tailWord_7258301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258301).length < 2 ^ (prefixWord ++ tailWord_7258301).sum := by decide
  have hdescent : baseEnd_7258301 < baseStart_7258301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258306 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7258306 : Nat := 118140960795 + 7258306 * 2 ^ 59
def prefixEnd_7258306 : Nat := 4983230072969 + 3 ^ 40 * 7258306 * 2
def baseEnd_7258306 : Nat := 3726999715412984078094665

theorem tailTrace_7258306 : CollatzResearch.WordTrace tailWord_7258306 prefixEnd_7258306 3726999715412984078094665 := by
  unfold tailWord_7258306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66183042110601114204680693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176488112294936304545815181 66183042110601114204680693)
  ·
    refine ⟨6204660197868854456688815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66183042110601114204680693 6204660197868854456688815)
    ·
      refine ⟨9306990296803281685033223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204660197868854456688815 9306990296803281685033223)
      ·
        refine ⟨13960485445204922527549835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9306990296803281685033223 13960485445204922527549835)
        ·
          refine ⟨20940728167807383791324753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960485445204922527549835 20940728167807383791324753)
          ·
            refine ⟨15705546125855537843493565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20940728167807383791324753 15705546125855537843493565)
            ·
              refine ⟨5889579797195826691310087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15705546125855537843493565 5889579797195826691310087)
              ·
                refine ⟨8834369695793740036965131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889579797195826691310087 8834369695793740036965131)
                ·
                  refine ⟨13251554543690610055447697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834369695793740036965131 13251554543690610055447697)
                  ·
                    refine ⟨9938665907767957541585773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13251554543690610055447697 9938665907767957541585773)
                    ·
                      refine ⟨3726999715412984078094665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938665907767957541585773 3726999715412984078094665)
                      ·
                        rfl

theorem cell23_7258306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7258306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258306 prefixEnd_7258306 := by exact prefixLift 7258306
  have htrace : WordTrace (prefixWord ++ tailWord_7258306) baseStart_7258306 baseEnd_7258306 := by
    simpa [prefixWord, tailWord_7258306, baseEnd_7258306] using wordTrace_append hprefix tailTrace_7258306
  have hstable : (prefixWord ++ tailWord_7258306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258306).length < 2 ^ (prefixWord ++ tailWord_7258306).sum := by decide
  have hdescent : baseEnd_7258306 < baseStart_7258306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258328 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_7258328 : Nat := 118140960795 + 7258328 * 2 ^ 59
def prefixEnd_7258328 : Nat := 4983230072969 + 3 ^ 40 * 7258328 * 2
def baseEnd_7258328 : Nat := 3727011011987382992019563

theorem tailTrace_7258328 : CollatzResearch.WordTrace tailWord_7258328 prefixEnd_7258328 3727011011987382992019563 := by
  unfold tailWord_7258328
  simp only [CollatzResearch.WordTrace]
  refine ⟨132366485424162377288011819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176488647232216503050682425 132366485424162377288011819)
  ·
    refine ⟨198549728136243565932017729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132366485424162377288011819 198549728136243565932017729)
    ·
      refine ⟨148912296102182674449013297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198549728136243565932017729 148912296102182674449013297)
      ·
        refine ⟨111684222076637005836759973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148912296102182674449013297 111684222076637005836759973)
        ·
          refine ⟨20940791639369438594392495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111684222076637005836759973 20940791639369438594392495)
          ·
            refine ⟨31411187459054157891588743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20940791639369438594392495 31411187459054157891588743)
            ·
              refine ⟨47116781188581236837383115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31411187459054157891588743 47116781188581236837383115)
              ·
                refine ⟨70675171782871855256074673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47116781188581236837383115 70675171782871855256074673)
                ·
                  refine ⟨53006378837153891442056005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70675171782871855256074673 53006378837153891442056005)
                  ·
                    refine ⟨9938696031966354645385501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53006378837153891442056005 9938696031966354645385501)
                    ·
                      refine ⟨3727011011987382992019563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9938696031966354645385501 3727011011987382992019563)
                      ·
                        rfl

theorem cell23_7258328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_7258328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258328 prefixEnd_7258328 := by exact prefixLift 7258328
  have htrace : WordTrace (prefixWord ++ tailWord_7258328) baseStart_7258328 baseEnd_7258328 := by
    simpa [prefixWord, tailWord_7258328, baseEnd_7258328] using wordTrace_append hprefix tailTrace_7258328
  have hstable : (prefixWord ++ tailWord_7258328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258328).length < 2 ^ (prefixWord ++ tailWord_7258328).sum := by decide
  have hdescent : baseEnd_7258328 < baseStart_7258328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258378 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_7258378 : Nat := 118140960795 + 7258378 * 2 ^ 59
def prefixEnd_7258378 : Nat := 4983230072969 + 3 ^ 40 * 7258378 * 2
def baseEnd_7258378 : Nat := 1242345562006702598798111

theorem tailTrace_7258378 : CollatzResearch.WordTrace tailWord_7258378 prefixEnd_7258378 1242345562006702598798111 := by
  unfold tailWord_7258378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66183698624535903278835947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176489862998762408743562525 66183698624535903278835947)
  ·
    refine ⟨99275547936803854918253921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66183698624535903278835947 99275547936803854918253921)
    ·
      refine ⟨74456660952602891188690441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99275547936803854918253921 74456660952602891188690441)
      ·
        refine ⟨55842495714452168391517831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74456660952602891188690441 55842495714452168391517831)
        ·
          refine ⟨83763743571678252587276747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55842495714452168391517831 83763743571678252587276747)
          ·
            refine ⟨125645615357517378880915121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83763743571678252587276747 125645615357517378880915121)
            ·
              refine ⟨94234211518138034160686341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125645615357517378880915121 94234211518138034160686341)
              ·
                refine ⟨17668914659650881405128689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94234211518138034160686341 17668914659650881405128689)
                ·
                  refine ⟨13251685994738161053846517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17668914659650881405128689 13251685994738161053846517)
                  ·
                    refine ⟨1242345562006702598798111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13251685994738161053846517 1242345562006702598798111)
                    ·
                      rfl

theorem cell23_7258378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_7258378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258378 prefixEnd_7258378 := by exact prefixLift 7258378
  have htrace : WordTrace (prefixWord ++ tailWord_7258378) baseStart_7258378 baseEnd_7258378 := by
    simpa [prefixWord, tailWord_7258378, baseEnd_7258378] using wordTrace_append hprefix tailTrace_7258378
  have hstable : (prefixWord ++ tailWord_7258378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258378).length < 2 ^ (prefixWord ++ tailWord_7258378).sum := by decide
  have hdescent : baseEnd_7258378 < baseStart_7258378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258475 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 6, 3, 2]
def baseStart_7258475 : Nat := 118140960795 + 7258475 * 2 ^ 59
def prefixEnd_7258475 : Nat := 4983230072969 + 3 ^ 40 * 7258475 * 2
def baseEnd_7258475 : Nat := 3727086493643593916881387

theorem tailTrace_7258475 : CollatzResearch.WordTrace tailWord_7258475 prefixEnd_7258475 3727086493643593916881387 := by
  unfold tailWord_7258475
  simp only [CollatzResearch.WordTrace]
  refine ⟨264738332378792198681624879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176492221585861465787749919 264738332378792198681624879)
  ·
    refine ⟨397107498568188298022437319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264738332378792198681624879 397107498568188298022437319)
    ·
      refine ⟨595661247852282447033655979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397107498568188298022437319 595661247852282447033655979)
      ·
        refine ⟨893491871778423670550483969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595661247852282447033655979 893491871778423670550483969)
        ·
          refine ⟨670118903833817752912862977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893491871778423670550483969 670118903833817752912862977)
          ·
            refine ⟨502589177875363314684647233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670118903833817752912862977 502589177875363314684647233)
            ·
              refine ⟨376941883406522486013485425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502589177875363314684647233 376941883406522486013485425)
              ·
                refine ⟨282706412554891864510114069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376941883406522486013485425 282706412554891864510114069)
                ·
                  refine ⟨13251863088510556148911597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282706412554891864510114069 13251863088510556148911597)
                  ·
                    refine ⟨4969448658191458555841849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13251863088510556148911597 4969448658191458555841849)
                    ·
                      refine ⟨3727086493643593916881387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969448658191458555841849 3727086493643593916881387)
                      ·
                        rfl

theorem cell23_7258475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3, 2].length) (baseStart_7258475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258475 prefixEnd_7258475 := by exact prefixLift 7258475
  have htrace : WordTrace (prefixWord ++ tailWord_7258475) baseStart_7258475 baseEnd_7258475 := by
    simpa [prefixWord, tailWord_7258475, baseEnd_7258475] using wordTrace_append hprefix tailTrace_7258475
  have hstable : (prefixWord ++ tailWord_7258475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258475).length < 2 ^ (prefixWord ++ tailWord_7258475).sum := by decide
  have hdescent : baseEnd_7258475 < baseStart_7258475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258505 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_7258505 : Nat := 118140960795 + 7258505 * 2 ^ 59
def prefixEnd_7258505 : Nat := 4983230072969 + 3 ^ 40 * 7258505 * 2
def baseEnd_7258505 : Nat := 3727101898063228799506249

theorem tailTrace_7258505 : CollatzResearch.WordTrace tailWord_7258505 prefixEnd_7258505 3727101898063228799506249 := by
  unfold tailWord_7258505
  simp only [CollatzResearch.WordTrace]
  refine ⟨264739426568683513805216969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176492951045789009203477979 264739426568683513805216969)
  ·
    refine ⟨198554569926512635353912727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264739426568683513805216969 198554569926512635353912727)
    ·
      refine ⟨297831854889768953030869091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198554569926512635353912727 297831854889768953030869091)
      ·
        refine ⟨446747782334653429546303637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297831854889768953030869091 446747782334653429546303637)
        ·
          refine ⟨20941302296936879509982983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446747782334653429546303637 20941302296936879509982983)
          ·
            refine ⟨31411953445405319264974475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20941302296936879509982983 31411953445405319264974475)
            ·
              refine ⟨47117930168107978897461713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31411953445405319264974475 47117930168107978897461713)
              ·
                refine ⟨35338447626080984173096285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47117930168107978897461713 35338447626080984173096285)
                ·
                  refine ⟨13251917859780369064911107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35338447626080984173096285 13251917859780369064911107)
                  ·
                    refine ⟨19877876789670553597366661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13251917859780369064911107 19877876789670553597366661)
                    ·
                      refine ⟨3727101898063228799506249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19877876789670553597366661 3727101898063228799506249)
                      ·
                        rfl

theorem cell23_7258505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_7258505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258505 prefixEnd_7258505 := by exact prefixLift 7258505
  have htrace : WordTrace (prefixWord ++ tailWord_7258505) baseStart_7258505 baseEnd_7258505 := by
    simpa [prefixWord, tailWord_7258505, baseEnd_7258505] using wordTrace_append hprefix tailTrace_7258505
  have hstable : (prefixWord ++ tailWord_7258505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258505).length < 2 ^ (prefixWord ++ tailWord_7258505).sum := by decide
  have hdescent : baseEnd_7258505 < baseStart_7258505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258526 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7258526 : Nat := 118140960795 + 7258526 * 2 ^ 59
def prefixEnd_7258526 : Nat := 4983230072969 + 3 ^ 40 * 7258526 * 2
def baseEnd_7258526 : Nat := 3727112681156973217343653

theorem tailTrace_7258526 : CollatzResearch.WordTrace tailWord_7258526 prefixEnd_7258526 3727112681156973217343653 := by
  unfold tailWord_7258526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33092524062700929298966429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176493461667738289594487621 33092524062700929298966429)
  ·
    refine ⟨12409696523512848487112411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33092524062700929298966429 12409696523512848487112411)
    ·
      refine ⟨18614544785269272730668617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409696523512848487112411 18614544785269272730668617)
      ·
        refine ⟨13960908588951954548001463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18614544785269272730668617 13960908588951954548001463)
        ·
          refine ⟨20941362883427931822002195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960908588951954548001463 20941362883427931822002195)
          ·
            refine ⟨31412044325141897733003293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20941362883427931822002195 31412044325141897733003293)
            ·
              refine ⟨11779516621928211649876235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31412044325141897733003293 11779516621928211649876235)
              ·
                refine ⟨17669274932892317474814353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11779516621928211649876235 17669274932892317474814353)
                ·
                  refine ⟨13251956199669238106110765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17669274932892317474814353 13251956199669238106110765)
                  ·
                    refine ⟨4969483574875964289791537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13251956199669238106110765 4969483574875964289791537)
                    ·
                      refine ⟨3727112681156973217343653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969483574875964289791537 3727112681156973217343653)
                      ·
                        rfl

theorem cell23_7258526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7258526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258526 prefixEnd_7258526 := by exact prefixLift 7258526
  have htrace : WordTrace (prefixWord ++ tailWord_7258526) baseStart_7258526 baseEnd_7258526 := by
    simpa [prefixWord, tailWord_7258526, baseEnd_7258526] using wordTrace_append hprefix tailTrace_7258526
  have hstable : (prefixWord ++ tailWord_7258526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258526).length < 2 ^ (prefixWord ++ tailWord_7258526).sum := by decide
  have hdescent : baseEnd_7258526 < baseStart_7258526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258536 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7258536 : Nat := 118140960795 + 7258536 * 2 ^ 59
def prefixEnd_7258536 : Nat := 4983230072969 + 3 ^ 40 * 7258536 * 2
def baseEnd_7258536 : Nat := 1242372605321172726072869

theorem tailTrace_7258536 : CollatzResearch.WordTrace tailWord_7258536 prefixEnd_7258536 1242372605321172726072869 := by
  unfold tailWord_7258536
  simp only [CollatzResearch.WordTrace]
  refine ⟨132370278615785603049797731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176493704821047470733063641 132370278615785603049797731)
  ·
    refine ⟨198555417923678404574696597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132370278615785603049797731 198555417923678404574696597)
    ·
      refine ⟨9307285215172425214438903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198555417923678404574696597 9307285215172425214438903)
      ·
        refine ⟨13960927822758637821658355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307285215172425214438903 13960927822758637821658355)
        ·
          refine ⟨20941391734137956732487533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960927822758637821658355 20941391734137956732487533)
          ·
            refine ⟨7853021900301733774682825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20941391734137956732487533 7853021900301733774682825)
            ·
              refine ⟨5889766425226300331012119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853021900301733774682825 5889766425226300331012119)
              ·
                refine ⟨8834649637839450496518179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889766425226300331012119 8834649637839450496518179)
                ·
                  refine ⟨13251974456759175744777269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834649637839450496518179 13251974456759175744777269)
                  ·
                    refine ⟨1242372605321172726072869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13251974456759175744777269 1242372605321172726072869)
                    ·
                      rfl

theorem cell23_7258536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7258536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258536 prefixEnd_7258536 := by exact prefixLift 7258536
  have htrace : WordTrace (prefixWord ++ tailWord_7258536) baseStart_7258536 baseEnd_7258536 := by
    simpa [prefixWord, tailWord_7258536, baseEnd_7258536] using wordTrace_append hprefix tailTrace_7258536
  have hstable : (prefixWord ++ tailWord_7258536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258536).length < 2 ^ (prefixWord ++ tailWord_7258536).sum := by decide
  have hdescent : baseEnd_7258536 < baseStart_7258536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258556 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7258556 : Nat := 118140960795 + 7258556 * 2 ^ 59
def prefixEnd_7258556 : Nat := 4983230072969 + 3 ^ 40 * 7258556 * 2
def baseEnd_7258556 : Nat := 3727128085576608099968515

theorem tailTrace_7258556 : CollatzResearch.WordTrace tailWord_7258556 prefixEnd_7258556 3727128085576608099968515 := by
  unfold tailWord_7258556
  simp only [CollatzResearch.WordTrace]
  refine ⟨132370643345749374757661761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176494191127665833010215681 132370643345749374757661761)
  ·
    refine ⟨99277982509312031068246321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132370643345749374757661761 99277982509312031068246321)
    ·
      refine ⟨74458486881984023301184741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99277982509312031068246321 74458486881984023301184741)
      ·
        refine ⟨13960966290372004368972139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74458486881984023301184741 13960966290372004368972139)
        ·
          refine ⟨20941449435558006553458209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13960966290372004368972139 20941449435558006553458209)
          ·
            refine ⟨15706087076668504915093657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20941449435558006553458209 15706087076668504915093657)
            ·
              refine ⟨11779565307501378686320243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15706087076668504915093657 11779565307501378686320243)
              ·
                refine ⟨17669347961252068029480365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11779565307501378686320243 17669347961252068029480365)
                ·
                  refine ⟨6626005485469525511055137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17669347961252068029480365 6626005485469525511055137)
                  ·
                    refine ⟨4969504114102144133291353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6626005485469525511055137 4969504114102144133291353)
                    ·
                      refine ⟨3727128085576608099968515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969504114102144133291353 3727128085576608099968515)
                      ·
                        rfl

theorem cell23_7258556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7258556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258556 prefixEnd_7258556 := by exact prefixLift 7258556
  have htrace : WordTrace (prefixWord ++ tailWord_7258556) baseStart_7258556 baseEnd_7258556 := by
    simpa [prefixWord, tailWord_7258556, baseEnd_7258556] using wordTrace_append hprefix tailTrace_7258556
  have hstable : (prefixWord ++ tailWord_7258556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258556).length < 2 ^ (prefixWord ++ tailWord_7258556).sum := by decide
  have hdescent : baseEnd_7258556 < baseStart_7258556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258599 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7258599 : Nat := 118140960795 + 7258599 * 2 ^ 59
def prefixEnd_7258599 : Nat := 4983230072969 + 3 ^ 40 * 7258599 * 2
def baseEnd_7258599 : Nat := 3727150165244751431730817

theorem tailTrace_7258599 : CollatzResearch.WordTrace tailWord_7258599 prefixEnd_7258599 3727150165244751431730817 := by
  unfold tailWord_7258599
  simp only [CollatzResearch.WordTrace]
  refine ⟨264742855030342967859138851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176495236686895311906092567 264742855030342967859138851)
  ·
    refine ⟨397114282545514451788708277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264742855030342967859138851 397114282545514451788708277)
    ·
      refine ⟨37229463988641979855191401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397114282545514451788708277 37229463988641979855191401)
      ·
        refine ⟨27922097991481484891393551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37229463988641979855191401 27922097991481484891393551)
        ·
          refine ⟨41883146987222227337090327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27922097991481484891393551 41883146987222227337090327)
          ·
            refine ⟨62824720480833341005635491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41883146987222227337090327 62824720480833341005635491)
            ·
              refine ⟨94237080721250011508453237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62824720480833341005635491 94237080721250011508453237)
              ·
                refine ⟨8834726317617188578917491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94237080721250011508453237 8834726317617188578917491)
                ·
                  refine ⟨13252089476425782868376237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8834726317617188578917491 13252089476425782868376237)
                  ·
                    refine ⟨4969533553659668575641089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13252089476425782868376237 4969533553659668575641089)
                    ·
                      refine ⟨3727150165244751431730817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969533553659668575641089 3727150165244751431730817)
                      ·
                        rfl

theorem cell23_7258599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7258599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258599 prefixEnd_7258599 := by exact prefixLift 7258599
  have htrace : WordTrace (prefixWord ++ tailWord_7258599) baseStart_7258599 baseEnd_7258599 := by
    simpa [prefixWord, tailWord_7258599, baseEnd_7258599] using wordTrace_append hprefix tailTrace_7258599
  have hstable : (prefixWord ++ tailWord_7258599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258599).length < 2 ^ (prefixWord ++ tailWord_7258599).sum := by decide
  have hdescent : baseEnd_7258599 < baseStart_7258599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258672 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2]
def baseStart_7258672 : Nat := 118140960795 + 7258672 * 2 ^ 59
def prefixEnd_7258672 : Nat := 4983230072969 + 3 ^ 40 * 7258672 * 2
def baseEnd_7258672 : Nat := 3727187649332529646117981

theorem tailTrace_7258672 : CollatzResearch.WordTrace tailWord_7258672 prefixEnd_7258672 3727187649332529646117981 := by
  unfold tailWord_7258672
  simp only [CollatzResearch.WordTrace]
  refine ⟨132372758779539250663273135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176497011706052334217697513 132372758779539250663273135)
  ·
    refine ⟨198559138169308875994909703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132372758779539250663273135 198559138169308875994909703)
    ·
      refine ⟨297838707253963313992364555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198559138169308875994909703 297838707253963313992364555)
      ·
        refine ⟨446758060880944970988546833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297838707253963313992364555 446758060880944970988546833)
        ·
          refine ⟨335068545660708728241410125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446758060880944970988546833 335068545660708728241410125)
          ·
            refine ⟨125650704622765773090528797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335068545660708728241410125 125650704622765773090528797)
            ·
              refine ⟨47119014233537164908948299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125650704622765773090528797 47119014233537164908948299)
              ·
                refine ⟨70678521350305747363422449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47119014233537164908948299 70678521350305747363422449)
                ·
                  refine ⟨53008891012729310522566837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70678521350305747363422449 53008891012729310522566837)
                  ·
                    refine ⟨4969583532443372861490641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53008891012729310522566837 4969583532443372861490641)
                    ·
                      refine ⟨3727187649332529646117981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969583532443372861490641 3727187649332529646117981)
                      ·
                        rfl

theorem cell23_7258672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 5, 2].length) (baseStart_7258672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258672 prefixEnd_7258672 := by exact prefixLift 7258672
  have htrace : WordTrace (prefixWord ++ tailWord_7258672) baseStart_7258672 baseEnd_7258672 := by
    simpa [prefixWord, tailWord_7258672, baseEnd_7258672] using wordTrace_append hprefix tailTrace_7258672
  have hstable : (prefixWord ++ tailWord_7258672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258672).length < 2 ^ (prefixWord ++ tailWord_7258672).sum := by decide
  have hdescent : baseEnd_7258672 < baseStart_7258672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258675 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_7258675 : Nat := 118140960795 + 7258675 * 2 ^ 59
def prefixEnd_7258675 : Nat := 4983230072969 + 3 ^ 40 * 7258675 * 2
def baseEnd_7258675 : Nat := 3727189189774493134380467

theorem tailTrace_7258675 : CollatzResearch.WordTrace tailWord_7258675 prefixEnd_7258675 3727189189774493134380467 := by
  unfold tailWord_7258675
  simp only [CollatzResearch.WordTrace]
  refine ⟨264745626978067632838905479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176497084652045088559270319 264745626978067632838905479)
  ·
    refine ⟨397118440467101449258358219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264745626978067632838905479 397118440467101449258358219)
    ·
      refine ⟨595677660700652173887537329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397118440467101449258358219 595677660700652173887537329)
      ·
        refine ⟨446758245525489130415652997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595677660700652173887537329 446758245525489130415652997)
        ·
          refine ⟨83767171036029211952934937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446758245525489130415652997 83767171036029211952934937)
          ·
            refine ⟨62825378277021908964701203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83767171036029211952934937 62825378277021908964701203)
            ·
              refine ⟨94238067415532863447051805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62825378277021908964701203 94238067415532863447051805)
              ·
                refine ⟨35339275280824823792644427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94238067415532863447051805 35339275280824823792644427)
                ·
                  refine ⟨53008912921237235688966641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35339275280824823792644427 53008912921237235688966641)
                  ·
                    refine ⟨39756684690927926766724981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53008912921237235688966641 39756684690927926766724981)
                    ·
                      refine ⟨3727189189774493134380467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39756684690927926766724981 3727189189774493134380467)
                      ·
                        rfl

theorem cell23_7258675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_7258675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258675 prefixEnd_7258675 := by exact prefixLift 7258675
  have htrace : WordTrace (prefixWord ++ tailWord_7258675) baseStart_7258675 baseEnd_7258675 := by
    simpa [prefixWord, tailWord_7258675, baseEnd_7258675] using wordTrace_append hprefix tailTrace_7258675
  have hstable : (prefixWord ++ tailWord_7258675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258675).length < 2 ^ (prefixWord ++ tailWord_7258675).sum := by decide
  have hdescent : baseEnd_7258675 < baseStart_7258675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
