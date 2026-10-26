import V185TrunkScan23Chunk1335

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7912664 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 5]
def baseStart_7912664 : Nat := 118140960795 + 7912664 * 2 ^ 59
def prefixEnd_7912664 : Nat := 4983230072969 + 3 ^ 40 * 7912664 * 2
def baseEnd_7912664 : Nat := 451444432169748322156703

theorem tailTrace_7912664 : CollatzResearch.WordTrace tailWord_7912664 prefixEnd_7912664 451444432169748322156703 := by
  unfold tailWord_7912664
  simp only [CollatzResearch.WordTrace]
  refine ⟨144299282702888589133908523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192399043603851452178544697 144299282702888589133908523)
  ·
    refine ⟨216448924054332883700862785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144299282702888589133908523 216448924054332883700862785)
    ·
      refine ⟨162336693040749662775647089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216448924054332883700862785 162336693040749662775647089)
      ·
        refine ⟨121752519780562247081735317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162336693040749662775647089 121752519780562247081735317)
        ·
          refine ⟨5707149364713855331956343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121752519780562247081735317 5707149364713855331956343)
          ·
            refine ⟨8560724047070782997934515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707149364713855331956343 8560724047070782997934515)
            ·
              refine ⟨12841086070606174496901773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560724047070782997934515 12841086070606174496901773)
              ·
                refine ⟨4815407276477315436338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12841086070606174496901773 4815407276477315436338165)
                ·
                  refine ⟨451444432169748322156703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815407276477315436338165 451444432169748322156703)
                  ·
                    rfl

theorem cell23_7912664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 5].length) (baseStart_7912664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912664 prefixEnd_7912664 := by exact prefixLift 7912664
  have htrace : WordTrace (prefixWord ++ tailWord_7912664) baseStart_7912664 baseEnd_7912664 := by
    simpa [prefixWord, tailWord_7912664, baseEnd_7912664] using wordTrace_append hprefix tailTrace_7912664
  have hstable : (prefixWord ++ tailWord_7912664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912664).length < 2 ^ (prefixWord ++ tailWord_7912664).sum := by decide
  have hdescent : baseEnd_7912664 < baseStart_7912664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912680 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7912680 : Nat := 118140960795 + 7912680 * 2 ^ 59
def prefixEnd_7912680 : Nat := 4983230072969 + 3 ^ 40 * 7912680 * 2
def baseEnd_7912680 : Nat := 4063008105218206836810253

theorem tailTrace_7912680 : CollatzResearch.WordTrace tailWord_7912680 prefixEnd_7912680 4063008105218206836810253 := by
  unfold tailWord_7912680
  simp only [CollatzResearch.WordTrace]
  refine ⟨144299574486859606500199747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192399432649146142000266329 144299574486859606500199747)
  ·
    refine ⟨216449361730289409750299621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144299574486859606500199747 216449361730289409750299621)
    ·
      refine ⟨40584255324429264328181179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216449361730289409750299621 40584255324429264328181179)
      ·
        refine ⟨60876382986643896492271769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40584255324429264328181179 60876382986643896492271769)
        ·
          refine ⟨45657287239982922369203827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60876382986643896492271769 45657287239982922369203827)
          ·
            refine ⟨68485930859974383553805741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45657287239982922369203827 68485930859974383553805741)
            ·
              refine ⟨25682224072490393832677153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68485930859974383553805741 25682224072490393832677153)
              ·
                refine ⟨19261668054367795374507865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682224072490393832677153 19261668054367795374507865)
                ·
                  refine ⟨14446251040775846530880899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19261668054367795374507865 14446251040775846530880899)
                  ·
                    refine ⟨21669376561163769796321349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14446251040775846530880899 21669376561163769796321349)
                    ·
                      refine ⟨4063008105218206836810253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21669376561163769796321349 4063008105218206836810253)
                      ·
                        rfl

theorem cell23_7912680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7912680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912680 prefixEnd_7912680 := by exact prefixLift 7912680
  have htrace : WordTrace (prefixWord ++ tailWord_7912680) baseStart_7912680 baseEnd_7912680 := by
    simpa [prefixWord, tailWord_7912680, baseEnd_7912680] using wordTrace_append hprefix tailTrace_7912680
  have hstable : (prefixWord ++ tailWord_7912680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912680).length < 2 ^ (prefixWord ++ tailWord_7912680).sum := by decide
  have hdescent : baseEnd_7912680 < baseStart_7912680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912692 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7912692 : Nat := 118140960795 + 7912692 * 2 ^ 59
def prefixEnd_7912692 : Nat := 4983230072969 + 3 ^ 40 * 7912692 * 2
def baseEnd_7912692 : Nat := 4063014266986060789860199

theorem tailTrace_7912692 : CollatzResearch.WordTrace tailWord_7912692 prefixEnd_7912692 4063014266986060789860199 := by
  unfold tailWord_7912692
  simp only [CollatzResearch.WordTrace]
  refine ⟨144299793324837869524918165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192399724433117159366557553 144299793324837869524918165)
  ·
    refine ⟨6764052812101775133980539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144299793324837869524918165 6764052812101775133980539)
    ·
      refine ⟨10146079218152662700970809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764052812101775133980539 10146079218152662700970809)
      ·
        refine ⟨7609559413614497025728107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10146079218152662700970809 7609559413614497025728107)
        ·
          refine ⟨11414339120421745538592161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609559413614497025728107 11414339120421745538592161)
          ·
            refine ⟨8560754340316309153944121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11414339120421745538592161 8560754340316309153944121)
            ·
              refine ⟨6420565755237231865458091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560754340316309153944121 6420565755237231865458091)
              ·
                refine ⟨9630848632855847798187137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420565755237231865458091 9630848632855847798187137)
                ·
                  refine ⟨7223136474641885848640353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630848632855847798187137 7223136474641885848640353)
                  ·
                    refine ⟨5417352355981414386480265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223136474641885848640353 5417352355981414386480265)
                    ·
                      refine ⟨4063014266986060789860199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417352355981414386480265 4063014266986060789860199)
                      ·
                        rfl

theorem cell23_7912692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7912692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912692 prefixEnd_7912692 := by exact prefixLift 7912692
  have htrace : WordTrace (prefixWord ++ tailWord_7912692) baseStart_7912692 baseEnd_7912692 := by
    simpa [prefixWord, tailWord_7912692, baseEnd_7912692] using wordTrace_append hprefix tailTrace_7912692
  have hstable : (prefixWord ++ tailWord_7912692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912692).length < 2 ^ (prefixWord ++ tailWord_7912692).sum := by decide
  have hdescent : baseEnd_7912692 < baseStart_7912692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912741 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_7912741 : Nat := 118140960795 + 7912741 * 2 ^ 59
def prefixEnd_7912741 : Nat := 4983230072969 + 3 ^ 40 * 7912741 * 2
def baseEnd_7912741 : Nat := 1354346475846043699382491

theorem tailTrace_7912741 : CollatzResearch.WordTrace tailWord_7912741 prefixEnd_7912741 1354346475846043699382491 := by
  unfold tailWord_7912741
  simp only [CollatzResearch.WordTrace]
  refine ⟨288601373826498220418370077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192400915884332146945580051 288601373826498220418370077)
  ·
    refine ⟨108225515184936832656888779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288601373826498220418370077 108225515184936832656888779)
    ·
      refine ⟨162338272777405248985333169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108225515184936832656888779 162338272777405248985333169)
      ·
        refine ⟨121753704583053936738999877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162338272777405248985333169 121753704583053936738999877)
        ·
          refine ⟨22828819609322613138562477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121753704583053936738999877 22828819609322613138562477)
          ·
            refine ⟨8560807353495979926960929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22828819609322613138562477 8560807353495979926960929)
            ·
              refine ⟨6420605515121984945220697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560807353495979926960929 6420605515121984945220697)
              ·
                refine ⟨4815454136341488708915523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6420605515121984945220697 4815454136341488708915523)
                ·
                  refine ⟨7223181204512233063373285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815454136341488708915523 7223181204512233063373285)
                  ·
                    refine ⟨1354346475846043699382491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7223181204512233063373285 1354346475846043699382491)
                    ·
                      rfl

theorem cell23_7912741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_7912741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912741 prefixEnd_7912741 := by exact prefixLift 7912741
  have htrace : WordTrace (prefixWord ++ tailWord_7912741) baseStart_7912741 baseEnd_7912741 := by
    simpa [prefixWord, tailWord_7912741, baseEnd_7912741] using wordTrace_append hprefix tailTrace_7912741
  have hstable : (prefixWord ++ tailWord_7912741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912741).length < 2 ^ (prefixWord ++ tailWord_7912741).sum := by decide
  have hdescent : baseEnd_7912741 < baseStart_7912741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912780 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_7912780 : Nat := 118140960795 + 7912780 * 2 ^ 59
def prefixEnd_7912780 : Nat := 4983230072969 + 3 ^ 40 * 7912780 * 2
def baseEnd_7912780 : Nat := 1354353151094552148519931

theorem tailTrace_7912780 : CollatzResearch.WordTrace tailWord_7912780 prefixEnd_7912780 1354353151094552148519931 := by
  unfold tailWord_7912780
  simp only [CollatzResearch.WordTrace]
  refine ⟨144301398136678465039519897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192401864182237953386026529 144301398136678465039519897)
  ·
    refine ⟨108226048602508848779639923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144301398136678465039519897 108226048602508848779639923)
    ·
      refine ⟨162339072903763273169459885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108226048602508848779639923 162339072903763273169459885)
      ·
        refine ⟨60877152338911227438547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162339072903763273169459885 60877152338911227438547457)
        ·
          refine ⟨45657864254183420578910593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60877152338911227438547457 45657864254183420578910593)
          ·
            refine ⟨34243398190637565434182945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45657864254183420578910593 34243398190637565434182945)
            ·
              refine ⟨25682548642978174075637209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34243398190637565434182945 25682548642978174075637209)
              ·
                refine ⟨19261911482233630556727907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682548642978174075637209 19261911482233630556727907)
                ·
                  refine ⟨28892867223350445835091861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19261911482233630556727907 28892867223350445835091861)
                  ·
                    refine ⟨1354353151094552148519931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28892867223350445835091861 1354353151094552148519931)
                    ·
                      rfl

theorem cell23_7912780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_7912780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912780 prefixEnd_7912780 := by exact prefixLift 7912780
  have htrace : WordTrace (prefixWord ++ tailWord_7912780) baseStart_7912780 baseEnd_7912780 := by
    simpa [prefixWord, tailWord_7912780, baseEnd_7912780] using wordTrace_append hprefix tailTrace_7912780
  have hstable : (prefixWord ++ tailWord_7912780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912780).length < 2 ^ (prefixWord ++ tailWord_7912780).sum := by decide
  have hdescent : baseEnd_7912780 < baseStart_7912780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912783 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_7912783 : Nat := 118140960795 + 7912783 * 2 ^ 59
def prefixEnd_7912783 : Nat := 4983230072969 + 3 ^ 40 * 7912783 * 2
def baseEnd_7912783 : Nat := 4063060993725619933822279

theorem tailTrace_7912783 : CollatzResearch.WordTrace tailWord_7912783 prefixEnd_7912783 4063060993725619933822279 := by
  unfold tailWord_7912783
  simp only [CollatzResearch.WordTrace]
  refine ⟨288602905692346061591399003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192401937128230707727599335 288602905692346061591399003)
  ·
    refine ⟨432904358538519092387098505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288602905692346061591399003 432904358538519092387098505)
    ·
      refine ⟨324678268903889319290323879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432904358538519092387098505 324678268903889319290323879)
      ·
        refine ⟨487017403355833978935485819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324678268903889319290323879 487017403355833978935485819)
        ·
          refine ⟨730526105033750968403228729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487017403355833978935485819 730526105033750968403228729)
          ·
            refine ⟨547894578775313226302421547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730526105033750968403228729 547894578775313226302421547)
            ·
              refine ⟨821841868162969839453632321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547894578775313226302421547 821841868162969839453632321)
              ·
                refine ⟨616381401122227379590224241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821841868162969839453632321 616381401122227379590224241)
                ·
                  refine ⟨462286050841670534692668181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616381401122227379590224241 462286050841670534692668181)
                  ·
                    refine ⟨21669658633203306313718821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 462286050841670534692668181 21669658633203306313718821)
                    ·
                      refine ⟨4063060993725619933822279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21669658633203306313718821 4063060993725619933822279)
                      ·
                        rfl

theorem cell23_7912783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_7912783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912783 prefixEnd_7912783 := by exact prefixLift 7912783
  have htrace : WordTrace (prefixWord ++ tailWord_7912783) baseStart_7912783 baseEnd_7912783 := by
    simpa [prefixWord, tailWord_7912783, baseEnd_7912783] using wordTrace_append hprefix tailTrace_7912783
  have hstable : (prefixWord ++ tailWord_7912783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912783).length < 2 ^ (prefixWord ++ tailWord_7912783).sum := by decide
  have hdescent : baseEnd_7912783 < baseStart_7912783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912787 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 5, 2, 2]
def baseStart_7912787 : Nat := 118140960795 + 7912787 * 2 ^ 59
def prefixEnd_7912787 : Nat := 4983230072969 + 3 ^ 40 * 7912787 * 2
def baseEnd_7912787 : Nat := 4063063047648237918172261

theorem tailTrace_7912787 : CollatzResearch.WordTrace tailWord_7912787 prefixEnd_7912787 4063063047648237918172261 := by
  unfold tailWord_7912787
  simp only [CollatzResearch.WordTrace]
  refine ⟨288603051584331570274544615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192402034389554380183029743 288603051584331570274544615)
  ·
    refine ⟨432904577376497355411816923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288603051584331570274544615 432904577376497355411816923)
    ·
      refine ⟨649356866064746033117725385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432904577376497355411816923 649356866064746033117725385)
      ·
        refine ⟨487017649548559524838294039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649356866064746033117725385 487017649548559524838294039)
        ·
          refine ⟨730526474322839287257441059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487017649548559524838294039 730526474322839287257441059)
          ·
            refine ⟨1095789711484258930886161589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730526474322839287257441059 1095789711484258930886161589)
            ·
              refine ⟨102730285451649274770577649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1095789711484258930886161589 102730285451649274770577649)
              ·
                refine ⟨77047714088736956077933237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102730285451649274770577649 77047714088736956077933237)
                ·
                  refine ⟨7223223195819089632306241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77047714088736956077933237 7223223195819089632306241)
                  ·
                    refine ⟨5417417396864317224229681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223223195819089632306241 5417417396864317224229681)
                    ·
                      refine ⟨4063063047648237918172261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417417396864317224229681 4063063047648237918172261)
                      ·
                        rfl

theorem cell23_7912787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 2, 2].length) (baseStart_7912787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912787 prefixEnd_7912787 := by exact prefixLift 7912787
  have htrace : WordTrace (prefixWord ++ tailWord_7912787) baseStart_7912787 baseEnd_7912787 := by
    simpa [prefixWord, tailWord_7912787, baseEnd_7912787] using wordTrace_append hprefix tailTrace_7912787
  have hstable : (prefixWord ++ tailWord_7912787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912787).length < 2 ^ (prefixWord ++ tailWord_7912787).sum := by decide
  have hdescent : baseEnd_7912787 < baseStart_7912787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912804 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_7912804 : Nat := 118140960795 + 7912804 * 2 ^ 59
def prefixEnd_7912804 : Nat := 4983230072969 + 3 ^ 40 * 7912804 * 2
def baseEnd_7912804 : Nat := 4063071776819364351659683

theorem tailTrace_7912804 : CollatzResearch.WordTrace tailWord_7912804 prefixEnd_7912804 4063071776819364351659683 := by
  unfold tailWord_7912804
  simp only [CollatzResearch.WordTrace]
  refine ⟨144301835812634991088956733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192402447750179988118608977 144301835812634991088956733)
  ·
    refine ⟨54113188429738121658358775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144301835812634991088956733 54113188429738121658358775)
    ·
      refine ⟨81169782644607182487538163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54113188429738121658358775 81169782644607182487538163)
      ·
        refine ⟨121754673966910773731307245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81169782644607182487538163 121754673966910773731307245)
        ·
          refine ⟨45658002737591540149240217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121754673966910773731307245 45658002737591540149240217)
          ·
            refine ⟨34243502053193655111930163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45658002737591540149240217 34243502053193655111930163)
            ·
              refine ⟨51365253079790482667895245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34243502053193655111930163 51365253079790482667895245)
              ·
                refine ⟨19261969904921431000460717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51365253079790482667895245 19261969904921431000460717)
                ·
                  refine ⟨7223238714345536625172769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19261969904921431000460717 7223238714345536625172769)
                  ·
                    refine ⟨5417429035759152468879577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223238714345536625172769 5417429035759152468879577)
                    ·
                      refine ⟨4063071776819364351659683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417429035759152468879577 4063071776819364351659683)
                      ·
                        rfl

theorem cell23_7912804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_7912804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912804 prefixEnd_7912804 := by exact prefixLift 7912804
  have htrace : WordTrace (prefixWord ++ tailWord_7912804) baseStart_7912804 baseEnd_7912804 := by
    simpa [prefixWord, tailWord_7912804, baseEnd_7912804] using wordTrace_append hprefix tailTrace_7912804
  have hstable : (prefixWord ++ tailWord_7912804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912804).length < 2 ^ (prefixWord ++ tailWord_7912804).sum := by decide
  have hdescent : baseEnd_7912804 < baseStart_7912804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912807 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_7912807 : Nat := 118140960795 + 7912807 * 2 ^ 59
def prefixEnd_7912807 : Nat := 4983230072969 + 3 ^ 40 * 7912807 * 2
def baseEnd_7912807 : Nat := 4063073317261327839922169

theorem tailTrace_7912807 : CollatzResearch.WordTrace tailWord_7912807 prefixEnd_7912807 4063073317261327839922169 := by
  unfold tailWord_7912807
  simp only [CollatzResearch.WordTrace]
  refine ⟨288603781044259113690272675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192402520696172742460181783 288603781044259113690272675)
  ·
    refine ⟨432905671566388670535409013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288603781044259113690272675 432905671566388670535409013)
    ·
      refine ⟨40584906709348937862694595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432905671566388670535409013 40584906709348937862694595)
      ·
        refine ⟨60877360064023406794041893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40584906709348937862694595 60877360064023406794041893)
        ·
          refine ⟨11414505012004388773882855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60877360064023406794041893 11414505012004388773882855)
          ·
            refine ⟨17121757518006583160824283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414505012004388773882855 17121757518006583160824283)
            ·
              refine ⟨25682636277009874741236425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121757518006583160824283 25682636277009874741236425)
              ·
                refine ⟨19261977207757406055927319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682636277009874741236425 19261977207757406055927319)
                ·
                  refine ⟨28892965811636109083890979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19261977207757406055927319 28892965811636109083890979)
                  ·
                    refine ⟨43339448717454163625836469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28892965811636109083890979 43339448717454163625836469)
                    ·
                      refine ⟨4063073317261327839922169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43339448717454163625836469 4063073317261327839922169)
                      ·
                        rfl

theorem cell23_7912807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_7912807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912807 prefixEnd_7912807 := by exact prefixLift 7912807
  have htrace : WordTrace (prefixWord ++ tailWord_7912807) baseStart_7912807 baseEnd_7912807 := by
    simpa [prefixWord, tailWord_7912807, baseEnd_7912807] using wordTrace_append hprefix tailTrace_7912807
  have hstable : (prefixWord ++ tailWord_7912807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912807).length < 2 ^ (prefixWord ++ tailWord_7912807).sum := by decide
  have hdescent : baseEnd_7912807 < baseStart_7912807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912837 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_7912837 : Nat := 118140960795 + 7912837 * 2 ^ 59
def prefixEnd_7912837 : Nat := 4983230072969 + 3 ^ 40 * 7912837 * 2
def baseEnd_7912837 : Nat := 4063088721680962722547031

theorem tailTrace_7912837 : CollatzResearch.WordTrace tailWord_7912837 prefixEnd_7912837 4063088721680962722547031 := by
  unfold tailWord_7912837
  simp only [CollatzResearch.WordTrace]
  refine ⟨288604875234150428813864765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192403250156100285875909843 288604875234150428813864765)
  ·
    refine ⟨108226828212806410805199287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288604875234150428813864765 108226828212806410805199287)
    ·
      refine ⟨162340242319209616207798931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108226828212806410805199287 162340242319209616207798931)
      ·
        refine ⟨243510363478814424311698397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162340242319209616207798931 243510363478814424311698397)
        ·
          refine ⟨91316386304555409116886899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243510363478814424311698397 91316386304555409116886899)
          ·
            refine ⟨136974579456833113675330349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91316386304555409116886899 136974579456833113675330349)
            ·
              refine ⟨51365467296312417628248881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136974579456833113675330349 51365467296312417628248881)
              ·
                refine ⟨38524100472234313221186661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51365467296312417628248881 38524100472234313221186661)
                ·
                  refine ⟨7223268838543933728972499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38524100472234313221186661 7223268838543933728972499)
                  ·
                    refine ⟨10834903257815900593458749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223268838543933728972499 10834903257815900593458749)
                    ·
                      refine ⟨4063088721680962722547031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834903257815900593458749 4063088721680962722547031)
                      ·
                        rfl

theorem cell23_7912837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_7912837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912837 prefixEnd_7912837 := by exact prefixLift 7912837
  have htrace : WordTrace (prefixWord ++ tailWord_7912837) baseStart_7912837 baseEnd_7912837 := by
    simpa [prefixWord, tailWord_7912837, baseEnd_7912837] using wordTrace_append hprefix tailTrace_7912837
  have hstable : (prefixWord ++ tailWord_7912837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912837).length < 2 ^ (prefixWord ++ tailWord_7912837).sum := by decide
  have hdescent : baseEnd_7912837 < baseStart_7912837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912880 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_7912880 : Nat := 118140960795 + 7912880 * 2 ^ 59
def prefixEnd_7912880 : Nat := 4983230072969 + 3 ^ 40 * 7912880 * 2
def baseEnd_7912880 : Nat := 4063110801349106054309333

theorem tailTrace_7912880 : CollatzResearch.WordTrace tailWord_7912880 prefixEnd_7912880 4063110801349106054309333 := by
  unfold tailWord_7912880
  simp only [CollatzResearch.WordTrace]
  refine ⟨144303221786497323578840047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192404295715329764771786729 144303221786497323578840047)
  ·
    refine ⟨216454832679745985368260071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144303221786497323578840047 216454832679745985368260071)
    ·
      refine ⟨324682249019618978052390107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216454832679745985368260071 324682249019618978052390107)
      ·
        refine ⟨487023373529428467078585161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324682249019618978052390107 487023373529428467078585161)
        ·
          refine ⟨365267530147071350308938871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487023373529428467078585161 365267530147071350308938871)
          ·
            refine ⟨547901295220607025463408307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365267530147071350308938871 547901295220607025463408307)
            ·
              refine ⟨821851942830910538195112461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547901295220607025463408307 821851942830910538195112461)
              ·
                refine ⟨308194478561591451823167173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 821851942830910538195112461 308194478561591451823167173)
                ·
                  refine ⟨57786464730298397216843845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308194478561591451823167173 57786464730298397216843845)
                  ·
                    refine ⟨10834962136930949478158221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57786464730298397216843845 10834962136930949478158221)
                    ·
                      refine ⟨4063110801349106054309333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834962136930949478158221 4063110801349106054309333)
                      ·
                        rfl

theorem cell23_7912880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_7912880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912880 prefixEnd_7912880 := by exact prefixLift 7912880
  have htrace : WordTrace (prefixWord ++ tailWord_7912880) baseStart_7912880 baseEnd_7912880 := by
    simpa [prefixWord, tailWord_7912880, baseEnd_7912880] using wordTrace_append hprefix tailTrace_7912880
  have hstable : (prefixWord ++ tailWord_7912880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912880).length < 2 ^ (prefixWord ++ tailWord_7912880).sum := by decide
  have hdescent : baseEnd_7912880 < baseStart_7912880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912890 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_7912890 : Nat := 118140960795 + 7912890 * 2 ^ 59
def prefixEnd_7912890 : Nat := 4983230072969 + 3 ^ 40 * 7912890 * 2
def baseEnd_7912890 : Nat := 4063115936155651015184287

theorem tailTrace_7912890 : CollatzResearch.WordTrace tailWord_7912890 prefixEnd_7912890 4063115936155651015184287 := by
  unfold tailWord_7912890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72151702075739604716386031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192404538868638945910362749 72151702075739604716386031)
  ·
    refine ⟨108227553113609407074579047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72151702075739604716386031 108227553113609407074579047)
    ·
      refine ⟨162341329670414110611868571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108227553113609407074579047 162341329670414110611868571)
      ·
        refine ⟨243511994505621165917802857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162341329670414110611868571 243511994505621165917802857)
        ·
          refine ⟨182633995879215874438352143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243511994505621165917802857 182633995879215874438352143)
          ·
            refine ⟨273950993818823811657528215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182633995879215874438352143 273950993818823811657528215)
            ·
              refine ⟨410926490728235717486292323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273950993818823811657528215 410926490728235717486292323)
              ·
                refine ⟨616389736092353576229438485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410926490728235717486292323 616389736092353576229438485)
                ·
                  refine ⟨28893268879329073885754929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 616389736092353576229438485 28893268879329073885754929)
                  ·
                    refine ⟨21669951659496805414316197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28893268879329073885754929 21669951659496805414316197)
                    ·
                      refine ⟨4063115936155651015184287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21669951659496805414316197 4063115936155651015184287)
                      ·
                        rfl

theorem cell23_7912890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_7912890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912890 prefixEnd_7912890 := by exact prefixLift 7912890
  have htrace : WordTrace (prefixWord ++ tailWord_7912890) baseStart_7912890 baseEnd_7912890 := by
    simpa [prefixWord, tailWord_7912890, baseEnd_7912890] using wordTrace_append hprefix tailTrace_7912890
  have hstable : (prefixWord ++ tailWord_7912890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912890).length < 2 ^ (prefixWord ++ tailWord_7912890).sum := by decide
  have hdescent : baseEnd_7912890 < baseStart_7912890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912910 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7912910 : Nat := 118140960795 + 7912910 * 2 ^ 59
def prefixEnd_7912910 : Nat := 4983230072969 + 3 ^ 40 * 7912910 * 2
def baseEnd_7912910 : Nat := 4063126205768740936934195

theorem tailTrace_7912910 : CollatzResearch.WordTrace tailWord_7912910 prefixEnd_7912910 4063126205768740936934195 := by
  unfold tailWord_7912910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36075942220360745285159023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192405025175257308187514789 36075942220360745285159023)
  ·
    refine ⟨54113913330541117927738535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36075942220360745285159023 54113913330541117927738535)
    ·
      refine ⟨81170869995811676891607803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54113913330541117927738535 81170869995811676891607803)
      ·
        refine ⟨121756304993717515337411705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81170869995811676891607803 121756304993717515337411705)
        ·
          refine ⟨91317228745288136503058779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121756304993717515337411705 91317228745288136503058779)
          ·
            refine ⟨136975843117932204754588169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91317228745288136503058779 136975843117932204754588169)
            ·
              refine ⟨102731882338449153565941127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136975843117932204754588169 102731882338449153565941127)
              ·
                refine ⟨154097823507673730348911691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102731882338449153565941127 154097823507673730348911691)
                ·
                  refine ⟨231146735261510595523367537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154097823507673730348911691 231146735261510595523367537)
                  ·
                    refine ⟨173360051446132946642525653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231146735261510595523367537 173360051446132946642525653)
                    ·
                      refine ⟨4063126205768740936934195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173360051446132946642525653 4063126205768740936934195)
                      ·
                        rfl

theorem cell23_7912910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7912910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912910 prefixEnd_7912910 := by exact prefixLift 7912910
  have htrace : WordTrace (prefixWord ++ tailWord_7912910) baseStart_7912910 baseEnd_7912910 := by
    simpa [prefixWord, tailWord_7912910, baseEnd_7912910] using wordTrace_append hprefix tailTrace_7912910
  have hstable : (prefixWord ++ tailWord_7912910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912910).length < 2 ^ (prefixWord ++ tailWord_7912910).sum := by decide
  have hdescent : baseEnd_7912910 < baseStart_7912910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912927 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_7912927 : Nat := 118140960795 + 7912927 * 2 ^ 59
def prefixEnd_7912927 : Nat := 4983230072969 + 3 ^ 40 * 7912927 * 2
def baseEnd_7912927 : Nat := 4063134934939867370421617

theorem tailTrace_7912927 : CollatzResearch.WordTrace tailWord_7912927 prefixEnd_7912927 4063134934939867370421617 := by
  unfold tailWord_7912927
  simp only [CollatzResearch.WordTrace]
  refine ⟨288608157803824374184641035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192405438535882916123094023 288608157803824374184641035)
  ·
    refine ⟨432912236705736561276961553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288608157803824374184641035 432912236705736561276961553)
    ·
      refine ⟨324684177529302420957721165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432912236705736561276961553 324684177529302420957721165)
      ·
        refine ⟨121756566573488407859145437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324684177529302420957721165 121756566573488407859145437)
        ·
          refine ⟨45658712465058152947179539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121756566573488407859145437 45658712465058152947179539)
          ·
            refine ⟨68488068697587229420769309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45658712465058152947179539 68488068697587229420769309)
            ·
              refine ⟨25683025761595211032788491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68488068697587229420769309 25683025761595211032788491)
              ·
                refine ⟨38524538642392816549182737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25683025761595211032788491 38524538642392816549182737)
                ·
                  refine ⟨28893403981794612411887053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38524538642392816549182737 28893403981794612411887053)
                  ·
                    refine ⟨10835026493172979654457645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28893403981794612411887053 10835026493172979654457645)
                    ·
                      refine ⟨4063134934939867370421617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835026493172979654457645 4063134934939867370421617)
                      ·
                        rfl

theorem cell23_7912927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_7912927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912927 prefixEnd_7912927 := by exact prefixLift 7912927
  have htrace : WordTrace (prefixWord ++ tailWord_7912927) baseStart_7912927 baseEnd_7912927 := by
    simpa [prefixWord, tailWord_7912927, baseEnd_7912927] using wordTrace_append hprefix tailTrace_7912927
  have hstable : (prefixWord ++ tailWord_7912927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912927).length < 2 ^ (prefixWord ++ tailWord_7912927).sum := by decide
  have hdescent : baseEnd_7912927 < baseStart_7912927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912940 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_7912940 : Nat := 118140960795 + 7912940 * 2 ^ 59
def prefixEnd_7912940 : Nat := 4983230072969 + 3 ^ 40 * 7912940 * 2
def baseEnd_7912940 : Nat := 4063141610188375819559057

theorem tailTrace_7912940 : CollatzResearch.WordTrace tailWord_7912940 prefixEnd_7912940 4063141610188375819559057 := by
  unfold tailWord_7912940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144304315976388638702432137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192405754635184851603242849 144304315976388638702432137)
  ·
    refine ⟨108228236982291479026824103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144304315976388638702432137 108228236982291479026824103)
    ·
      refine ⟨162342355473437218540236155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108228236982291479026824103 162342355473437218540236155)
      ·
        refine ⟨243513533210155827810354233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162342355473437218540236155 243513533210155827810354233)
        ·
          refine ⟨182635149907616870857765675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243513533210155827810354233 182635149907616870857765675)
          ·
            refine ⟨273952724861425306286648513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182635149907616870857765675 273952724861425306286648513)
            ·
              refine ⟨205464543646068979714986385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273952724861425306286648513 205464543646068979714986385)
              ·
                refine ⟨154098407734551734786239789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205464543646068979714986385 154098407734551734786239789)
                ·
                  refine ⟨57786902900456900544839921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154098407734551734786239789 57786902900456900544839921)
                  ·
                    refine ⟨43340177175342675408629941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57786902900456900544839921 43340177175342675408629941)
                    ·
                      refine ⟨4063141610188375819559057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43340177175342675408629941 4063141610188375819559057)
                      ·
                        rfl

theorem cell23_7912940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_7912940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912940 prefixEnd_7912940 := by exact prefixLift 7912940
  have htrace : WordTrace (prefixWord ++ tailWord_7912940) baseStart_7912940 baseEnd_7912940 := by
    simpa [prefixWord, tailWord_7912940, baseEnd_7912940] using wordTrace_append hprefix tailTrace_7912940
  have hstable : (prefixWord ++ tailWord_7912940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912940).length < 2 ^ (prefixWord ++ tailWord_7912940).sum := by decide
  have hdescent : baseEnd_7912940 < baseStart_7912940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912994 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7912994 : Nat := 118140960795 + 7912994 * 2 ^ 59
def prefixEnd_7912994 : Nat := 4983230072969 + 3 ^ 40 * 7912994 * 2
def baseEnd_7912994 : Nat := 1354389779381239536094603

theorem tailTrace_7912994 : CollatzResearch.WordTrace tailWord_7912994 prefixEnd_7912994 1354389779381239536094603 := by
  unfold tailWord_7912994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72152650373645411156832509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192407067663054429751553357 72152650373645411156832509)
  ·
    refine ⟨27057243890117029183812191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72152650373645411156832509 27057243890117029183812191)
    ·
      refine ⟨40585865835175543775718287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27057243890117029183812191 40585865835175543775718287)
      ·
        refine ⟨60878798752763315663577431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40585865835175543775718287 60878798752763315663577431)
        ·
          refine ⟨91318198129144973495366147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60878798752763315663577431 91318198129144973495366147)
          ·
            refine ⟨136977297193717460243049221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91318198129144973495366147 136977297193717460243049221)
            ·
              refine ⟨25683243223822023795571729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136977297193717460243049221 25683243223822023795571729)
              ·
                refine ⟨19262432417866517846678797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25683243223822023795571729 19262432417866517846678797)
                ·
                  refine ⟨7223412156699944192504549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19262432417866517846678797 7223412156699944192504549)
                  ·
                    refine ⟨1354389779381239536094603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7223412156699944192504549 1354389779381239536094603)
                    ·
                      rfl

theorem cell23_7912994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7912994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912994 prefixEnd_7912994 := by exact prefixLift 7912994
  have htrace : WordTrace (prefixWord ++ tailWord_7912994) baseStart_7912994 baseEnd_7912994 := by
    simpa [prefixWord, tailWord_7912994, baseEnd_7912994] using wordTrace_append hprefix tailTrace_7912994
  have hstable : (prefixWord ++ tailWord_7912994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912994).length < 2 ^ (prefixWord ++ tailWord_7912994).sum := by decide
  have hdescent : baseEnd_7912994 < baseStart_7912994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913011 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 1, 4]
def baseStart_7913011 : Nat := 118140960795 + 7913011 * 2 ^ 59
def prefixEnd_7913011 : Nat := 4983230072969 + 3 ^ 40 * 7913011 * 2
def baseEnd_7913011 : Nat := 1354392689104948347257077

theorem tailTrace_7913011 : CollatzResearch.WordTrace tailWord_7913011 prefixEnd_7913011 1354392689104948347257077 := by
  unfold tailWord_7913011
  simp only [CollatzResearch.WordTrace]
  refine ⟨288611221535520056530698887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192407481023680037687132591 288611221535520056530698887)
  ·
    refine ⟨432916832303280084796048331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288611221535520056530698887 432916832303280084796048331)
    ·
      refine ⟨649375248454920127194072497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432916832303280084796048331 649375248454920127194072497)
      ·
        refine ⟨487031436341190095395554373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649375248454920127194072497 487031436341190095395554373)
        ·
          refine ⟨91318394313973142886666445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487031436341190095395554373 91318394313973142886666445)
          ·
            refine ⟨34244397867739928582499917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91318394313973142886666445 34244397867739928582499917)
            ·
              refine ⟨12841649200402473218437469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34244397867739928582499917 12841649200402473218437469)
              ·
                refine ⟨4815618450150927456914051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12841649200402473218437469 4815618450150927456914051)
                ·
                  refine ⟨7223427675226391185371077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815618450150927456914051 7223427675226391185371077)
                  ·
                    refine ⟨1354392689104948347257077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7223427675226391185371077 1354392689104948347257077)
                    ·
                      rfl

theorem cell23_7913011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 4].length) (baseStart_7913011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913011 prefixEnd_7913011 := by exact prefixLift 7913011
  have htrace : WordTrace (prefixWord ++ tailWord_7913011) baseStart_7913011 baseEnd_7913011 := by
    simpa [prefixWord, tailWord_7913011, baseEnd_7913011] using wordTrace_append hprefix tailTrace_7913011
  have hstable : (prefixWord ++ tailWord_7913011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913011).length < 2 ^ (prefixWord ++ tailWord_7913011).sum := by decide
  have hdescent : baseEnd_7913011 < baseStart_7913011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913021 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7913021 : Nat := 118140960795 + 7913021 * 2 ^ 59
def prefixEnd_7913021 : Nat := 4983230072969 + 3 ^ 40 * 7913021 * 2
def baseEnd_7913021 : Nat := 4063183202121390002646185

theorem tailTrace_7913021 : CollatzResearch.WordTrace tailWord_7913021 prefixEnd_7913021 4063183202121390002646185 := by
  unfold tailWord_7913021
  simp only [CollatzResearch.WordTrace]
  refine ⟨288611586265483828238562917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192407724176989218825708611 288611586265483828238562917)
  ·
    refine ⟨54114672424778217794730547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288611586265483828238562917 54114672424778217794730547)
    ·
      refine ⟨81172008637167326692095821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54114672424778217794730547 81172008637167326692095821)
      ·
        refine ⟨30439503238937747509535933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81172008637167326692095821 30439503238937747509535933)
        ·
          refine ⟨11414813714601655316075975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30439503238937747509535933 11414813714601655316075975)
          ·
            refine ⟨17122220571902482974113963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414813714601655316075975 17122220571902482974113963)
            ·
              refine ⟨25683330857853724461170945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17122220571902482974113963 25683330857853724461170945)
              ·
                refine ⟨19262498143390293345878209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25683330857853724461170945 19262498143390293345878209)
                ·
                  refine ⟨14446873607542720009408657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19262498143390293345878209 14446873607542720009408657)
                  ·
                    refine ⟨10835155205657040007056493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14446873607542720009408657 10835155205657040007056493)
                    ·
                      refine ⟨4063183202121390002646185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835155205657040007056493 4063183202121390002646185)
                      ·
                        rfl

theorem cell23_7913021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7913021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913021 prefixEnd_7913021 := by exact prefixLift 7913021
  have htrace : WordTrace (prefixWord ++ tailWord_7913021) baseStart_7913021 baseEnd_7913021 := by
    simpa [prefixWord, tailWord_7913021, baseEnd_7913021] using wordTrace_append hprefix tailTrace_7913021
  have hstable : (prefixWord ++ tailWord_7913021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913021).length < 2 ^ (prefixWord ++ tailWord_7913021).sum := by decide
  have hdescent : baseEnd_7913021 < baseStart_7913021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913061 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_7913061 : Nat := 118140960795 + 7913061 * 2 ^ 59
def prefixEnd_7913061 : Nat := 4983230072969 + 3 ^ 40 * 7913061 * 2
def baseEnd_7913061 : Nat := 4063203741347569846146001

theorem tailTrace_7913061 : CollatzResearch.WordTrace tailWord_7913061 prefixEnd_7913061 4063203741347569846146001 := by
  unfold tailWord_7913061
  simp only [CollatzResearch.WordTrace]
  refine ⟨288613045185338915070019037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192408696790225943380012691 288613045185338915070019037)
  ·
    refine ⟨108229891944502093151257139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288613045185338915070019037 108229891944502093151257139)
    ·
      refine ⟨162344837916753139726885709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108229891944502093151257139 162344837916753139726885709)
      ·
        refine ⟨60879314218782427397582141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162344837916753139726885709 60879314218782427397582141)
        ·
          refine ⟨22829742832043410274093303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60879314218782427397582141 22829742832043410274093303)
          ·
            refine ⟨34244614248065115411139955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22829742832043410274093303 34244614248065115411139955)
            ·
              refine ⟨51366921372097673116709933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34244614248065115411139955 51366921372097673116709933)
              ·
                refine ⟨19262595514536627418766225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51366921372097673116709933 19262595514536627418766225)
                ·
                  refine ⟨14446946635902470564074669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19262595514536627418766225 14446946635902470564074669)
                  ·
                    refine ⟨5417604988463426461528001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14446946635902470564074669 5417604988463426461528001)
                    ·
                      refine ⟨4063203741347569846146001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417604988463426461528001 4063203741347569846146001)
                      ·
                        rfl

theorem cell23_7913061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_7913061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913061 prefixEnd_7913061 := by exact prefixLift 7913061
  have htrace : WordTrace (prefixWord ++ tailWord_7913061) baseStart_7913061 baseEnd_7913061 := by
    simpa [prefixWord, tailWord_7913061, baseEnd_7913061] using wordTrace_append hprefix tailTrace_7913061
  have hstable : (prefixWord ++ tailWord_7913061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913061).length < 2 ^ (prefixWord ++ tailWord_7913061).sum := by decide
  have hdescent : baseEnd_7913061 < baseStart_7913061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913078 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7913078 : Nat := 118140960795 + 7913078 * 2 ^ 59
def prefixEnd_7913078 : Nat := 4983230072969 + 3 ^ 40 * 7913078 * 2
def baseEnd_7913078 : Nat := 4063212470518696279633423

theorem tailTrace_7913078 : CollatzResearch.WordTrace tailWord_7913078 prefixEnd_7913078 4063212470518696279633423 := by
  unfold tailWord_7913078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038354076642332935836743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192409110150851551315591925 18038354076642332935836743)
  ·
    refine ⟨27057531114963499403755115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18038354076642332935836743 27057531114963499403755115)
    ·
      refine ⟨40586296672445249105632673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27057531114963499403755115 40586296672445249105632673)
      ·
        refine ⟨30439722504333936829224505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40586296672445249105632673 30439722504333936829224505)
        ·
          refine ⟨22829791878250452621918379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30439722504333936829224505 22829791878250452621918379)
          ·
            refine ⟨34244687817375678932877569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22829791878250452621918379 34244687817375678932877569)
            ·
              refine ⟨25683515863031759199658177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34244687817375678932877569 25683515863031759199658177)
              ·
                refine ⟨19262636897273819399743633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25683515863031759199658177 19262636897273819399743633)
                ·
                  refine ⟨14446977672955364549807725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19262636897273819399743633 14446977672955364549807725)
                  ·
                    refine ⟨5417616627358261706177897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14446977672955364549807725 5417616627358261706177897)
                    ·
                      refine ⟨4063212470518696279633423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417616627358261706177897 4063212470518696279633423)
                      ·
                        rfl

theorem cell23_7913078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7913078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913078 prefixEnd_7913078 := by exact prefixLift 7913078
  have htrace : WordTrace (prefixWord ++ tailWord_7913078) baseStart_7913078 baseEnd_7913078 := by
    simpa [prefixWord, tailWord_7913078, baseEnd_7913078] using wordTrace_append hprefix tailTrace_7913078
  have hstable : (prefixWord ++ tailWord_7913078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913078).length < 2 ^ (prefixWord ++ tailWord_7913078).sum := by decide
  have hdescent : baseEnd_7913078 < baseStart_7913078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913085 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_7913085 : Nat := 118140960795 + 7913085 * 2 ^ 59
def prefixEnd_7913085 : Nat := 4983230072969 + 3 ^ 40 * 7913085 * 2
def baseEnd_7913085 : Nat := 4063216064883277752245891

theorem tailTrace_7913085 : CollatzResearch.WordTrace tailWord_7913085 prefixEnd_7913085 4063216064883277752245891 := by
  unfold tailWord_7913085
  simp only [CollatzResearch.WordTrace]
  refine ⟨288613920537251967168892709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192409280358167978112595139 288613920537251967168892709)
  ·
    refine ⟨54115110100734743844167383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288613920537251967168892709 54115110100734743844167383)
    ·
      refine ⟨81172665151102115766251075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54115110100734743844167383 81172665151102115766251075)
      ·
        refine ⟨121758997726653173649376613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81172665151102115766251075 121758997726653173649376613)
        ·
          refine ⟨22829812073747470059258115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121758997726653173649376613 22829812073747470059258115)
          ·
            refine ⟨34244718110621205088887173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22829812073747470059258115 34244718110621205088887173)
            ·
              refine ⟨6420884645741475954166345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34244718110621205088887173 6420884645741475954166345)
              ·
                refine ⟨4815663484306106965624759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6420884645741475954166345 4815663484306106965624759)
                ·
                  refine ⟨7223495226459160448437139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815663484306106965624759 7223495226459160448437139)
                  ·
                    refine ⟨10835242839688740672655709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223495226459160448437139 10835242839688740672655709)
                    ·
                      refine ⟨4063216064883277752245891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835242839688740672655709 4063216064883277752245891)
                      ·
                        rfl

theorem cell23_7913085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_7913085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913085 prefixEnd_7913085 := by exact prefixLift 7913085
  have htrace : WordTrace (prefixWord ++ tailWord_7913085) baseStart_7913085 baseEnd_7913085 := by
    simpa [prefixWord, tailWord_7913085, baseEnd_7913085] using wordTrace_append hprefix tailTrace_7913085
  have hstable : (prefixWord ++ tailWord_7913085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913085).length < 2 ^ (prefixWord ++ tailWord_7913085).sum := by decide
  have hdescent : baseEnd_7913085 < baseStart_7913085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913091 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 3, 2, 2]
def baseStart_7913091 : Nat := 118140960795 + 7913091 * 2 ^ 59
def prefixEnd_7913091 : Nat := 4983230072969 + 3 ^ 40 * 7913091 * 2
def baseEnd_7913091 : Nat := 4063219145767204728770863

theorem tailTrace_7913091 : CollatzResearch.WordTrace tailWord_7913091 prefixEnd_7913091 4063219145767204728770863 := by
  unfold tailWord_7913091
  simp only [CollatzResearch.WordTrace]
  refine ⟨288614139375230230193611127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192409426250153486795740751 288614139375230230193611127)
  ·
    refine ⟨432921209062845345290416691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288614139375230230193611127 432921209062845345290416691)
    ·
      refine ⟨649381813594268017935625037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432921209062845345290416691 649381813594268017935625037)
      ·
        refine ⟨243518180097850506725859389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649381813594268017935625037 243518180097850506725859389)
        ·
          refine ⟨91319317536693940022197271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243518180097850506725859389 91319317536693940022197271)
          ·
            refine ⟨136978976305040910033295907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91319317536693940022197271 136978976305040910033295907)
            ·
              refine ⟨205468464457561365049943861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136978976305040910033295907 205468464457561365049943861)
              ·
                refine ⟨19262668542896377973432237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205468464457561365049943861 19262668542896377973432237)
                ·
                  refine ⟨7223500703586141740037089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19262668542896377973432237 7223500703586141740037089)
                  ·
                    refine ⟨5417625527689606305027817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223500703586141740037089 5417625527689606305027817)
                    ·
                      refine ⟨4063219145767204728770863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417625527689606305027817 4063219145767204728770863)
                      ·
                        rfl

theorem cell23_7913091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_7913091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913091 prefixEnd_7913091 := by exact prefixLift 7913091
  have htrace : WordTrace (prefixWord ++ tailWord_7913091) baseStart_7913091 baseEnd_7913091 := by
    simpa [prefixWord, tailWord_7913091, baseEnd_7913091] using wordTrace_append hprefix tailTrace_7913091
  have hstable : (prefixWord ++ tailWord_7913091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913091).length < 2 ^ (prefixWord ++ tailWord_7913091).sum := by decide
  have hdescent : baseEnd_7913091 < baseStart_7913091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913097 : List Nat := [1, 2, 1, 1, 4, 1, 5, 8]
def baseStart_7913097 : Nat := 118140960795 + 7913097 * 2 ^ 59
def prefixEnd_7913097 : Nat := 4983230072969 + 3 ^ 40 * 7913097 * 2
def baseEnd_7913097 : Nat := 150489712098190063159105

theorem tailTrace_7913097 : CollatzResearch.WordTrace tailWord_7913097 prefixEnd_7913097 150489712098190063159105 := by
  unfold tailWord_7913097
  simp only [CollatzResearch.WordTrace]
  refine ⟨288614358213208493218329545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192409572142138995478886363 288614358213208493218329545)
  ·
    refine ⟨216460768659906369913747159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288614358213208493218329545 216460768659906369913747159)
    ·
      refine ⟨324691152989859554870620739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216460768659906369913747159 324691152989859554870620739)
      ·
        refine ⟨487036729484789332305931109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324691152989859554870620739 487036729484789332305931109)
        ·
          refine ⟨91319386778397999807362083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487036729484789332305931109 91319386778397999807362083)
          ·
            refine ⟨136979080167596999711043125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91319386778397999807362083 136979080167596999711043125)
            ·
              refine ⟨12841788765712218722910293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136979080167596999711043125 12841788765712218722910293)
              ·
                refine ⟨150489712098190063159105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12841788765712218722910293 150489712098190063159105)
                ·
                  rfl

theorem cell23_7913097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 8].length) (baseStart_7913097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913097 prefixEnd_7913097 := by exact prefixLift 7913097
  have htrace : WordTrace (prefixWord ++ tailWord_7913097) baseStart_7913097 baseEnd_7913097 := by
    simpa [prefixWord, tailWord_7913097, baseEnd_7913097] using wordTrace_append hprefix tailTrace_7913097
  have hstable : (prefixWord ++ tailWord_7913097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913097).length < 2 ^ (prefixWord ++ tailWord_7913097).sum := by decide
  have hdescent : baseEnd_7913097 < baseStart_7913097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913122 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7913122 : Nat := 118140960795 + 7913122 * 2 ^ 59
def prefixEnd_7913122 : Nat := 4983230072969 + 3 ^ 40 * 7913122 * 2
def baseEnd_7913122 : Nat := 1354411687889164702494407

theorem tailTrace_7913122 : CollatzResearch.WordTrace tailWord_7913122 prefixEnd_7913122 1354411687889164702494407 := by
  unfold tailWord_7913122
  simp only [CollatzResearch.WordTrace]
  refine ⟨72153817509529480621997405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192410180025411948325326413 72153817509529480621997405)
  ·
    refine ⟨27057681566073555233249027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72153817509529480621997405 27057681566073555233249027)
    ·
      refine ⟨40586522349110332849873541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27057681566073555233249027 40586522349110332849873541)
      ·
        refine ⟨7609972940458187409351289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40586522349110332849873541 7609972940458187409351289)
        ·
          refine ⟨5707479705343640557013467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7609972940458187409351289 5707479705343640557013467)
          ·
            refine ⟨8561219558015460835520201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707479705343640557013467 8561219558015460835520201)
            ·
              refine ⟨6420914668511595626640151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8561219558015460835520201 6420914668511595626640151)
              ·
                refine ⟨9631372002767393439960227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420914668511595626640151 9631372002767393439960227)
                ·
                  refine ⟨14447058004151090159940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9631372002767393439960227 14447058004151090159940341)
                  ·
                    refine ⟨1354411687889164702494407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14447058004151090159940341 1354411687889164702494407)
                    ·
                      rfl

theorem cell23_7913122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7913122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913122 prefixEnd_7913122 := by exact prefixLift 7913122
  have htrace : WordTrace (prefixWord ++ tailWord_7913122) baseStart_7913122 baseEnd_7913122 := by
    simpa [prefixWord, tailWord_7913122, baseEnd_7913122] using wordTrace_append hprefix tailTrace_7913122
  have hstable : (prefixWord ++ tailWord_7913122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913122).length < 2 ^ (prefixWord ++ tailWord_7913122).sum := by decide
  have hdescent : baseEnd_7913122 < baseStart_7913122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913142 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7913142 : Nat := 118140960795 + 7913142 * 2 ^ 59
def prefixEnd_7913142 : Nat := 4983230072969 + 3 ^ 40 * 7913142 * 2
def baseEnd_7913142 : Nat := 4063245333280584029233129

theorem tailTrace_7913142 : CollatzResearch.WordTrace tailWord_7913142 prefixEnd_7913142 4063245333280584029233129 := by
  unfold tailWord_7913142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038499968627841618982355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192410666332030310602478453 18038499968627841618982355)
  ·
    refine ⟨27057749952941762428473533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18038499968627841618982355 27057749952941762428473533)
    ·
      refine ⟨10146656232353160910677575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27057749952941762428473533 10146656232353160910677575)
      ·
        refine ⟨15219984348529741366016363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146656232353160910677575 15219984348529741366016363)
        ·
          refine ⟨22829976522794612049024545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219984348529741366016363 22829976522794612049024545)
          ·
            refine ⟨17122482392095959036768409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22829976522794612049024545 17122482392095959036768409)
            ·
              refine ⟨12841861794071969277576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17122482392095959036768409 12841861794071969277576307)
              ·
                refine ⟨19262792691107953916364461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12841861794071969277576307 19262792691107953916364461)
                ·
                  refine ⟨7223547259165482718636673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19262792691107953916364461 7223547259165482718636673)
                  ·
                    refine ⟨5417660444374112038977505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223547259165482718636673 5417660444374112038977505)
                    ·
                      refine ⟨4063245333280584029233129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417660444374112038977505 4063245333280584029233129)
                      ·
                        rfl

theorem cell23_7913142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7913142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913142 prefixEnd_7913142 := by exact prefixLift 7913142
  have htrace : WordTrace (prefixWord ++ tailWord_7913142) baseStart_7913142 baseEnd_7913142 := by
    simpa [prefixWord, tailWord_7913142, baseEnd_7913142] using wordTrace_append hprefix tailTrace_7913142
  have hstable : (prefixWord ++ tailWord_7913142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913142).length < 2 ^ (prefixWord ++ tailWord_7913142).sum := by decide
  have hdescent : baseEnd_7913142 < baseStart_7913142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913147 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_7913147 : Nat := 118140960795 + 7913147 * 2 ^ 59
def prefixEnd_7913147 : Nat := 4983230072969 + 3 ^ 40 * 7913147 * 2
def baseEnd_7913147 : Nat := 4063247900683856509670605

theorem tailTrace_7913147 : CollatzResearch.WordTrace tailWord_7913147 prefixEnd_7913147 4063247900683856509670605 := by
  unfold tailWord_7913147
  simp only [CollatzResearch.WordTrace]
  refine ⟨288616181863027351757649695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192410787908684901171766463 288616181863027351757649695)
  ·
    refine ⟨432924272794541027636474543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288616181863027351757649695 432924272794541027636474543)
    ·
      refine ⟨649386409191811541454711815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432924272794541027636474543 649386409191811541454711815)
      ·
        refine ⟨974079613787717312182067723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649386409191811541454711815 974079613787717312182067723)
        ·
          refine ⟨1461119420681575968273101585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974079613787717312182067723 1461119420681575968273101585)
          ·
            refine ⟨1095839565511181976204826189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461119420681575968273101585 1095839565511181976204826189)
            ·
              refine ⟨410939837066693241076809821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095839565511181976204826189 410939837066693241076809821)
              ·
                refine ⟨154102438900009965403803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410939837066693241076809821 154102438900009965403803683)
                ·
                  refine ⟨231153658350014948105705525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154102438900009965403803683 231153658350014948105705525)
                  ·
                    refine ⟨21670655470313901384909893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231153658350014948105705525 21670655470313901384909893)
                    ·
                      refine ⟨4063247900683856509670605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21670655470313901384909893 4063247900683856509670605)
                      ·
                        rfl

theorem cell23_7913147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_7913147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913147 prefixEnd_7913147 := by exact prefixLift 7913147
  have htrace : WordTrace (prefixWord ++ tailWord_7913147) baseStart_7913147 baseEnd_7913147 := by
    simpa [prefixWord, tailWord_7913147, baseEnd_7913147] using wordTrace_append hprefix tailTrace_7913147
  have hstable : (prefixWord ++ tailWord_7913147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913147).length < 2 ^ (prefixWord ++ tailWord_7913147).sum := by decide
  have hdescent : baseEnd_7913147 < baseStart_7913147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913167 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_7913167 : Nat := 118140960795 + 7913167 * 2 ^ 59
def prefixEnd_7913167 : Nat := 4983230072969 + 3 ^ 40 * 7913167 * 2
def baseEnd_7913167 : Nat := 4063258170296946431420513

theorem tailTrace_7913167 : CollatzResearch.WordTrace tailWord_7913167 prefixEnd_7913167 4063258170296946431420513 := by
  unfold tailWord_7913167
  simp only [CollatzResearch.WordTrace]
  refine ⟨288616911322954895173377755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192411274215303263448918503 288616911322954895173377755)
  ·
    refine ⟨432925366984432342760066633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288616911322954895173377755 432925366984432342760066633)
    ·
      refine ⟨324694025238324257070049975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432925366984432342760066633 324694025238324257070049975)
      ·
        refine ⟨487041037857486385605074963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324694025238324257070049975 487041037857486385605074963)
        ·
          refine ⟨730561556786229578407612445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487041037857486385605074963 730561556786229578407612445)
          ·
            refine ⟨273960583794836091902854667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730561556786229578407612445 273960583794836091902854667)
            ·
              refine ⟨410940875692254137854282001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273960583794836091902854667 410940875692254137854282001)
              ·
                refine ⟨308205656769190603390711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410940875692254137854282001 308205656769190603390711501)
                ·
                  refine ⟨115577121288446476271516813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308205656769190603390711501 115577121288446476271516813)
                  ·
                    refine ⟨43341420483167428601818805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115577121288446476271516813 43341420483167428601818805)
                    ·
                      refine ⟨4063258170296946431420513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43341420483167428601818805 4063258170296946431420513)
                      ·
                        rfl

theorem cell23_7913167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_7913167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913167 prefixEnd_7913167 := by exact prefixLift 7913167
  have htrace : WordTrace (prefixWord ++ tailWord_7913167) baseStart_7913167 baseEnd_7913167 := by
    simpa [prefixWord, tailWord_7913167, baseEnd_7913167] using wordTrace_append hprefix tailTrace_7913167
  have hstable : (prefixWord ++ tailWord_7913167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913167).length < 2 ^ (prefixWord ++ tailWord_7913167).sum := by decide
  have hdescent : baseEnd_7913167 < baseStart_7913167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913194 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_7913194 : Nat := 118140960795 + 7913194 * 2 ^ 59
def prefixEnd_7913194 : Nat := 4983230072969 + 3 ^ 40 * 7913194 * 2
def baseEnd_7913194 : Nat := 4063272034274617825782889

theorem tailTrace_7913194 : CollatzResearch.WordTrace tailWord_7913194 prefixEnd_7913194 4063272034274617825782889 := by
  unfold tailWord_7913194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72154474023464269696152659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192411930729238052523073757 72154474023464269696152659)
  ·
    refine ⟨108231711035196404544228989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72154474023464269696152659 108231711035196404544228989)
    ·
      refine ⟨40586891638198651704085871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108231711035196404544228989 40586891638198651704085871)
      ·
        refine ⟨60880337457297977556128807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40586891638198651704085871 60880337457297977556128807)
        ·
          refine ⟨91320506185946966334193211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60880337457297977556128807 91320506185946966334193211)
          ·
            refine ⟨136980759278920449501289817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91320506185946966334193211 136980759278920449501289817)
            ·
              refine ⟨102735569459190337125967363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136980759278920449501289817 102735569459190337125967363)
              ·
                refine ⟨154103354188785505688951045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102735569459190337125967363 154103354188785505688951045)
                ·
                  refine ⟨28894378910397282316678321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154103354188785505688951045 28894378910397282316678321)
                  ·
                    refine ⟨21670784182797961737508741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28894378910397282316678321 21670784182797961737508741)
                    ·
                      refine ⟨4063272034274617825782889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21670784182797961737508741 4063272034274617825782889)
                      ·
                        rfl

theorem cell23_7913194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_7913194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913194 prefixEnd_7913194 := by exact prefixLift 7913194
  have htrace : WordTrace (prefixWord ++ tailWord_7913194) baseStart_7913194 baseEnd_7913194 := by
    simpa [prefixWord, tailWord_7913194, baseEnd_7913194] using wordTrace_append hprefix tailTrace_7913194
  have hstable : (prefixWord ++ tailWord_7913194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913194).length < 2 ^ (prefixWord ++ tailWord_7913194).sum := by decide
  have hdescent : baseEnd_7913194 < baseStart_7913194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913198 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_7913198 : Nat := 118140960795 + 7913198 * 2 ^ 59
def prefixEnd_7913198 : Nat := 4983230072969 + 3 ^ 40 * 7913198 * 2
def baseEnd_7913198 : Nat := 4063274088197235810132871

theorem tailTrace_7913198 : CollatzResearch.WordTrace tailWord_7913198 prefixEnd_7913198 4063274088197235810132871 := by
  unfold tailWord_7913198
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077255248230323433469531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192412027990561724978504165 36077255248230323433469531)
  ·
    refine ⟨54115882872345485150204297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077255248230323433469531 54115882872345485150204297)
    ·
      refine ⟨40586912154259113862653223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54115882872345485150204297 40586912154259113862653223)
      ·
        refine ⟨60880368231388670793979835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40586912154259113862653223 60880368231388670793979835)
        ·
          refine ⟨91320552347083006190969753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60880368231388670793979835 91320552347083006190969753)
          ·
            refine ⟨68490414260312254643227315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91320552347083006190969753 68490414260312254643227315)
            ·
              refine ⟨102735621390468381964840973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68490414260312254643227315 102735621390468381964840973)
              ·
                refine ⟨38525858021425643236815365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102735621390468381964840973 38525858021425643236815365)
                ·
                  refine ⟨7223598379017308106902881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38525858021425643236815365 7223598379017308106902881)
                  ·
                    refine ⟨5417698784262981080177161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223598379017308106902881 5417698784262981080177161)
                    ·
                      refine ⟨4063274088197235810132871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417698784262981080177161 4063274088197235810132871)
                      ·
                        rfl

theorem cell23_7913198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_7913198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913198 prefixEnd_7913198 := by exact prefixLift 7913198
  have htrace : WordTrace (prefixWord ++ tailWord_7913198) baseStart_7913198 baseEnd_7913198 := by
    simpa [prefixWord, tailWord_7913198, baseEnd_7913198] using wordTrace_append hprefix tailTrace_7913198
  have hstable : (prefixWord ++ tailWord_7913198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913198).length < 2 ^ (prefixWord ++ tailWord_7913198).sum := by decide
  have hdescent : baseEnd_7913198 < baseStart_7913198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913215 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 2, 2, 2]
def baseStart_7913215 : Nat := 118140960795 + 7913215 * 2 ^ 59
def prefixEnd_7913215 : Nat := 4983230072969 + 3 ^ 40 * 7913215 * 2
def baseEnd_7913215 : Nat := 4063282817368362243620293

theorem tailTrace_7913215 : CollatzResearch.WordTrace tailWord_7913215 prefixEnd_7913215 4063282817368362243620293 := by
  unfold tailWord_7913215
  simp only [CollatzResearch.WordTrace]
  refine ⟨288618662026780999371125099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192412441351187332914083399 288618662026780999371125099)
  ·
    refine ⟨432927993040171499056687649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288618662026780999371125099 432927993040171499056687649)
    ·
      refine ⟨324695994780128624292515737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432927993040171499056687649 324695994780128624292515737)
      ·
        refine ⟨243521996085096468219386803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324695994780128624292515737 243521996085096468219386803)
        ·
          refine ⟨365282994127644702329080205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243521996085096468219386803 365282994127644702329080205)
          ·
            refine ⟨136981122797866763373405077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365282994127644702329080205 136981122797866763373405077)
            ·
              refine ⟨6420990131150004533128363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136981122797866763373405077 6420990131150004533128363)
              ·
                refine ⟨9631485196725006799692545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420990131150004533128363 9631485196725006799692545)
                ·
                  refine ⟨7223613897543755099769409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9631485196725006799692545 7223613897543755099769409)
                  ·
                    refine ⟨5417710423157816324827057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223613897543755099769409 5417710423157816324827057)
                    ·
                      refine ⟨4063282817368362243620293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417710423157816324827057 4063282817368362243620293)
                      ·
                        rfl

theorem cell23_7913215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_7913215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913215 prefixEnd_7913215 := by exact prefixLift 7913215
  have htrace : WordTrace (prefixWord ++ tailWord_7913215) baseStart_7913215 baseEnd_7913215 := by
    simpa [prefixWord, tailWord_7913215, baseEnd_7913215] using wordTrace_append hprefix tailTrace_7913215
  have hstable : (prefixWord ++ tailWord_7913215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913215).length < 2 ^ (prefixWord ++ tailWord_7913215).sum := by decide
  have hdescent : baseEnd_7913215 < baseStart_7913215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913236 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7913236 : Nat := 118140960795 + 7913236 * 2 ^ 59
def prefixEnd_7913236 : Nat := 4983230072969 + 3 ^ 40 * 7913236 * 2
def baseEnd_7913236 : Nat := 4063293600462106661457697

theorem tailTrace_7913236 : CollatzResearch.WordTrace tailWord_7913236 prefixEnd_7913236 4063293600462106661457697 := by
  unfold tailWord_7913236
  simp only [CollatzResearch.WordTrace]
  refine ⟨144309713979852459978819781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192412951973136613305093041 144309713979852459978819781)
  ·
    refine ⟨27058071371222336246028709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144309713979852459978819781 27058071371222336246028709)
    ·
      refine ⟨5073388382104188046130383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27058071371222336246028709 5073388382104188046130383)
      ·
        refine ⟨7610082573156282069195575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073388382104188046130383 7610082573156282069195575)
        ·
          refine ⟨11415123859734423103793363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610082573156282069195575 11415123859734423103793363)
          ·
            refine ⟨17122685789601634655690045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415123859734423103793363 17122685789601634655690045)
            ·
              refine ⟨6421007171100612995883767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17122685789601634655690045 6421007171100612995883767)
              ·
                refine ⟨9631510756650919493825651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421007171100612995883767 9631510756650919493825651)
                ·
                  refine ⟨14447266134976379240738477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9631510756650919493825651 14447266134976379240738477)
                  ·
                    refine ⟨5417724800616142215276929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14447266134976379240738477 5417724800616142215276929)
                    ·
                      refine ⟨4063293600462106661457697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417724800616142215276929 4063293600462106661457697)
                      ·
                        rfl

theorem cell23_7913236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7913236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913236 prefixEnd_7913236 := by exact prefixLift 7913236
  have htrace : WordTrace (prefixWord ++ tailWord_7913236) baseStart_7913236 baseEnd_7913236 := by
    simpa [prefixWord, tailWord_7913236, baseEnd_7913236] using wordTrace_append hprefix tailTrace_7913236
  have hstable : (prefixWord ++ tailWord_7913236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913236).length < 2 ^ (prefixWord ++ tailWord_7913236).sum := by decide
  have hdescent : baseEnd_7913236 < baseStart_7913236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913244 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7913244 : Nat := 118140960795 + 7913244 * 2 ^ 59
def prefixEnd_7913244 : Nat := 4983230072969 + 3 ^ 40 * 7913244 * 2
def baseEnd_7913244 : Nat := 4063297708307342630157659

theorem tailTrace_7913244 : CollatzResearch.WordTrace tailWord_7913244 prefixEnd_7913244 4063297708307342630157659 := by
  unfold tailWord_7913244
  simp only [CollatzResearch.WordTrace]
  refine ⟨144309859871837968661965393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192413146495783958215953857 144309859871837968661965393)
  ·
    refine ⟨108232394903878476496474045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144309859871837968661965393 108232394903878476496474045)
    ·
      refine ⟨40587148088954428686177767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108232394903878476496474045 40587148088954428686177767)
      ·
        refine ⟨60880722133431643029266651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40587148088954428686177767 60880722133431643029266651)
        ·
          refine ⟨91321083200147464543899977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60880722133431643029266651 91321083200147464543899977)
          ·
            refine ⟨68490812400110598407924983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91321083200147464543899977 68490812400110598407924983)
            ·
              refine ⟨102736218600165897611887475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68490812400110598407924983 102736218600165897611887475)
              ·
                refine ⟨154104327900248846417831213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102736218600165897611887475 154104327900248846417831213)
                ·
                  refine ⟨57789122962593317406686705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154104327900248846417831213 57789122962593317406686705)
                  ·
                    refine ⟨43341842221944988055015029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57789122962593317406686705 43341842221944988055015029)
                    ·
                      refine ⟨4063297708307342630157659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43341842221944988055015029 4063297708307342630157659)
                      ·
                        rfl

theorem cell23_7913244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7913244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913244 prefixEnd_7913244 := by exact prefixLift 7913244
  have htrace : WordTrace (prefixWord ++ tailWord_7913244) baseStart_7913244 baseEnd_7913244 := by
    simpa [prefixWord, tailWord_7913244, baseEnd_7913244] using wordTrace_append hprefix tailTrace_7913244
  have hstable : (prefixWord ++ tailWord_7913244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913244).length < 2 ^ (prefixWord ++ tailWord_7913244).sum := by decide
  have hdescent : baseEnd_7913244 < baseStart_7913244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913288 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_7913288 : Nat := 118140960795 + 7913288 * 2 ^ 59
def prefixEnd_7913288 : Nat := 4983230072969 + 3 ^ 40 * 7913288 * 2
def baseEnd_7913288 : Nat := 4063320301456140458007457

theorem tailTrace_7913288 : CollatzResearch.WordTrace tailWord_7913288 prefixEnd_7913288 4063320301456140458007457 := by
  unfold tailWord_7913288
  simp only [CollatzResearch.WordTrace]
  refine ⟨144310662277758266419266259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192414216370344355225688345 144310662277758266419266259)
  ·
    refine ⟨216465993416637399628899389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144310662277758266419266259 216465993416637399628899389)
    ·
      refine ⟨81174747531239024860837271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216465993416637399628899389 81174747531239024860837271)
      ·
        refine ⟨121762121296858537291255907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81174747531239024860837271 121762121296858537291255907)
        ·
          refine ⟨182643181945287805936883861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121762121296858537291255907 182643181945287805936883861)
          ·
            refine ⟨8561399153685365903291431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182643181945287805936883861 8561399153685365903291431)
            ·
              refine ⟨12842098730528048854937147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561399153685365903291431 12842098730528048854937147)
              ·
                refine ⟨19263148095792073282405721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842098730528048854937147 19263148095792073282405721)
                ·
                  refine ⟨14447361071844054961804291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19263148095792073282405721 14447361071844054961804291)
                  ·
                    refine ⟨21671041607766082442706437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14447361071844054961804291 21671041607766082442706437)
                    ·
                      refine ⟨4063320301456140458007457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21671041607766082442706437 4063320301456140458007457)
                      ·
                        rfl

theorem cell23_7913288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_7913288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913288 prefixEnd_7913288 := by exact prefixLift 7913288
  have htrace : WordTrace (prefixWord ++ tailWord_7913288) baseStart_7913288 baseEnd_7913288 := by
    simpa [prefixWord, tailWord_7913288, baseEnd_7913288] using wordTrace_append hprefix tailTrace_7913288
  have hstable : (prefixWord ++ tailWord_7913288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913288).length < 2 ^ (prefixWord ++ tailWord_7913288).sum := by decide
  have hdescent : baseEnd_7913288 < baseStart_7913288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913311 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 6]
def baseStart_7913311 : Nat := 118140960795 + 7913311 * 2 ^ 59
def prefixEnd_7913311 : Nat := 4983230072969 + 3 ^ 40 * 7913311 * 2
def baseEnd_7913311 : Nat := 451481345723465985335539

theorem tailTrace_7913311 : CollatzResearch.WordTrace tailWord_7913311 prefixEnd_7913311 451481345723465985335539 := by
  unfold tailWord_7913311
  simp only [CollatzResearch.WordTrace]
  refine ⟨288622163434433207766619787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192414775622955471844413191 288622163434433207766619787)
  ·
    refine ⟨432933245151649811649929681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288622163434433207766619787 432933245151649811649929681)
    ·
      refine ⟨324699933863737358737447261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432933245151649811649929681 324699933863737358737447261)
      ·
        refine ⟨121762475198901509526542723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324699933863737358737447261 121762475198901509526542723)
        ·
          refine ⟨182643712798352264289814085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121762475198901509526542723 182643712798352264289814085)
          ·
            refine ⟨34245696149691049554340141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182643712798352264289814085 34245696149691049554340141)
            ·
              refine ⟨12842136056134143582877553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34245696149691049554340141 12842136056134143582877553)
              ·
                refine ⟨9631602042100607687158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842136056134143582877553 9631602042100607687158165)
                ·
                  refine ⟨451481345723465985335539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9631602042100607687158165 451481345723465985335539)
                  ·
                    rfl

theorem cell23_7913311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 6].length) (baseStart_7913311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913311 prefixEnd_7913311 := by exact prefixLift 7913311
  have htrace : WordTrace (prefixWord ++ tailWord_7913311) baseStart_7913311 baseEnd_7913311 := by
    simpa [prefixWord, tailWord_7913311, baseEnd_7913311] using wordTrace_append hprefix tailTrace_7913311
  have hstable : (prefixWord ++ tailWord_7913311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913311).length < 2 ^ (prefixWord ++ tailWord_7913311).sum := by decide
  have hdescent : baseEnd_7913311 < baseStart_7913311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913338 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_7913338 : Nat := 118140960795 + 7913338 * 2 ^ 59
def prefixEnd_7913338 : Nat := 4983230072969 + 3 ^ 40 * 7913338 * 2
def baseEnd_7913338 : Nat := 4063345975488865262382227

theorem tailTrace_7913338 : CollatzResearch.WordTrace tailWord_7913338 prefixEnd_7913338 4063345975488865262382227 := by
  unfold tailWord_7913338
  simp only [CollatzResearch.WordTrace]
  refine ⟨72155787051333847844463167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192415432136890260918568445 72155787051333847844463167)
  ·
    refine ⟨108233680577000771766694751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72155787051333847844463167 108233680577000771766694751)
    ·
      refine ⟨162350520865501157650042127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108233680577000771766694751 162350520865501157650042127)
      ·
        refine ⟨243525781298251736475063191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162350520865501157650042127 243525781298251736475063191)
        ·
          refine ⟨365288671947377604712594787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243525781298251736475063191 365288671947377604712594787)
          ·
            refine ⟨547933007921066407068892181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365288671947377604712594787 547933007921066407068892181)
            ·
              refine ⟨25684359746299987831354321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 547933007921066407068892181 25684359746299987831354321)
              ·
                refine ⟨19263269809724990873515741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25684359746299987831354321 19263269809724990873515741)
                ·
                  refine ⟨7223726178646871577568403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19263269809724990873515741 7223726178646871577568403)
                  ·
                    refine ⟨10835589267970307366352605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223726178646871577568403 10835589267970307366352605)
                    ·
                      refine ⟨4063345975488865262382227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835589267970307366352605 4063345975488865262382227)
                      ·
                        rfl

theorem cell23_7913338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_7913338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913338 prefixEnd_7913338 := by exact prefixLift 7913338
  have htrace : WordTrace (prefixWord ++ tailWord_7913338) baseStart_7913338 baseEnd_7913338 := by
    simpa [prefixWord, tailWord_7913338, baseEnd_7913338] using wordTrace_append hprefix tailTrace_7913338
  have hstable : (prefixWord ++ tailWord_7913338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913338).length < 2 ^ (prefixWord ++ tailWord_7913338).sum := by decide
  have hdescent : baseEnd_7913338 < baseStart_7913338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913348 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7913348 : Nat := 118140960795 + 7913348 * 2 ^ 59
def prefixEnd_7913348 : Nat := 4983230072969 + 3 ^ 40 * 7913348 * 2
def baseEnd_7913348 : Nat := 4063351110295410223257181

theorem tailTrace_7913348 : CollatzResearch.WordTrace tailWord_7913348 prefixEnd_7913348 4063351110295410223257181 := by
  unfold tailWord_7913348
  simp only [CollatzResearch.WordTrace]
  refine ⟨144311756467649581542858349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192415675290199442057144465 144311756467649581542858349)
  ·
    refine ⟨54116908675368593078571881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144311756467649581542858349 54116908675368593078571881)
    ·
      refine ⟨40587681506526444808928911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54116908675368593078571881 40587681506526444808928911)
      ·
        refine ⟨60881522259789667213393367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40587681506526444808928911 60881522259789667213393367)
        ·
          refine ⟨91322283389684500820090051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60881522259789667213393367 91322283389684500820090051)
          ·
            refine ⟨136983425084526751230135077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91322283389684500820090051 136983425084526751230135077)
            ·
              refine ⟨25684392203348765855650327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136983425084526751230135077 25684392203348765855650327)
              ·
                refine ⟨38526588305023148783475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25684392203348765855650327 38526588305023148783475491)
                ·
                  refine ⟨57789882457534723175213237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38526588305023148783475491 57789882457534723175213237)
                  ·
                    refine ⟨5417801480393880297676241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57789882457534723175213237 5417801480393880297676241)
                    ·
                      refine ⟨4063351110295410223257181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417801480393880297676241 4063351110295410223257181)
                      ·
                        rfl

theorem cell23_7913348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7913348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913348 prefixEnd_7913348 := by exact prefixLift 7913348
  have htrace : WordTrace (prefixWord ++ tailWord_7913348) baseStart_7913348 baseEnd_7913348 := by
    simpa [prefixWord, tailWord_7913348, baseEnd_7913348] using wordTrace_append hprefix tailTrace_7913348
  have hstable : (prefixWord ++ tailWord_7913348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913348).length < 2 ^ (prefixWord ++ tailWord_7913348).sum := by decide
  have hdescent : baseEnd_7913348 < baseStart_7913348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913366 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7913366 : Nat := 118140960795 + 7913366 * 2 ^ 59
def prefixEnd_7913366 : Nat := 4983230072969 + 3 ^ 40 * 7913366 * 2
def baseEnd_7913366 : Nat := 1354453450982397050944033

theorem tailTrace_7913366 : CollatzResearch.WordTrace tailWord_7913366 prefixEnd_7913366 1354453450982397050944033 := by
  unfold tailWord_7913366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039010590577122009991997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192416112966155968106581301 18039010590577122009991997)
  ·
    refine ⟨6764628971466420753746999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18039010590577122009991997 6764628971466420753746999)
    ·
      refine ⟨10146943457199631130620499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764628971466420753746999 10146943457199631130620499)
      ·
        refine ⟨15220415185799446695930749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146943457199631130620499 15220415185799446695930749)
        ·
          refine ⟨5707655694674792510974031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15220415185799446695930749 5707655694674792510974031)
          ·
            refine ⟨8561483542012188766461047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707655694674792510974031 8561483542012188766461047)
            ·
              refine ⟨12842225313018283149691571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561483542012188766461047 12842225313018283149691571)
              ·
                refine ⟨19263337969527424724537357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842225313018283149691571 19263337969527424724537357)
                ·
                  refine ⟨7223751738572784271701509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19263337969527424724537357 7223751738572784271701509)
                  ·
                    refine ⟨1354453450982397050944033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7223751738572784271701509 1354453450982397050944033)
                    ·
                      rfl

theorem cell23_7913366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7913366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913366 prefixEnd_7913366 := by exact prefixLift 7913366
  have htrace : WordTrace (prefixWord ++ tailWord_7913366) baseStart_7913366 baseEnd_7913366 := by
    simpa [prefixWord, tailWord_7913366, baseEnd_7913366] using wordTrace_append hprefix tailTrace_7913366
  have hstable : (prefixWord ++ tailWord_7913366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913366).length < 2 ^ (prefixWord ++ tailWord_7913366).sum := by decide
  have hdescent : baseEnd_7913366 < baseStart_7913366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913372 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7913372 : Nat := 118140960795 + 7913372 * 2 ^ 59
def prefixEnd_7913372 : Nat := 4983230072969 + 3 ^ 40 * 7913372 * 2
def baseEnd_7913372 : Nat := 4063363433831118129357071

theorem tailTrace_7913372 : CollatzResearch.WordTrace tailWord_7913372 prefixEnd_7913372 4063363433831118129357071 := by
  unfold tailWord_7913372
  simp only [CollatzResearch.WordTrace]
  refine ⟨144312194143606107592295185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192416258858141476789726913 144312194143606107592295185)
  ·
    refine ⟨108234145607704580694221389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144312194143606107592295185 108234145607704580694221389)
    ·
      refine ⟨40587804602889217760333021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108234145607704580694221389 40587804602889217760333021)
      ·
        refine ⟨15220426726083456660124883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40587804602889217760333021 15220426726083456660124883)
        ·
          refine ⟨22830640089125184990187325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220426726083456660124883 22830640089125184990187325)
          ·
            refine ⟨8561490033421944371320247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22830640089125184990187325 8561490033421944371320247)
            ·
              refine ⟨12842235050132916556980371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561490033421944371320247 12842235050132916556980371)
              ·
                refine ⟨19263352575199374835470557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842235050132916556980371 19263352575199374835470557)
                ·
                  refine ⟨7223757215699765563301459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19263352575199374835470557 7223757215699765563301459)
                  ·
                    refine ⟨10835635823549648344952189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7223757215699765563301459 10835635823549648344952189)
                    ·
                      refine ⟨4063363433831118129357071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835635823549648344952189 4063363433831118129357071)
                      ·
                        rfl

theorem cell23_7913372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7913372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913372 prefixEnd_7913372 := by exact prefixLift 7913372
  have htrace : WordTrace (prefixWord ++ tailWord_7913372) baseStart_7913372 baseEnd_7913372 := by
    simpa [prefixWord, tailWord_7913372, baseEnd_7913372] using wordTrace_append hprefix tailTrace_7913372
  have hstable : (prefixWord ++ tailWord_7913372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913372).length < 2 ^ (prefixWord ++ tailWord_7913372).sum := by decide
  have hdescent : baseEnd_7913372 < baseStart_7913372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913391 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_7913391 : Nat := 118140960795 + 7913391 * 2 ^ 59
def prefixEnd_7913391 : Nat := 4983230072969 + 3 ^ 40 * 7913391 * 2
def baseEnd_7913391 : Nat := 4063373189963553555019483

theorem tailTrace_7913391 : CollatzResearch.WordTrace tailWord_7913391 prefixEnd_7913391 4063373189963553555019483 := by
  unfold tailWord_7913391
  simp only [CollatzResearch.WordTrace]
  refine ⟨288625081274143381429532027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192416720849428920953021351 288625081274143381429532027)
  ·
    refine ⟨432937621911215072144298041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288625081274143381429532027 432937621911215072144298041)
    ·
      refine ⟨324703216433411304108223531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432937621911215072144298041 324703216433411304108223531)
      ·
        refine ⟨487054824650116956162335297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324703216433411304108223531 487054824650116956162335297)
        ·
          refine ⟨365291118487587717121751473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487054824650116956162335297 365291118487587717121751473)
          ·
            refine ⟨273968338865690787841313605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365291118487587717121751473 273968338865690787841313605)
            ·
              refine ⟨51369063537317022720246301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273968338865690787841313605 51369063537317022720246301)
              ·
                refine ⟨19263398826493883520092363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51369063537317022720246301 19263398826493883520092363)
                ·
                  refine ⟨28895098239740825280138545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19263398826493883520092363 28895098239740825280138545)
                  ·
                    refine ⟨21671323679805618960103909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28895098239740825280138545 21671323679805618960103909)
                    ·
                      refine ⟨4063373189963553555019483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21671323679805618960103909 4063373189963553555019483)
                      ·
                        rfl

theorem cell23_7913391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_7913391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913391 prefixEnd_7913391 := by exact prefixLift 7913391
  have htrace : WordTrace (prefixWord ++ tailWord_7913391) baseStart_7913391 baseEnd_7913391 := by
    simpa [prefixWord, tailWord_7913391, baseEnd_7913391] using wordTrace_append hprefix tailTrace_7913391
  have hstable : (prefixWord ++ tailWord_7913391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913391).length < 2 ^ (prefixWord ++ tailWord_7913391).sum := by decide
  have hdescent : baseEnd_7913391 < baseStart_7913391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913428 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7913428 : Nat := 118140960795 + 7913428 * 2 ^ 59
def prefixEnd_7913428 : Nat := 4983230072969 + 3 ^ 40 * 7913428 * 2
def baseEnd_7913428 : Nat := 4063392188747769910256813

theorem tailTrace_7913428 : CollatzResearch.WordTrace tailWord_7913428 prefixEnd_7913428 4063392188747769910256813 := by
  unfold tailWord_7913428
  simp only [CollatzResearch.WordTrace]
  refine ⟨144313215387504668374314469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192417620516672891165752625 144313215387504668374314469)
  ·
    refine ⟨27058727885157125320183963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144313215387504668374314469 27058727885157125320183963)
    ·
      refine ⟨40588091827735687980275945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27058727885157125320183963 40588091827735687980275945)
      ·
        refine ⟨30441068870801765985206959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40588091827735687980275945 30441068870801765985206959)
        ·
          refine ⟨45661603306202648977810439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30441068870801765985206959 45661603306202648977810439)
          ·
            refine ⟨68492404959303973466715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45661603306202648977810439 68492404959303973466715659)
            ·
              refine ⟨102738607438955960200073489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68492404959303973466715659 102738607438955960200073489)
              ·
                refine ⟨77053955579216970150055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102738607438955960200073489 77053955579216970150055117)
                ·
                  refine ⟨28895233342206363806270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77053955579216970150055117 28895233342206363806270669)
                  ·
                    refine ⟨10835712503327386427351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28895233342206363806270669 10835712503327386427351501)
                    ·
                      refine ⟨4063392188747769910256813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10835712503327386427351501 4063392188747769910256813)
                      ·
                        rfl

theorem cell23_7913428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7913428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913428 prefixEnd_7913428 := by exact prefixLift 7913428
  have htrace : WordTrace (prefixWord ++ tailWord_7913428) baseStart_7913428 baseEnd_7913428 := by
    simpa [prefixWord, tailWord_7913428, baseEnd_7913428] using wordTrace_append hprefix tailTrace_7913428
  have hstable : (prefixWord ++ tailWord_7913428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913428).length < 2 ^ (prefixWord ++ tailWord_7913428).sum := by decide
  have hdescent : baseEnd_7913428 < baseStart_7913428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913429 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7913429 : Nat := 118140960795 + 7913429 * 2 ^ 59
def prefixEnd_7913429 : Nat := 4983230072969 + 3 ^ 40 * 7913429 * 2
def baseEnd_7913429 : Nat := 4063392702228424406344309

theorem tailTrace_7913429 : CollatzResearch.WordTrace tailWord_7913429 prefixEnd_7913429 4063392702228424406344309 := by
  unfold tailWord_7913429
  simp only [CollatzResearch.WordTrace]
  refine ⟨288626467248005713919415341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192417644832003809279610227 288626467248005713919415341)
  ·
    refine ⟨108234925218002142719780753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288626467248005713919415341 108234925218002142719780753)
    ·
      refine ⟨81176193913501607039835565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108234925218002142719780753 81176193913501607039835565)
      ·
        refine ⟨30441072717563102639938337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81176193913501607039835565 30441072717563102639938337)
        ·
          refine ⟨22830804538172326979953753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30441072717563102639938337 22830804538172326979953753)
          ·
            refine ⟨17123103403629245234965315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22830804538172326979953753 17123103403629245234965315)
            ·
              refine ⟨25684655105443867852447973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17123103403629245234965315 25684655105443867852447973)
              ·
                refine ⟨4815872832270725222333995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25684655105443867852447973 4815872832270725222333995)
                ·
                  refine ⟨7223809248406087833500993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815872832270725222333995 7223809248406087833500993)
                  ·
                    refine ⟨5417856936304565875125745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223809248406087833500993 5417856936304565875125745)
                    ·
                      refine ⟨4063392702228424406344309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417856936304565875125745 4063392702228424406344309)
                      ·
                        rfl

theorem cell23_7913429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7913429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913429 prefixEnd_7913429 := by exact prefixLift 7913429
  have htrace : WordTrace (prefixWord ++ tailWord_7913429) baseStart_7913429 baseEnd_7913429 := by
    simpa [prefixWord, tailWord_7913429, baseEnd_7913429] using wordTrace_append hprefix tailTrace_7913429
  have hstable : (prefixWord ++ tailWord_7913429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913429).length < 2 ^ (prefixWord ++ tailWord_7913429).sum := by decide
  have hdescent : baseEnd_7913429 < baseStart_7913429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913442 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7913442 : Nat := 118140960795 + 7913442 * 2 ^ 59
def prefixEnd_7913442 : Nat := 4983230072969 + 3 ^ 40 * 7913442 * 2
def baseEnd_7913442 : Nat := 4063399377476932855481749

theorem tailTrace_7913442 : CollatzResearch.WordTrace tailWord_7913442 prefixEnd_7913442 4063399377476932855481749 := by
  unfold tailWord_7913442
  simp only [CollatzResearch.WordTrace]
  refine ⟨72156735349239654284909645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192417960931305744759759053 72156735349239654284909645)
  ·
    refine ⟨27058775755964870356841117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72156735349239654284909645 27058775755964870356841117)
    ·
      refine ⟨10147040908486826383815419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27058775755964870356841117 10147040908486826383815419)
      ·
        refine ⟨15220561362730239575723129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147040908486826383815419 15220561362730239575723129)
        ·
          refine ⟨11415421022047679681792347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15220561362730239575723129 11415421022047679681792347)
          ·
            refine ⟨17123131533071519522688521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415421022047679681792347 17123131533071519522688521)
            ·
              refine ⟨12842348649803639642016391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17123131533071519522688521 12842348649803639642016391)
              ·
                refine ⟨19263522974705459463024587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842348649803639642016391 19263522974705459463024587)
                ·
                  refine ⟨28895284462058189194536881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19263522974705459463024587 28895284462058189194536881)
                  ·
                    refine ⟨21671463346543641895902661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28895284462058189194536881 21671463346543641895902661)
                    ·
                      refine ⟨4063399377476932855481749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21671463346543641895902661 4063399377476932855481749)
                      ·
                        rfl

theorem cell23_7913442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7913442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913442 prefixEnd_7913442 := by exact prefixLift 7913442
  have htrace : WordTrace (prefixWord ++ tailWord_7913442) baseStart_7913442 baseEnd_7913442 := by
    simpa [prefixWord, tailWord_7913442, baseEnd_7913442] using wordTrace_append hprefix tailTrace_7913442
  have hstable : (prefixWord ++ tailWord_7913442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913442).length < 2 ^ (prefixWord ++ tailWord_7913442).sum := by decide
  have hdescent : baseEnd_7913442 < baseStart_7913442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913455 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 1, 3, 2]
def baseStart_7913455 : Nat := 118140960795 + 7913455 * 2 ^ 59
def prefixEnd_7913455 : Nat := 4983230072969 + 3 ^ 40 * 7913455 * 2
def baseEnd_7913455 : Nat := 4063406052725441304619189

theorem tailTrace_7913455 : CollatzResearch.WordTrace tailWord_7913455 prefixEnd_7913455 4063406052725441304619189 := by
  unfold tailWord_7913455
  simp only [CollatzResearch.WordTrace]
  refine ⟨288627415545911520359861819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192418277030607680239907879 288627415545911520359861819)
  ·
    refine ⟨432941123318867280539792729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288627415545911520359861819 432941123318867280539792729)
    ·
      refine ⟨324705842489150460404844547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432941123318867280539792729 324705842489150460404844547)
      ·
        refine ⟨487058763733725690607266821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324705842489150460404844547 487058763733725690607266821)
        ·
          refine ⟨91323518200073566988862529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487058763733725690607266821 91323518200073566988862529)
          ·
            refine ⟨68492638650055175241646897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91323518200073566988862529 68492638650055175241646897)
            ·
              refine ⟨51369478987541381431235173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68492638650055175241646897 51369478987541381431235173)
              ·
                refine ⟨9631777310164009018356595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51369478987541381431235173 9631777310164009018356595)
                ·
                  refine ⟨14447665965246013527534893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9631777310164009018356595 14447665965246013527534893)
                  ·
                    refine ⟨5417874736967255072825585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14447665965246013527534893 5417874736967255072825585)
                    ·
                      refine ⟨4063406052725441304619189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417874736967255072825585 4063406052725441304619189)
                      ·
                        rfl

theorem cell23_7913455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 3, 2].length) (baseStart_7913455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913455 prefixEnd_7913455 := by exact prefixLift 7913455
  have htrace : WordTrace (prefixWord ++ tailWord_7913455) baseStart_7913455 baseEnd_7913455 := by
    simpa [prefixWord, tailWord_7913455, baseEnd_7913455] using wordTrace_append hprefix tailTrace_7913455
  have hstable : (prefixWord ++ tailWord_7913455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913455).length < 2 ^ (prefixWord ++ tailWord_7913455).sum := by decide
  have hdescent : baseEnd_7913455 < baseStart_7913455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913471 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_7913471 : Nat := 118140960795 + 7913471 * 2 ^ 59
def prefixEnd_7913471 : Nat := 4983230072969 + 3 ^ 40 * 7913471 * 2
def baseEnd_7913471 : Nat := 4063414268415913242019115

theorem tailTrace_7913471 : CollatzResearch.WordTrace tailWord_7913471 prefixEnd_7913471 4063414268415913242019115 := by
  unfold tailWord_7913471
  simp only [CollatzResearch.WordTrace]
  refine ⟨288627999113853555092444267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192418666075902370061629511 288627999113853555092444267)
  ·
    refine ⟨432941998670780332638666401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288627999113853555092444267 432941998670780332638666401)
    ·
      refine ⟨324706499003085249478999801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432941998670780332638666401 324706499003085249478999801)
      ·
        refine ⟨243529874252313937109249851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324706499003085249478999801 243529874252313937109249851)
        ·
          refine ⟨365294811378470905663874777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243529874252313937109249851 365294811378470905663874777)
          ·
            refine ⟨273971108533853179247906083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365294811378470905663874777 273971108533853179247906083)
            ·
              refine ⟨410956662800779768871859125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273971108533853179247906083 410956662800779768871859125)
              ·
                refine ⟨38527187137573103331736793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410956662800779768871859125 38527187137573103331736793)
                ·
                  refine ⟨28895390353179827498802595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38527187137573103331736793 28895390353179827498802595)
                  ·
                    refine ⟨43343085529769741248203893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28895390353179827498802595 43343085529769741248203893)
                    ·
                      refine ⟨4063414268415913242019115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43343085529769741248203893 4063414268415913242019115)
                      ·
                        rfl

theorem cell23_7913471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_7913471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913471 prefixEnd_7913471 := by exact prefixLift 7913471
  have htrace : WordTrace (prefixWord ++ tailWord_7913471) baseStart_7913471 baseEnd_7913471 := by
    simpa [prefixWord, tailWord_7913471, baseEnd_7913471] using wordTrace_append hprefix tailTrace_7913471
  have hstable : (prefixWord ++ tailWord_7913471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913471).length < 2 ^ (prefixWord ++ tailWord_7913471).sum := by decide
  have hdescent : baseEnd_7913471 < baseStart_7913471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913491 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 7]
def baseStart_7913491 : Nat := 118140960795 + 7913491 * 2 ^ 59
def prefixEnd_7913491 : Nat := 4983230072969 + 3 ^ 40 * 7913491 * 2
def baseEnd_7913491 : Nat := 451491615336555907085447

theorem tailTrace_7913491 : CollatzResearch.WordTrace tailWord_7913491 prefixEnd_7913491 451491615336555907085447 := by
  unfold tailWord_7913491
  simp only [CollatzResearch.WordTrace]
  refine ⟨288628728573781098508172327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192419152382520732338781551 288628728573781098508172327)
  ·
    refine ⟨432943092860671647762258491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288628728573781098508172327 432943092860671647762258491)
    ·
      refine ⟨649414639291007471643387737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432943092860671647762258491 649414639291007471643387737)
      ·
        refine ⟨487060979468255603732540803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649414639291007471643387737 487060979468255603732540803)
        ·
          refine ⟨730591469202383405598811205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487060979468255603732540803 730591469202383405598811205)
          ·
            refine ⟨136985900475446888549777101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730591469202383405598811205 136985900475446888549777101)
            ·
              refine ⟨51369712678292583206166413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136985900475446888549777101 51369712678292583206166413)
              ·
                refine ⟨19263642254359718702312405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51369712678292583206166413 19263642254359718702312405)
                ·
                  refine ⟨451491615336555907085447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19263642254359718702312405 451491615336555907085447)
                  ·
                    rfl

theorem cell23_7913491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 7].length) (baseStart_7913491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913491 prefixEnd_7913491 := by exact prefixLift 7913491
  have htrace : WordTrace (prefixWord ++ tailWord_7913491) baseStart_7913491 baseEnd_7913491 := by
    simpa [prefixWord, tailWord_7913491, baseEnd_7913491] using wordTrace_append hprefix tailTrace_7913491
  have hstable : (prefixWord ++ tailWord_7913491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913491).length < 2 ^ (prefixWord ++ tailWord_7913491).sum := by decide
  have hdescent : baseEnd_7913491 < baseStart_7913491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913498 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_7913498 : Nat := 118140960795 + 7913498 * 2 ^ 59
def prefixEnd_7913498 : Nat := 4983230072969 + 3 ^ 40 * 7913498 * 2
def baseEnd_7913498 : Nat := 4063428132393584636381491

theorem tailTrace_7913498 : CollatzResearch.WordTrace tailWord_7913498 prefixEnd_7913498 4063428132393584636381491 := by
  unfold tailWord_7913498
  simp only [CollatzResearch.WordTrace]
  refine ⟨72157245971188934675919287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192419322589837159135784765 72157245971188934675919287)
  ·
    refine ⟨108235868956783402013878931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72157245971188934675919287 108235868956783402013878931)
    ·
      refine ⟨162353803435175103020818397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108235868956783402013878931 162353803435175103020818397)
      ·
        refine ⟨60882676288190663632806899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162353803435175103020818397 60882676288190663632806899)
        ·
          refine ⟨91324014432285995449210349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60882676288190663632806899 91324014432285995449210349)
          ·
            refine ⟨34246505412107248293453881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91324014432285995449210349 34246505412107248293453881)
            ·
              refine ⟨25684879059080436220090411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34246505412107248293453881 25684879059080436220090411)
              ·
                refine ⟨38527318588620654330135617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25684879059080436220090411 38527318588620654330135617)
                ·
                  refine ⟨28895488941465490747601713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38527318588620654330135617 28895488941465490747601713)
                  ·
                    refine ⟨21671616706099118060701285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28895488941465490747601713 21671616706099118060701285)
                    ·
                      refine ⟨4063428132393584636381491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21671616706099118060701285 4063428132393584636381491)
                      ·
                        rfl

theorem cell23_7913498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_7913498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913498 prefixEnd_7913498 := by exact prefixLift 7913498
  have htrace : WordTrace (prefixWord ++ tailWord_7913498) baseStart_7913498 baseEnd_7913498 := by
    simpa [prefixWord, tailWord_7913498, baseEnd_7913498] using wordTrace_append hprefix tailTrace_7913498
  have hstable : (prefixWord ++ tailWord_7913498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913498).length < 2 ^ (prefixWord ++ tailWord_7913498).sum := by decide
  have hdescent : baseEnd_7913498 < baseStart_7913498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913525 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 5]
def baseStart_7913525 : Nat := 118140960795 + 7913525 * 2 ^ 59
def prefixEnd_7913525 : Nat := 4983230072969 + 3 ^ 40 * 7913525 * 2
def baseEnd_7913525 : Nat := 451493555152361781193763

theorem tailTrace_7913525 : CollatzResearch.WordTrace tailWord_7913525 prefixEnd_7913525 451493555152361781193763 := by
  unfold tailWord_7913525
  simp only [CollatzResearch.WordTrace]
  refine ⟨288629968655657922314910029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192419979103771948209940019 288629968655657922314910029)
  ·
    refine ⟨108236238245871720868091261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288629968655657922314910029 108236238245871720868091261)
    ·
      refine ⟨40588589342201895325534223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108236238245871720868091261 40588589342201895325534223)
      ·
        refine ⟨60882884013302842988301335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40588589342201895325534223 60882884013302842988301335)
        ·
          refine ⟨91324326019954264482452003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60882884013302842988301335 91324326019954264482452003)
          ·
            refine ⟨136986489029931396723678005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91324326019954264482452003 136986489029931396723678005)
            ·
              refine ⟨12842483346556068442844813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136986489029931396723678005 12842483346556068442844813)
              ·
                refine ⟨4815931254958525666066805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12842483346556068442844813 4815931254958525666066805)
                ·
                  refine ⟨451493555152361781193763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815931254958525666066805 451493555152361781193763)
                  ·
                    rfl

theorem cell23_7913525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_7913525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913525 prefixEnd_7913525 := by exact prefixLift 7913525
  have htrace : WordTrace (prefixWord ++ tailWord_7913525) baseStart_7913525 baseEnd_7913525 := by
    simpa [prefixWord, tailWord_7913525, baseEnd_7913525] using wordTrace_append hprefix tailTrace_7913525
  have hstable : (prefixWord ++ tailWord_7913525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913525).length < 2 ^ (prefixWord ++ tailWord_7913525).sum := by decide
  have hdescent : baseEnd_7913525 < baseStart_7913525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_7913531 : Nat := 118140960795 + 7913531 * 2 ^ 59
def prefixEnd_7913531 : Nat := 4983230072969 + 3 ^ 40 * 7913531 * 2
def baseEnd_7913531 : Nat := 4063445077255183007268839

theorem tailTrace_7913531 : CollatzResearch.WordTrace tailWord_7913531 prefixEnd_7913531 4063445077255183007268839 := by
  unfold tailWord_7913531
  simp only [CollatzResearch.WordTrace]
  refine ⟨288630187493636185339628447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192420124995757456893085631 288630187493636185339628447)
  ·
    refine ⟨432945281240454278009442671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288630187493636185339628447 432945281240454278009442671)
    ·
      refine ⟨649417921860681417014164007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432945281240454278009442671 649417921860681417014164007)
      ·
        refine ⟨974126882791022125521246011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649417921860681417014164007 974126882791022125521246011)
        ·
          refine ⟨1461190324186533188281869017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974126882791022125521246011 1461190324186533188281869017)
          ·
            refine ⟨1095892743139899891211401763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461190324186533188281869017 1095892743139899891211401763)
            ·
              refine ⟨1643839114709849836817102645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095892743139899891211401763 1643839114709849836817102645)
              ·
                refine ⟨154109917004048422201603373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1643839114709849836817102645 154109917004048422201603373)
                ·
                  refine ⟨57791218876518158325601265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154109917004048422201603373 57791218876518158325601265)
                  ·
                    refine ⟨43343414157388618744200949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57791218876518158325601265 43343414157388618744200949)
                    ·
                      refine ⟨4063445077255183007268839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43343414157388618744200949 4063445077255183007268839)
                      ·
                        rfl

theorem cell23_7913531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_7913531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913531 prefixEnd_7913531 := by exact prefixLift 7913531
  have htrace : WordTrace (prefixWord ++ tailWord_7913531) baseStart_7913531 baseEnd_7913531 := by
    simpa [prefixWord, tailWord_7913531, baseEnd_7913531] using wordTrace_append hprefix tailTrace_7913531
  have hstable : (prefixWord ++ tailWord_7913531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913531).length < 2 ^ (prefixWord ++ tailWord_7913531).sum := by decide
  have hdescent : baseEnd_7913531 < baseStart_7913531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913575 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_7913575 : Nat := 118140960795 + 7913575 * 2 ^ 59
def prefixEnd_7913575 : Nat := 4983230072969 + 3 ^ 40 * 7913575 * 2
def baseEnd_7913575 : Nat := 4063467670403980835118637

theorem tailTrace_7913575 : CollatzResearch.WordTrace tailWord_7913575 prefixEnd_7913575 4063467670403980835118637 := by
  unfold tailWord_7913575
  simp only [CollatzResearch.WordTrace]
  refine ⟨288631792305476780854230179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192421194870317853902820119 288631792305476780854230179)
  ·
    refine ⟨432947688458215171281345269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288631792305476780854230179 432947688458215171281345269)
    ·
      refine ⟨40588845792957672307626119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432947688458215171281345269 40588845792957672307626119)
      ·
        refine ⟨60883268689436508461439179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40588845792957672307626119 60883268689436508461439179)
        ·
          refine ⟨91324903034154762692158769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60883268689436508461439179 91324903034154762692158769)
          ·
            refine ⟨68493677275616072019119077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91324903034154762692158769 68493677275616072019119077)
            ·
              refine ⟨12842564489178013503584827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68493677275616072019119077 12842564489178013503584827)
              ·
                refine ⟨19263846733767020255377241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842564489178013503584827 19263846733767020255377241)
                ·
                  refine ⟨14447885050325265191532931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19263846733767020255377241 14447885050325265191532931)
                  ·
                    refine ⟨21671827575487897787299397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14447885050325265191532931 21671827575487897787299397)
                    ·
                      refine ⟨4063467670403980835118637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21671827575487897787299397 4063467670403980835118637)
                      ·
                        rfl

theorem cell23_7913575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_7913575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913575 prefixEnd_7913575 := by exact prefixLift 7913575
  have htrace : WordTrace (prefixWord ++ tailWord_7913575) baseStart_7913575 baseEnd_7913575 := by
    simpa [prefixWord, tailWord_7913575, baseEnd_7913575] using wordTrace_append hprefix tailTrace_7913575
  have hstable : (prefixWord ++ tailWord_7913575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913575).length < 2 ^ (prefixWord ++ tailWord_7913575).sum := by decide
  have hdescent : baseEnd_7913575 < baseStart_7913575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913649 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 6]
def baseStart_7913649 : Nat := 118140960795 + 7913649 * 2 ^ 59
def prefixEnd_7913649 : Nat := 4983230072969 + 3 ^ 40 * 7913649 * 2
def baseEnd_7913649 : Nat := 451500629774712616177033

theorem tailTrace_7913649 : CollatzResearch.WordTrace tailWord_7913649 prefixEnd_7913649 451500629774712616177033 := by
  unfold tailWord_7913649
  simp only [CollatzResearch.WordTrace]
  refine ⟨288634491307208691492424001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192422994204805794328282667 288634491307208691492424001)
  ·
    refine ⟨216475868480406518619318001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288634491307208691492424001 216475868480406518619318001)
    ·
      refine ⟨162356901360304888964488501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216475868480406518619318001 162356901360304888964488501)
      ·
        refine ⟨15220959502528583340420797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162356901360304888964488501 15220959502528583340420797)
        ·
          refine ⟨5707859813448218752657799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15220959502528583340420797 5707859813448218752657799)
          ·
            refine ⟨8561789720172328128986699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707859813448218752657799 8561789720172328128986699)
            ·
              refine ⟨12842684580258492193480049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561789720172328128986699 12842684580258492193480049)
              ·
                refine ⟨9632013435193869145110037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842684580258492193480049 9632013435193869145110037)
                ·
                  refine ⟨451500629774712616177033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9632013435193869145110037 451500629774712616177033)
                  ·
                    rfl

theorem cell23_7913649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_7913649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913649 prefixEnd_7913649 := by exact prefixLift 7913649
  have htrace : WordTrace (prefixWord ++ tailWord_7913649) baseStart_7913649 baseEnd_7913649 := by
    simpa [prefixWord, tailWord_7913649, baseEnd_7913649] using wordTrace_append hprefix tailTrace_7913649
  have hstable : (prefixWord ++ tailWord_7913649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913649).length < 2 ^ (prefixWord ++ tailWord_7913649).sum := by decide
  have hdescent : baseEnd_7913649 < baseStart_7913649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913658 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_7913658 : Nat := 118140960795 + 7913658 * 2 ^ 59
def prefixEnd_7913658 : Nat := 4983230072969 + 3 ^ 40 * 7913658 * 2
def baseEnd_7913658 : Nat := 1354503429766101336793585

theorem tailTrace_7913658 : CollatzResearch.WordTrace tailWord_7913658 prefixEnd_7913658 1354503429766101336793585 := by
  unfold tailWord_7913658
  simp only [CollatzResearch.WordTrace]
  refine ⟨72158704891044021507375407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192423213042784057353001085 72158704891044021507375407)
  ·
    refine ⟨108238057336566032261063111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72158704891044021507375407 108238057336566032261063111)
    ·
      refine ⟨162357086004849048391594667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108238057336566032261063111 162357086004849048391594667)
      ·
        refine ⟨243535629007273572587392001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162357086004849048391594667 243535629007273572587392001)
        ·
          refine ⟨182651721755455179440544001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243535629007273572587392001 182651721755455179440544001)
          ·
            refine ⟨136988791316591384580408001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182651721755455179440544001 136988791316591384580408001)
            ·
              refine ⟨102741593487443538435306001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136988791316591384580408001 102741593487443538435306001)
              ·
                refine ⟨77056195115582653826479501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102741593487443538435306001 77056195115582653826479501)
                ·
                  refine ⟨28896073168343495184929813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77056195115582653826479501 28896073168343495184929813)
                  ·
                    refine ⟨1354503429766101336793585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28896073168343495184929813 1354503429766101336793585)
                    ·
                      rfl

theorem cell23_7913658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_7913658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913658 prefixEnd_7913658 := by exact prefixLift 7913658
  have htrace : WordTrace (prefixWord ++ tailWord_7913658) baseStart_7913658 baseEnd_7913658 := by
    simpa [prefixWord, tailWord_7913658, baseEnd_7913658] using wordTrace_append hprefix tailTrace_7913658
  have hstable : (prefixWord ++ tailWord_7913658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913658).length < 2 ^ (prefixWord ++ tailWord_7913658).sum := by decide
  have hdescent : baseEnd_7913658 < baseStart_7913658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913666 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7913666 : Nat := 118140960795 + 7913666 * 2 ^ 59
def prefixEnd_7913666 : Nat := 4983230072969 + 3 ^ 40 * 7913666 * 2
def baseEnd_7913666 : Nat := 451501599682615553231191

theorem tailTrace_7913666 : CollatzResearch.WordTrace tailWord_7913666 prefixEnd_7913666 451501599682615553231191 := by
  unfold tailWord_7913666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72158777837036775848948213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192423407565431402263861901 72158777837036775848948213)
  ·
    refine ⟨6764885422222197735838895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72158777837036775848948213 6764885422222197735838895)
    ·
      refine ⟨10147328133333296603758343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764885422222197735838895 10147328133333296603758343)
      ·
        refine ⟨15220992199999944905637515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147328133333296603758343 15220992199999944905637515)
        ·
          refine ⟨22831488299999917358456273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220992199999944905637515 22831488299999917358456273)
          ·
            refine ⟨17123616224999938018842205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22831488299999917358456273 17123616224999938018842205)
            ·
              refine ⟨6421356084374976757065827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123616224999938018842205 6421356084374976757065827)
              ·
                refine ⟨9632034126562465135598741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421356084374976757065827 9632034126562465135598741)
                ·
                  refine ⟨451501599682615553231191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9632034126562465135598741 451501599682615553231191)
                  ·
                    rfl

theorem cell23_7913666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7913666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913666 prefixEnd_7913666 := by exact prefixLift 7913666
  have htrace : WordTrace (prefixWord ++ tailWord_7913666) baseStart_7913666 baseEnd_7913666 := by
    simpa [prefixWord, tailWord_7913666, baseEnd_7913666] using wordTrace_append hprefix tailTrace_7913666
  have hstable : (prefixWord ++ tailWord_7913666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913666).length < 2 ^ (prefixWord ++ tailWord_7913666).sum := by decide
  have hdescent : baseEnd_7913666 < baseStart_7913666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913682 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_7913682 : Nat := 118140960795 + 7913682 * 2 ^ 59
def prefixEnd_7913682 : Nat := 4983230072969 + 3 ^ 40 * 7913682 * 2
def baseEnd_7913682 : Nat := 4063522612834011916480645

theorem tailTrace_7913682 : CollatzResearch.WordTrace tailWord_7913682 prefixEnd_7913682 4063522612834011916480645 := by
  unfold tailWord_7913682
  simp only [CollatzResearch.WordTrace]
  refine ⟨72158923729022284532093825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192423796610726092085583533 72158923729022284532093825)
  ·
    refine ⟨54119192796766713399070369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72158923729022284532093825 54119192796766713399070369)
    ·
      refine ⟨40589394597575035049302777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54119192796766713399070369 40589394597575035049302777)
      ·
        refine ⟨30442045948181276286977083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40589394597575035049302777 30442045948181276286977083)
        ·
          refine ⟨45663068922271914430465625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30442045948181276286977083 45663068922271914430465625)
          ·
            refine ⟨34247301691703935822849219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45663068922271914430465625 34247301691703935822849219)
            ·
              refine ⟨51370952537555903734273829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34247301691703935822849219 51370952537555903734273829)
              ·
                refine ⟨9632053600791731950176343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51370952537555903734273829 9632053600791731950176343)
                ·
                  refine ⟨14448080401187597925264515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632053600791731950176343 14448080401187597925264515)
                  ·
                    refine ⟨21672120601781396887896773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14448080401187597925264515 21672120601781396887896773)
                    ·
                      refine ⟨4063522612834011916480645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21672120601781396887896773 4063522612834011916480645)
                      ·
                        rfl

theorem cell23_7913682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_7913682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913682 prefixEnd_7913682 := by exact prefixLift 7913682
  have htrace : WordTrace (prefixWord ++ tailWord_7913682) baseStart_7913682 baseEnd_7913682 := by
    simpa [prefixWord, tailWord_7913682, baseEnd_7913682] using wordTrace_append hprefix tailTrace_7913682
  have hstable : (prefixWord ++ tailWord_7913682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913682).length < 2 ^ (prefixWord ++ tailWord_7913682).sum := by decide
  have hdescent : baseEnd_7913682 < baseStart_7913682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913693 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7913693 : Nat := 118140960795 + 7913693 * 2 ^ 59
def prefixEnd_7913693 : Nat := 4983230072969 + 3 ^ 40 * 7913693 * 2
def baseEnd_7913693 : Nat := 4063528261121211373443095

theorem tailTrace_7913693 : CollatzResearch.WordTrace tailWord_7913693 prefixEnd_7913693 4063528261121211373443095 := by
  unfold tailWord_7913693
  simp only [CollatzResearch.WordTrace]
  refine ⟨288636096119049287007025733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192424064079366191338017155 288636096119049287007025733)
  ·
    refine ⟨54119268022321741313817325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288636096119049287007025733 54119268022321741313817325)
    ·
      refine ⟨20294725508370652992681497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54119268022321741313817325 20294725508370652992681497)
      ·
        refine ⟨15221044131277989744511123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20294725508370652992681497 15221044131277989744511123)
        ·
          refine ⟨22831566196916984616766685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221044131277989744511123 22831566196916984616766685)
          ·
            refine ⟨8561837323843869231287507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22831566196916984616766685 8561837323843869231287507)
            ·
              refine ⟨12842755985765803846931261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561837323843869231287507 12842755985765803846931261)
              ·
                refine ⟨4816033494662176442599223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12842755985765803846931261 4816033494662176442599223)
                ·
                  refine ⟨7224050241993264663898835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816033494662176442599223 7224050241993264663898835)
                  ·
                    refine ⟨10836075362989896995848253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224050241993264663898835 10836075362989896995848253)
                    ·
                      refine ⟨4063528261121211373443095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836075362989896995848253 4063528261121211373443095)
                      ·
                        rfl

theorem cell23_7913693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7913693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913693 prefixEnd_7913693 := by exact prefixLift 7913693
  have htrace : WordTrace (prefixWord ++ tailWord_7913693) baseStart_7913693 baseEnd_7913693 := by
    simpa [prefixWord, tailWord_7913693, baseEnd_7913693] using wordTrace_append hprefix tailTrace_7913693
  have hstable : (prefixWord ++ tailWord_7913693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913693).length < 2 ^ (prefixWord ++ tailWord_7913693).sum := by decide
  have hdescent : baseEnd_7913693 < baseStart_7913693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913767 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7913767 : Nat := 118140960795 + 7913767 * 2 ^ 59
def prefixEnd_7913767 : Nat := 4983230072969 + 3 ^ 40 * 7913767 * 2
def baseEnd_7913767 : Nat := 4063566258689644083917755

theorem tailTrace_7913767 : CollatzResearch.WordTrace tailWord_7913767 prefixEnd_7913767 4063566258689644083917755 := by
  unfold tailWord_7913767
  simp only [CollatzResearch.WordTrace]
  refine ⟨288638795120781197645219555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192425863413854131763479703 288638795120781197645219555)
  ·
    refine ⟨432958192681171796467829333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288638795120781197645219555 432958192681171796467829333)
    ·
      refine ⟨5073728820482481989857375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 432958192681171796467829333 5073728820482481989857375)
      ·
        refine ⟨7610593230723722984786063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073728820482481989857375 7610593230723722984786063)
        ·
          refine ⟨11415889846085584477179095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610593230723722984786063 11415889846085584477179095)
          ·
            refine ⟨17123834769128376715768643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415889846085584477179095 17123834769128376715768643)
            ·
              refine ⟨25685752153692565073652965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17123834769128376715768643 25685752153692565073652965)
              ·
                refine ⟨4816078528817355951309931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25685752153692565073652965 4816078528817355951309931)
                ·
                  refine ⟨7224117793226033926964897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816078528817355951309931 7224117793226033926964897)
                  ·
                    refine ⟨5418088344919525445223673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224117793226033926964897 5418088344919525445223673)
                    ·
                      refine ⟨4063566258689644083917755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418088344919525445223673 4063566258689644083917755)
                      ·
                        rfl

theorem cell23_7913767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7913767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913767 prefixEnd_7913767 := by exact prefixLift 7913767
  have htrace : WordTrace (prefixWord ++ tailWord_7913767) baseStart_7913767 baseEnd_7913767 := by
    simpa [prefixWord, tailWord_7913767, baseEnd_7913767] using wordTrace_append hprefix tailTrace_7913767
  have hstable : (prefixWord ++ tailWord_7913767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913767).length < 2 ^ (prefixWord ++ tailWord_7913767).sum := by decide
  have hdescent : baseEnd_7913767 < baseStart_7913767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913775 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_7913775 : Nat := 118140960795 + 7913775 * 2 ^ 59
def prefixEnd_7913775 : Nat := 4983230072969 + 3 ^ 40 * 7913775 * 2
def baseEnd_7913775 : Nat := 4063570366534880052617717

theorem tailTrace_7913775 : CollatzResearch.WordTrace tailWord_7913775 prefixEnd_7913775 4063570366534880052617717 := by
  unfold tailWord_7913775
  simp only [CollatzResearch.WordTrace]
  refine ⟨288639086904752215011510779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192426057936501476674340519 288639086904752215011510779)
  ·
    refine ⟨432958630357128322517266169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288639086904752215011510779 432958630357128322517266169)
    ·
      refine ⟨324718972767846241887949627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432958630357128322517266169 324718972767846241887949627)
      ·
        refine ⟨487078459151769362831924441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324718972767846241887949627 487078459151769362831924441)
        ·
          refine ⟨365308844363827022123943331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487078459151769362831924441 365308844363827022123943331)
          ·
            refine ⟨547963266545740533185914997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365308844363827022123943331 547963266545740533185914997)
            ·
              refine ⟨51371556238663174986179531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547963266545740533185914997 51371556238663174986179531)
              ·
                refine ⟨77057334357994762479269297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51371556238663174986179531 77057334357994762479269297)
                ·
                  refine ⟨57793000768496071859451973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77057334357994762479269297 57793000768496071859451973)
                  ·
                    refine ⟨10836187644093013473647245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57793000768496071859451973 10836187644093013473647245)
                    ·
                      refine ⟨4063570366534880052617717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836187644093013473647245 4063570366534880052617717)
                      ·
                        rfl

theorem cell23_7913775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_7913775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913775 prefixEnd_7913775 := by exact prefixLift 7913775
  have htrace : WordTrace (prefixWord ++ tailWord_7913775) baseStart_7913775 baseEnd_7913775 := by
    simpa [prefixWord, tailWord_7913775, baseEnd_7913775] using wordTrace_append hprefix tailTrace_7913775
  have hstable : (prefixWord ++ tailWord_7913775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913775).length < 2 ^ (prefixWord ++ tailWord_7913775).sum := by decide
  have hdescent : baseEnd_7913775 < baseStart_7913775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913916 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7913916 : Nat := 118140960795 + 7913916 * 2 ^ 59
def prefixEnd_7913916 : Nat := 4983230072969 + 3 ^ 40 * 7913916 * 2
def baseEnd_7913916 : Nat := 4063642767307164000954569

theorem tailTrace_7913916 : CollatzResearch.WordTrace tailWord_7913916 prefixEnd_7913916 4063642767307164000954569 := by
  unfold tailWord_7913916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144322114798620698046196801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192429486398160930728262401 144322114798620698046196801)
  ·
    refine ⟨108241586098965523534647601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144322114798620698046196801 108241586098965523534647601)
    ·
      refine ⟨81181189574224142650985701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108241586098965523534647601 81181189574224142650985701)
      ·
        refine ⟨15221473045167026747059819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81181189574224142650985701 15221473045167026747059819)
        ·
          refine ⟨22832209567750540120589729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221473045167026747059819 22832209567750540120589729)
          ·
            refine ⟨17124157175812905090442297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22832209567750540120589729 17124157175812905090442297)
            ·
              refine ⟨12843117881859678817831723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17124157175812905090442297 12843117881859678817831723)
              ·
                refine ⟨19264676822789518226747585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12843117881859678817831723 19264676822789518226747585)
                ·
                  refine ⟨14448507617092138670060689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19264676822789518226747585 14448507617092138670060689)
                  ·
                    refine ⟨10836380712819104002545517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14448507617092138670060689 10836380712819104002545517)
                    ·
                      refine ⟨4063642767307164000954569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836380712819104002545517 4063642767307164000954569)
                      ·
                        rfl

theorem cell23_7913916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7913916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913916 prefixEnd_7913916 := by exact prefixLift 7913916
  have htrace : WordTrace (prefixWord ++ tailWord_7913916) baseStart_7913916 baseEnd_7913916 := by
    simpa [prefixWord, tailWord_7913916, baseEnd_7913916] using wordTrace_append hprefix tailTrace_7913916
  have hstable : (prefixWord ++ tailWord_7913916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913916).length < 2 ^ (prefixWord ++ tailWord_7913916).sum := by decide
  have hdescent : baseEnd_7913916 < baseStart_7913916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913925 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_7913925 : Nat := 118140960795 + 7913925 * 2 ^ 59
def prefixEnd_7913925 : Nat := 4983230072969 + 3 ^ 40 * 7913925 * 2
def baseEnd_7913925 : Nat := 4063647388633054465742027

theorem tailTrace_7913925 : CollatzResearch.WordTrace tailWord_7913925 prefixEnd_7913925 4063647388633054465742027 := by
  unfold tailWord_7913925
  simp only [CollatzResearch.WordTrace]
  refine ⟨288644557854208790629471229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192429705236139193752980819 288644557854208790629471229)
  ·
    refine ⟨108241709195328296486051711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288644557854208790629471229 108241709195328296486051711)
    ·
      refine ⟨162362563792992444729077567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108241709195328296486051711 162362563792992444729077567)
      ·
        refine ⟨243543845689488667093616351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162362563792992444729077567 243543845689488667093616351)
        ·
          refine ⟨365315768534233000640424527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243543845689488667093616351 365315768534233000640424527)
          ·
            refine ⟨547973652801349500960636791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365315768534233000640424527 547973652801349500960636791)
            ·
              refine ⟨821960479202024251440955187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547973652801349500960636791 821960479202024251440955187)
              ·
                refine ⟨1232940718803036377161432781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821960479202024251440955187 1232940718803036377161432781)
                ·
                  refine ⟨462352769551138641435537293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232940718803036377161432781 462352769551138641435537293)
                  ·
                    refine ⟨173382288581676990538326485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462352769551138641435537293 173382288581676990538326485)
                    ·
                      refine ⟨4063647388633054465742027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173382288581676990538326485 4063647388633054465742027)
                      ·
                        rfl

theorem cell23_7913925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_7913925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913925 prefixEnd_7913925 := by exact prefixLift 7913925
  have htrace : WordTrace (prefixWord ++ tailWord_7913925) baseStart_7913925 baseEnd_7913925 := by
    simpa [prefixWord, tailWord_7913925, baseEnd_7913925] using wordTrace_append hprefix tailTrace_7913925
  have hstable : (prefixWord ++ tailWord_7913925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913925).length < 2 ^ (prefixWord ++ tailWord_7913925).sum := by decide
  have hdescent : baseEnd_7913925 < baseStart_7913925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913940 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_7913940 : Nat := 118140960795 + 7913940 * 2 ^ 59
def prefixEnd_7913940 : Nat := 4983230072969 + 3 ^ 40 * 7913940 * 2
def baseEnd_7913940 : Nat := 1354551696947623969018153

theorem tailTrace_7913940 : CollatzResearch.WordTrace tailWord_7913940 prefixEnd_7913940 1354551696947623969018153 := by
  unfold tailWord_7913940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144322552474577224095633637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192430069966102965460844849 144322552474577224095633637)
  ·
    refine ⟨27060478588983229517931307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144322552474577224095633637 27060478588983229517931307)
    ·
      refine ⟨40590717883474844276896961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27060478588983229517931307 40590717883474844276896961)
      ·
        refine ⟨30443038412606133207672721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40590717883474844276896961 30443038412606133207672721)
        ·
          refine ⟨22832278809454599905754541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30443038412606133207672721 22832278809454599905754541)
          ·
            refine ⟨8562104553545474964657953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22832278809454599905754541 8562104553545474964657953)
            ·
              refine ⟨6421578415159106223493465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562104553545474964657953 6421578415159106223493465)
              ·
                refine ⟨4816183811369329667620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421578415159106223493465 4816183811369329667620099)
                ·
                  refine ⟨7224275717053994501430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816183811369329667620099 7224275717053994501430149)
                  ·
                    refine ⟨1354551696947623969018153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224275717053994501430149 1354551696947623969018153)
                    ·
                      rfl

theorem cell23_7913940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_7913940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913940 prefixEnd_7913940 := by exact prefixLift 7913940
  have htrace : WordTrace (prefixWord ++ tailWord_7913940) baseStart_7913940 baseEnd_7913940 := by
    simpa [prefixWord, tailWord_7913940, baseEnd_7913940] using wordTrace_append hprefix tailTrace_7913940
  have hstable : (prefixWord ++ tailWord_7913940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913940).length < 2 ^ (prefixWord ++ tailWord_7913940).sum := by decide
  have hdescent : baseEnd_7913940 < baseStart_7913940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913952 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_7913952 : Nat := 118140960795 + 7913952 * 2 ^ 59
def prefixEnd_7913952 : Nat := 4983230072969 + 3 ^ 40 * 7913952 * 2
def baseEnd_7913952 : Nat := 4063661252610725860104403

theorem tailTrace_7913952 : CollatzResearch.WordTrace tailWord_7913952 prefixEnd_7913952 4063661252610725860104403 := by
  unfold tailWord_7913952
  simp only [CollatzResearch.WordTrace]
  refine ⟨144322771312555487120352055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192430361750073982827136073 144322771312555487120352055)
  ·
    refine ⟨216484156968833230680528083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144322771312555487120352055 216484156968833230680528083)
    ·
      refine ⟨324726235453249846020792125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216484156968833230680528083 324726235453249846020792125)
      ·
        refine ⟨121772338294968692257797047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324726235453249846020792125 121772338294968692257797047)
        ·
          refine ⟨182658507442453038386695571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121772338294968692257797047 182658507442453038386695571)
          ·
            refine ⟨273987761163679557580043357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182658507442453038386695571 273987761163679557580043357)
            ·
              refine ⟨102745410436379834092516259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273987761163679557580043357 102745410436379834092516259)
              ·
                refine ⟨154118115654569751138774389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102745410436379834092516259 154118115654569751138774389)
                ·
                  refine ⟨14448573342615914169260099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154118115654569751138774389 14448573342615914169260099)
                  ·
                    refine ⟨21672860013923871253890149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14448573342615914169260099 21672860013923871253890149)
                    ·
                      refine ⟨4063661252610725860104403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21672860013923871253890149 4063661252610725860104403)
                      ·
                        rfl

theorem cell23_7913952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_7913952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913952 prefixEnd_7913952 := by exact prefixLift 7913952
  have htrace : WordTrace (prefixWord ++ tailWord_7913952) baseStart_7913952 baseEnd_7913952 := by
    simpa [prefixWord, tailWord_7913952, baseEnd_7913952] using wordTrace_append hprefix tailTrace_7913952
  have hstable : (prefixWord ++ tailWord_7913952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913952).length < 2 ^ (prefixWord ++ tailWord_7913952).sum := by decide
  have hdescent : baseEnd_7913952 < baseStart_7913952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913969 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_7913969 : Nat := 118140960795 + 7913969 * 2 ^ 59
def prefixEnd_7913969 : Nat := 4983230072969 + 3 ^ 40 * 7913969 * 2
def baseEnd_7913969 : Nat := 4063669981781852293591825

theorem tailTrace_7913969 : CollatzResearch.WordTrace tailWord_7913969 prefixEnd_7913969 4063669981781852293591825 := by
  unfold tailWord_7913969
  simp only [CollatzResearch.WordTrace]
  refine ⟨288646162666049386144072961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192430775110699590762715307 288646162666049386144072961)
  ·
    refine ⟨216484621999537039608054721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288646162666049386144072961 216484621999537039608054721)
    ·
      refine ⟨162363466499652779706041041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216484621999537039608054721 162363466499652779706041041)
      ·
        refine ⟨121772599874739584779530781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162363466499652779706041041 121772599874739584779530781)
        ·
          refine ⟨45664724953027344292324043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121772599874739584779530781 45664724953027344292324043)
          ·
            refine ⟨68497087429541016438486065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45664724953027344292324043 68497087429541016438486065)
            ·
              refine ⟨51372815572155762328864549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68497087429541016438486065 51372815572155762328864549)
              ·
                refine ⟨9632402919779205436662103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51372815572155762328864549 9632402919779205436662103)
                ·
                  refine ⟨14448604379668808154993155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632402919779205436662103 14448604379668808154993155)
                  ·
                    refine ⟨21672906569503212232489733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14448604379668808154993155 21672906569503212232489733)
                    ·
                      refine ⟨4063669981781852293591825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21672906569503212232489733 4063669981781852293591825)
                      ·
                        rfl

theorem cell23_7913969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_7913969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913969 prefixEnd_7913969 := by exact prefixLift 7913969
  have htrace : WordTrace (prefixWord ++ tailWord_7913969) baseStart_7913969 baseEnd_7913969 := by
    simpa [prefixWord, tailWord_7913969, baseEnd_7913969] using wordTrace_append hprefix tailTrace_7913969
  have hstable : (prefixWord ++ tailWord_7913969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913969).length < 2 ^ (prefixWord ++ tailWord_7913969).sum := by decide
  have hdescent : baseEnd_7913969 < baseStart_7913969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913973 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7913973 : Nat := 118140960795 + 7913973 * 2 ^ 59
def prefixEnd_7913973 : Nat := 4983230072969 + 3 ^ 40 * 7913973 * 2
def baseEnd_7913973 : Nat := 4063672035704470277941807

theorem tailTrace_7913973 : CollatzResearch.WordTrace tailWord_7913973 prefixEnd_7913973 4063672035704470277941807 := by
  unfold tailWord_7913973
  simp only [CollatzResearch.WordTrace]
  refine ⟨288646308558034894827218573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192430872372023263218145715 288646308558034894827218573)
  ·
    refine ⟨108242365709263085560206965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288646308558034894827218573 108242365709263085560206965)
    ·
      refine ⟨10147721785243414271269403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108242365709263085560206965 10147721785243414271269403)
      ·
        refine ⟨15221582677865121406904105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147721785243414271269403 15221582677865121406904105)
        ·
          refine ⟨11416187008398841055178079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15221582677865121406904105 11416187008398841055178079)
          ·
            refine ⟨17124280512598261582767119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416187008398841055178079 17124280512598261582767119)
            ·
              refine ⟨25686420768897392374150679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17124280512598261582767119 25686420768897392374150679)
              ·
                refine ⟨38529631153346088561226019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25686420768897392374150679 38529631153346088561226019)
                ·
                  refine ⟨57794446730019132841839029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38529631153346088561226019 57794446730019132841839029)
                  ·
                    refine ⟨5418229380939293703922409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57794446730019132841839029 5418229380939293703922409)
                    ·
                      refine ⟨4063672035704470277941807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418229380939293703922409 4063672035704470277941807)
                      ·
                        rfl

theorem cell23_7913973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7913973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913973 prefixEnd_7913973 := by exact prefixLift 7913973
  have htrace : WordTrace (prefixWord ++ tailWord_7913973) baseStart_7913973 baseEnd_7913973 := by
    simpa [prefixWord, tailWord_7913973, baseEnd_7913973] using wordTrace_append hprefix tailTrace_7913973
  have hstable : (prefixWord ++ tailWord_7913973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913973).length < 2 ^ (prefixWord ++ tailWord_7913973).sum := by decide
  have hdescent : baseEnd_7913973 < baseStart_7913973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913996 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_7913996 : Nat := 118140960795 + 7913996 * 2 ^ 59
def prefixEnd_7913996 : Nat := 4983230072969 + 3 ^ 40 * 7913996 * 2
def baseEnd_7913996 : Nat := 1354561281919841229318067

theorem tailTrace_7913996 : CollatzResearch.WordTrace tailWord_7913996 prefixEnd_7913996 1354561281919841229318067 := by
  unfold tailWord_7913996
  simp only [CollatzResearch.WordTrace]
  refine ⟨144323573718475784877652921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192431431624634379836870561 144323573718475784877652921)
  ·
    refine ⟨108242680288856838658239691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144323573718475784877652921 108242680288856838658239691)
    ·
      refine ⟨162364020433285257987359537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108242680288856838658239691 162364020433285257987359537)
      ·
        refine ⟨121773015324963943490519653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162364020433285257987359537 121773015324963943490519653)
        ·
          refine ⟨22832440373430739404472435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121773015324963943490519653 22832440373430739404472435)
          ·
            refine ⟨34248660560146109106708653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832440373430739404472435 34248660560146109106708653)
            ·
              refine ⟨12843247710054790915015745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34248660560146109106708653 12843247710054790915015745)
              ·
                refine ⟨9632435782541093186261809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12843247710054790915015745 9632435782541093186261809)
                ·
                  refine ⟨7224326836905819889696357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632435782541093186261809 7224326836905819889696357)
                  ·
                    refine ⟨1354561281919841229318067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224326836905819889696357 1354561281919841229318067)
                    ·
                      rfl

theorem cell23_7913996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_7913996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913996 prefixEnd_7913996 := by exact prefixLift 7913996
  have htrace : WordTrace (prefixWord ++ tailWord_7913996) baseStart_7913996 baseEnd_7913996 := by
    simpa [prefixWord, tailWord_7913996, baseEnd_7913996] using wordTrace_append hprefix tailTrace_7913996
  have hstable : (prefixWord ++ tailWord_7913996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913996).length < 2 ^ (prefixWord ++ tailWord_7913996).sum := by decide
  have hdescent : baseEnd_7913996 < baseStart_7913996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7913997 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7913997 : Nat := 118140960795 + 7913997 * 2 ^ 59
def prefixEnd_7913997 : Nat := 4983230072969 + 3 ^ 40 * 7913997 * 2
def baseEnd_7913997 : Nat := 4063684359240178184041697

theorem tailTrace_7913997 : CollatzResearch.WordTrace tailWord_7913997 prefixEnd_7913997 4063684359240178184041697 := by
  unfold tailWord_7913997
  simp only [CollatzResearch.WordTrace]
  refine ⟨288647183909947946926092245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192431455939965297950728163 288647183909947946926092245)
  ·
    refine ⟨6765168372889405006080287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 288647183909947946926092245 6765168372889405006080287)
    ·
      refine ⟨10147752559334107509120431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765168372889405006080287 10147752559334107509120431)
      ·
        refine ⟨15221628839001161263680647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147752559334107509120431 15221628839001161263680647)
        ·
          refine ⟨22832443258501741895520971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221628839001161263680647 22832443258501741895520971)
          ·
            refine ⟨34248664887752612843281457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832443258501741895520971 34248664887752612843281457)
            ·
              refine ⟨25686498665814459632461093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34248664887752612843281457 25686498665814459632461093)
              ·
                refine ⟨4816218499840211181086455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25686498665814459632461093 4816218499840211181086455)
                ·
                  refine ⟨7224327749760316771629683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816218499840211181086455 7224327749760316771629683)
                  ·
                    refine ⟨10836491624640475157444525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224327749760316771629683 10836491624640475157444525)
                    ·
                      refine ⟨4063684359240178184041697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836491624640475157444525 4063684359240178184041697)
                      ·
                        rfl

theorem cell23_7913997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7913997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7913997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7913997 prefixEnd_7913997 := by exact prefixLift 7913997
  have htrace : WordTrace (prefixWord ++ tailWord_7913997) baseStart_7913997 baseEnd_7913997 := by
    simpa [prefixWord, tailWord_7913997, baseEnd_7913997] using wordTrace_append hprefix tailTrace_7913997
  have hstable : (prefixWord ++ tailWord_7913997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7913997).length < 2 ^ (prefixWord ++ tailWord_7913997).sum := by decide
  have hdescent : baseEnd_7913997 < baseStart_7913997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7913997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914003 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 1, 2, 2]
def baseStart_7914003 : Nat := 118140960795 + 7914003 * 2 ^ 59
def prefixEnd_7914003 : Nat := 4983230072969 + 3 ^ 40 * 7914003 * 2
def baseEnd_7914003 : Nat := 4063687440124105160566669

theorem tailTrace_7914003 : CollatzResearch.WordTrace tailWord_7914003 prefixEnd_7914003 4063687440124105160566669 := by
  unfold tailWord_7914003
  simp only [CollatzResearch.WordTrace]
  refine ⟨288647402747926209950810663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192431601831950806633873775 288647402747926209950810663)
  ·
    refine ⟨432971104121889314926215995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288647402747926209950810663 432971104121889314926215995)
    ·
      refine ⟨649456656182833972389323993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432971104121889314926215995 649456656182833972389323993)
      ·
        refine ⟨487092492137125479291992995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649456656182833972389323993 487092492137125479291992995)
        ·
          refine ⟨730638738205688218937989493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487092492137125479291992995 730638738205688218937989493)
          ·
            refine ⟨68497381706783270525436515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 730638738205688218937989493 68497381706783270525436515)
            ·
              refine ⟨102746072560174905788154773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68497381706783270525436515 102746072560174905788154773)
              ·
                refine ⟨4816222151258198708819755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102746072560174905788154773 4816222151258198708819755)
                ·
                  refine ⟨7224333226887298063229633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816222151258198708819755 7224333226887298063229633)
                  ·
                    refine ⟨5418249920165473547422225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224333226887298063229633 5418249920165473547422225)
                    ·
                      refine ⟨4063687440124105160566669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418249920165473547422225 4063687440124105160566669)
                      ·
                        rfl

theorem cell23_7914003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 1, 2, 2].length) (baseStart_7914003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914003 prefixEnd_7914003 := by exact prefixLift 7914003
  have htrace : WordTrace (prefixWord ++ tailWord_7914003) baseStart_7914003 baseEnd_7914003 := by
    simpa [prefixWord, tailWord_7914003, baseEnd_7914003] using wordTrace_append hprefix tailTrace_7914003
  have hstable : (prefixWord ++ tailWord_7914003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914003).length < 2 ^ (prefixWord ++ tailWord_7914003).sum := by decide
  have hdescent : baseEnd_7914003 < baseStart_7914003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914013 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7914013 : Nat := 118140960795 + 7914013 * 2 ^ 59
def prefixEnd_7914013 : Nat := 4983230072969 + 3 ^ 40 * 7914013 * 2
def baseEnd_7914013 : Nat := 1354564191643550040480541

theorem tailTrace_7914013 : CollatzResearch.WordTrace tailWord_7914013 prefixEnd_7914013 1354564191643550040480541 := by
  unfold tailWord_7914013
  simp only [CollatzResearch.WordTrace]
  refine ⟨288647767477889981658674693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192431844985259987772449795 288647767477889981658674693)
  ·
    refine ⟨54121456402104371561001505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288647767477889981658674693 54121456402104371561001505)
    ·
      refine ⟨40591092301578278670751129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54121456402104371561001505 40591092301578278670751129)
      ·
        refine ⟨30443319226183709003063347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40591092301578278670751129 30443319226183709003063347)
        ·
          refine ⟨45664978839275563504595021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443319226183709003063347 45664978839275563504595021)
          ·
            refine ⟨17124367064728336314223133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45664978839275563504595021 17124367064728336314223133)
            ·
              refine ⟨6421637649273126117833675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17124367064728336314223133 6421637649273126117833675)
              ·
                refine ⟨9632456473909689176750513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421637649273126117833675 9632456473909689176750513)
                ·
                  refine ⟨7224342355432266882562885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632456473909689176750513 7224342355432266882562885)
                  ·
                    refine ⟨1354564191643550040480541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224342355432266882562885 1354564191643550040480541)
                    ·
                      rfl

theorem cell23_7914013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7914013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914013 prefixEnd_7914013 := by exact prefixLift 7914013
  have htrace : WordTrace (prefixWord ++ tailWord_7914013) baseStart_7914013 baseEnd_7914013 := by
    simpa [prefixWord, tailWord_7914013, baseEnd_7914013] using wordTrace_append hprefix tailTrace_7914013
  have hstable : (prefixWord ++ tailWord_7914013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914013).length < 2 ^ (prefixWord ++ tailWord_7914013).sum := by decide
  have hdescent : baseEnd_7914013 < baseStart_7914013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914026 : List Nat := [3, 1, 4, 1, 1, 4, 2, 7]
def baseStart_7914026 : Nat := 118140960795 + 7914026 * 2 ^ 59
def prefixEnd_7914026 : Nat := 4983230072969 + 3 ^ 40 * 7914026 * 2
def baseEnd_7914026 : Nat := 150507379636265132243669

theorem tailTrace_7914026 : CollatzResearch.WordTrace tailWord_7914026 prefixEnd_7914026 150507379636265132243669 := by
  unfold tailWord_7914026
  simp only [CollatzResearch.WordTrace]
  refine ⟨72162060406710721219724483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192432161084561923252598621 72162060406710721219724483)
  ·
    refine ⟨108243090610066081829586725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72162060406710721219724483 108243090610066081829586725)
    ·
      refine ⟨20295579489387390343047511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108243090610066081829586725 20295579489387390343047511)
      ·
        refine ⟨30443369234081085514571267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20295579489387390343047511 30443369234081085514571267)
        ·
          refine ⟨45665053851121628271856901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443369234081085514571267 45665053851121628271856901)
          ·
            refine ⟨8562197597085305300973169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45665053851121628271856901 8562197597085305300973169)
            ·
              refine ⟨6421648197813978975729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562197597085305300973169 6421648197813978975729877)
              ·
                refine ⟨150507379636265132243669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6421648197813978975729877 150507379636265132243669)
                ·
                  rfl

theorem cell23_7914026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_7914026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914026 prefixEnd_7914026 := by exact prefixLift 7914026
  have htrace : WordTrace (prefixWord ++ tailWord_7914026) baseStart_7914026 baseEnd_7914026 := by
    simpa [prefixWord, tailWord_7914026, baseEnd_7914026] using wordTrace_append hprefix tailTrace_7914026
  have hstable : (prefixWord ++ tailWord_7914026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914026).length < 2 ^ (prefixWord ++ tailWord_7914026).sum := by decide
  have hdescent : baseEnd_7914026 < baseStart_7914026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914032 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_7914032 : Nat := 118140960795 + 7914032 * 2 ^ 59
def prefixEnd_7914032 : Nat := 4983230072969 + 3 ^ 40 * 7914032 * 2
def baseEnd_7914032 : Nat := 4063702331063085547104035

theorem tailTrace_7914032 : CollatzResearch.WordTrace tailWord_7914032 prefixEnd_7914032 4063702331063085547104035 := by
  unfold tailWord_7914032
  simp only [CollatzResearch.WordTrace]
  refine ⟨144324230232410573951808175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192432306976547431935744233 144324230232410573951808175)
  ·
    refine ⟨216486345348615860927712263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144324230232410573951808175 216486345348615860927712263)
    ·
      refine ⟨324729518022923791391568395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216486345348615860927712263 324729518022923791391568395)
      ·
        refine ⟨487094277034385687087352593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324729518022923791391568395 487094277034385687087352593)
        ·
          refine ⟨365320707775789265315514445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487094277034385687087352593 365320707775789265315514445)
          ·
            refine ⟨136995265415920974493317917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365320707775789265315514445 136995265415920974493317917)
            ·
              refine ⟨51373224530970365434994219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136995265415920974493317917 51373224530970365434994219)
              ·
                refine ⟨77059836796455548152491329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51373224530970365434994219 77059836796455548152491329)
                ·
                  refine ⟨57794877597341661114368497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77059836796455548152491329 57794877597341661114368497)
                  ·
                    refine ⟨43346158198006245835776373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57794877597341661114368497 43346158198006245835776373)
                    ·
                      refine ⟨4063702331063085547104035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43346158198006245835776373 4063702331063085547104035)
                      ·
                        rfl

theorem cell23_7914032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_7914032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914032 prefixEnd_7914032 := by exact prefixLift 7914032
  have htrace : WordTrace (prefixWord ++ tailWord_7914032) baseStart_7914032 baseEnd_7914032 := by
    simpa [prefixWord, tailWord_7914032, baseEnd_7914032] using wordTrace_append hprefix tailTrace_7914032
  have hstable : (prefixWord ++ tailWord_7914032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914032).length < 2 ^ (prefixWord ++ tailWord_7914032).sum := by decide
  have hdescent : baseEnd_7914032 < baseStart_7914032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914093 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_7914093 : Nat := 118140960795 + 7914093 * 2 ^ 59
def prefixEnd_7914093 : Nat := 4983230072969 + 3 ^ 40 * 7914093 * 2
def baseEnd_7914093 : Nat := 4063733653383009808441255

theorem tailTrace_7914093 : CollatzResearch.WordTrace tailWord_7914093 prefixEnd_7914093 4063733653383009808441255 := by
  unfold tailWord_7914093
  simp only [CollatzResearch.WordTrace]
  refine ⟨288650685317600155321586933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192433790211733436881057955 288650685317600155321586933)
  ·
    refine ⟨27061001748525014561398775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288650685317600155321586933 27061001748525014561398775)
    ·
      refine ⟨40591502622787521842098163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061001748525014561398775 40591502622787521842098163)
      ·
        refine ⟨60887253934181282763147245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40591502622787521842098163 60887253934181282763147245)
        ·
          refine ⟨22832720225317981036180217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60887253934181282763147245 22832720225317981036180217)
          ·
            refine ⟨17124540168988485777135163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22832720225317981036180217 17124540168988485777135163)
            ·
              refine ⟨25686810253482728665702745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17124540168988485777135163 25686810253482728665702745)
              ·
                refine ⟨19265107690112046499277059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25686810253482728665702745 19265107690112046499277059)
                ·
                  refine ⟨28897661535168069748915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19265107690112046499277059 28897661535168069748915589)
                  ·
                    refine ⟨5418311537844013077921673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28897661535168069748915589 5418311537844013077921673)
                    ·
                      refine ⟨4063733653383009808441255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418311537844013077921673 4063733653383009808441255)
                      ·
                        rfl

theorem cell23_7914093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_7914093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914093 prefixEnd_7914093 := by exact prefixLift 7914093
  have htrace : WordTrace (prefixWord ++ tailWord_7914093) baseStart_7914093 baseEnd_7914093 := by
    simpa [prefixWord, tailWord_7914093, baseEnd_7914093] using wordTrace_append hprefix tailTrace_7914093
  have hstable : (prefixWord ++ tailWord_7914093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914093).length < 2 ^ (prefixWord ++ tailWord_7914093).sum := by decide
  have hdescent : baseEnd_7914093 < baseStart_7914093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914126 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7914126 : Nat := 118140960795 + 7914126 * 2 ^ 59
def prefixEnd_7914126 : Nat := 4983230072969 + 3 ^ 40 * 7914126 * 2
def baseEnd_7914126 : Nat := 4063750598244608179328603

theorem tailTrace_7914126 : CollatzResearch.WordTrace tailWord_7914126 prefixEnd_7914126 4063750598244608179328603 := by
  unfold tailWord_7914126
  simp only [CollatzResearch.WordTrace]
  refine ⟨36081486115810075244692279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192434592617653734638358821 36081486115810075244692279)
  ·
    refine ⟨54122229173715112867038419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36081486115810075244692279 54122229173715112867038419)
    ·
      refine ⟨81183343760572669300557629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54122229173715112867038419 81183343760572669300557629)
      ·
        refine ⟨30443753910214750987709111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81183343760572669300557629 30443753910214750987709111)
        ·
          refine ⟨45665630865322126481563667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443753910214750987709111 45665630865322126481563667)
          ·
            refine ⟨68498446297983189722345501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45665630865322126481563667 68498446297983189722345501)
            ·
              refine ⟨25686917361743696145879563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68498446297983189722345501 25686917361743696145879563)
              ·
                refine ⟨38530376042615544218819345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25686917361743696145879563 38530376042615544218819345)
                ·
                  refine ⟨28897782031961658164114509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38530376042615544218819345 28897782031961658164114509)
                  ·
                    refine ⟨10836668261985621811542941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28897782031961658164114509 10836668261985621811542941)
                    ·
                      refine ⟨4063750598244608179328603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836668261985621811542941 4063750598244608179328603)
                      ·
                        rfl

theorem cell23_7914126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7914126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914126 prefixEnd_7914126 := by exact prefixLift 7914126
  have htrace : WordTrace (prefixWord ++ tailWord_7914126) baseStart_7914126 baseEnd_7914126 := by
    simpa [prefixWord, tailWord_7914126, baseEnd_7914126] using wordTrace_append hprefix tailTrace_7914126
  have hstable : (prefixWord ++ tailWord_7914126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914126).length < 2 ^ (prefixWord ++ tailWord_7914126).sum := by decide
  have hdescent : baseEnd_7914126 < baseStart_7914126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914136 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7914136 : Nat := 118140960795 + 7914136 * 2 ^ 59
def prefixEnd_7914136 : Nat := 4983230072969 + 3 ^ 40 * 7914136 * 2
def baseEnd_7914136 : Nat := 4063755733051153140203557

theorem tailTrace_7914136 : CollatzResearch.WordTrace tailWord_7914136 prefixEnd_7914136 4063755733051153140203557 := by
  unfold tailWord_7914136
  simp only [CollatzResearch.WordTrace]
  refine ⟨144326126828222186832701131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192434835770962915776934841 144326126828222186832701131)
  ·
    refine ⟨216489190242333280249051697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144326126828222186832701131 216489190242333280249051697)
    ·
      refine ⟨162366892681749960186788773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216489190242333280249051697 162366892681749960186788773)
      ·
        refine ⟨30443792377828117535022895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162366892681749960186788773 30443792377828117535022895)
        ·
          refine ⟨45665688566742176302534343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30443792377828117535022895 45665688566742176302534343)
          ·
            refine ⟨68498532850113264453801515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45665688566742176302534343 68498532850113264453801515)
            ·
              refine ⟨102747799275169896680702273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68498532850113264453801515 102747799275169896680702273)
              ·
                refine ⟨77060849456377422510526705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102747799275169896680702273 77060849456377422510526705)
                ·
                  refine ⟨57795637092283066882895029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77060849456377422510526705 57795637092283066882895029)
                  ·
                    refine ⟨5418340977401537520271409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57795637092283066882895029 5418340977401537520271409)
                    ·
                      refine ⟨4063755733051153140203557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418340977401537520271409 4063755733051153140203557)
                      ·
                        rfl

theorem cell23_7914136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7914136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914136 prefixEnd_7914136 := by exact prefixLift 7914136
  have htrace : WordTrace (prefixWord ++ tailWord_7914136) baseStart_7914136 baseEnd_7914136 := by
    simpa [prefixWord, tailWord_7914136, baseEnd_7914136] using wordTrace_append hprefix tailTrace_7914136
  have hstable : (prefixWord ++ tailWord_7914136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914136).length < 2 ^ (prefixWord ++ tailWord_7914136).sum := by decide
  have hdescent : baseEnd_7914136 < baseStart_7914136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914176 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_7914176 : Nat := 118140960795 + 7914176 * 2 ^ 59
def prefixEnd_7914176 : Nat := 4983230072969 + 3 ^ 40 * 7914176 * 2
def baseEnd_7914176 : Nat := 1354592090759110994567791

theorem tailTrace_7914176 : CollatzResearch.WordTrace tailWord_7914176 prefixEnd_7914176 1354592090759110994567791 := by
  unfold tailWord_7914176
  simp only [CollatzResearch.WordTrace]
  refine ⟨144326856288149730248429191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192435808384199640331238921 144326856288149730248429191)
  ·
    refine ⟨216490284432224595372643787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144326856288149730248429191 216490284432224595372643787)
    ·
      refine ⟨324735426648336893058965681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216490284432224595372643787 324735426648336893058965681)
      ·
        refine ⟨243551569986252669794224261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324735426648336893058965681 243551569986252669794224261)
        ·
          refine ⟨45665919372422375586417049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243551569986252669794224261 45665919372422375586417049)
          ·
            refine ⟨34249439529316781689812787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45665919372422375586417049 34249439529316781689812787)
            ·
              refine ⟨51374159293975172534719181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34249439529316781689812787 51374159293975172534719181)
              ·
                refine ⟨19265309735240689700519693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51374159293975172534719181 19265309735240689700519693)
                ·
                  refine ⟨7224491150715258637694885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19265309735240689700519693 7224491150715258637694885)
                  ·
                    refine ⟨1354592090759110994567791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224491150715258637694885 1354592090759110994567791)
                    ·
                      rfl

theorem cell23_7914176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_7914176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914176 prefixEnd_7914176 := by exact prefixLift 7914176
  have htrace : WordTrace (prefixWord ++ tailWord_7914176) baseStart_7914176 baseEnd_7914176 := by
    simpa [prefixWord, tailWord_7914176, baseEnd_7914176] using wordTrace_append hprefix tailTrace_7914176
  have hstable : (prefixWord ++ tailWord_7914176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914176).length < 2 ^ (prefixWord ++ tailWord_7914176).sum := by decide
  have hdescent : baseEnd_7914176 < baseStart_7914176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914186 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_7914186 : Nat := 118140960795 + 7914186 * 2 ^ 59
def prefixEnd_7914186 : Nat := 4983230072969 + 3 ^ 40 * 7914186 * 2
def baseEnd_7914186 : Nat := 4063781407083877944578327

theorem tailTrace_7914186 : CollatzResearch.WordTrace tailWord_7914186 prefixEnd_7914186 4063781407083877944578327 := by
  unfold tailWord_7914186
  simp only [CollatzResearch.WordTrace]
  refine ⟨72163519326565808051180603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192436051537508821469814941 72163519326565808051180603)
  ·
    refine ⟨108245278989848712076770905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72163519326565808051180603 108245278989848712076770905)
    ·
      refine ⟨81183959242386534057578179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108245278989848712076770905 81183959242386534057578179)
      ·
        refine ⟨121775938863579801086367269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81183959242386534057578179 121775938863579801086367269)
        ·
          refine ⟨22832988536921212703693863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121775938863579801086367269 22832988536921212703693863)
          ·
            refine ⟨34249482805381819055540795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832988536921212703693863 34249482805381819055540795)
            ·
              refine ⟨51374224208072728583311193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34249482805381819055540795 51374224208072728583311193)
              ·
                refine ⟨38530668156054546437483395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51374224208072728583311193 38530668156054546437483395)
                ·
                  refine ⟨57796002234081819656225093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38530668156054546437483395 57796002234081819656225093)
                  ·
                    refine ⟨10836750418890341185542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57796002234081819656225093 10836750418890341185542205)
                    ·
                      refine ⟨4063781407083877944578327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836750418890341185542205 4063781407083877944578327)
                      ·
                        rfl

theorem cell23_7914186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_7914186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914186 prefixEnd_7914186 := by exact prefixLift 7914186
  have htrace : WordTrace (prefixWord ++ tailWord_7914186) baseStart_7914186 baseEnd_7914186 := by
    simpa [prefixWord, tailWord_7914186, baseEnd_7914186] using wordTrace_append hprefix tailTrace_7914186
  have hstable : (prefixWord ++ tailWord_7914186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914186).length < 2 ^ (prefixWord ++ tailWord_7914186).sum := by decide
  have hdescent : baseEnd_7914186 < baseStart_7914186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914219 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 5, 5]
def baseStart_7914219 : Nat := 118140960795 + 7914219 * 2 ^ 59
def prefixEnd_7914219 : Nat := 4983230072969 + 3 ^ 40 * 7914219 * 2
def baseEnd_7914219 : Nat := 1354599450648492105155225

theorem tailTrace_7914219 : CollatzResearch.WordTrace tailWord_7914219 prefixEnd_7914219 1354599450648492105155225 := by
  unfold tailWord_7914219
  simp only [CollatzResearch.WordTrace]
  refine ⟨288655280915143678840673711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192436853943429119227115807 288655280915143678840673711)
  ·
    refine ⟨432982921372715518261010567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288655280915143678840673711 432982921372715518261010567)
    ·
      refine ⟨649474382059073277391515851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432982921372715518261010567 649474382059073277391515851)
      ·
        refine ⟨974211573088609916087273777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649474382059073277391515851 974211573088609916087273777)
        ·
          refine ⟨730658679816457437065455333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974211573088609916087273777 730658679816457437065455333)
          ·
            refine ⟨136998502465585769449772875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730658679816457437065455333 136998502465585769449772875)
            ·
              refine ⟨205497753698378654174659313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136998502465585769449772875 205497753698378654174659313)
              ·
                refine ⟨154123315273783990630994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205497753698378654174659313 154123315273783990630994485)
                ·
                  refine ⟨14449060806917249121655733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154123315273783990630994485 14449060806917249121655733)
                  ·
                    refine ⟨1354599450648492105155225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14449060806917249121655733 1354599450648492105155225)
                    ·
                      rfl

theorem cell23_7914219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 5].length) (baseStart_7914219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914219 prefixEnd_7914219 := by exact prefixLift 7914219
  have htrace : WordTrace (prefixWord ++ tailWord_7914219) baseStart_7914219 baseEnd_7914219 := by
    simpa [prefixWord, tailWord_7914219, baseEnd_7914219] using wordTrace_append hprefix tailTrace_7914219
  have hstable : (prefixWord ++ tailWord_7914219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914219).length < 2 ^ (prefixWord ++ tailWord_7914219).sum := by decide
  have hdescent : baseEnd_7914219 < baseStart_7914219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914239 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_7914239 : Nat := 118140960795 + 7914239 * 2 ^ 59
def prefixEnd_7914239 : Nat := 4983230072969 + 3 ^ 40 * 7914239 * 2
def baseEnd_7914239 : Nat := 4063808621558566237215583

theorem tailTrace_7914239 : CollatzResearch.WordTrace tailWord_7914239 prefixEnd_7914239 4063808621558566237215583 := by
  unfold tailWord_7914239
  simp only [CollatzResearch.WordTrace]
  refine ⟨288656010375071222256401771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192437340250047481504267847 288656010375071222256401771)
  ·
    refine ⟨432984015562606833384602657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288656010375071222256401771 432984015562606833384602657)
    ·
      refine ⟨324738011671955125038451993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432984015562606833384602657 324738011671955125038451993)
      ·
        refine ⟨243553508753966343778838995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324738011671955125038451993 243553508753966343778838995)
        ·
          refine ⟨365330263130949515668258493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243553508753966343778838995 365330263130949515668258493)
          ·
            refine ⟨136998848674106068375596935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365330263130949515668258493 136998848674106068375596935)
            ·
              refine ⟨205498273011159102563395403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136998848674106068375596935 205498273011159102563395403)
              ·
                refine ⟨308247409516738653845093105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205498273011159102563395403 308247409516738653845093105)
                ·
                  refine ⟨231185557137553990383819829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308247409516738653845093105 231185557137553990383819829)
                  ·
                    refine ⟨21673645981645686598483109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231185557137553990383819829 21673645981645686598483109)
                    ·
                      refine ⟨4063808621558566237215583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21673645981645686598483109 4063808621558566237215583)
                      ·
                        rfl

theorem cell23_7914239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_7914239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914239 prefixEnd_7914239 := by exact prefixLift 7914239
  have htrace : WordTrace (prefixWord ++ tailWord_7914239) baseStart_7914239 baseEnd_7914239 := by
    simpa [prefixWord, tailWord_7914239, baseEnd_7914239] using wordTrace_append hprefix tailTrace_7914239
  have hstable : (prefixWord ++ tailWord_7914239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914239).length < 2 ^ (prefixWord ++ tailWord_7914239).sum := by decide
  have hdescent : baseEnd_7914239 < baseStart_7914239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914266 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_7914266 : Nat := 118140960795 + 7914266 * 2 ^ 59
def prefixEnd_7914266 : Nat := 4983230072969 + 3 ^ 40 * 7914266 * 2
def baseEnd_7914266 : Nat := 1354607495178745877192653

theorem tailTrace_7914266 : CollatzResearch.WordTrace tailWord_7914266 prefixEnd_7914266 1354607495178745877192653 := by
  unfold tailWord_7914266
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164248786493351466908663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192437996763982270578423101 72164248786493351466908663)
  ·
    refine ⟨108246373179740027200362995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72164248786493351466908663 108246373179740027200362995)
    ·
      refine ⟨162369559769610040800544493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108246373179740027200362995 162369559769610040800544493)
      ·
        refine ⟨60888584913603765300204185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162369559769610040800544493 60888584913603765300204185)
        ·
          refine ⟨45666438685202823975153139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60888584913603765300204185 45666438685202823975153139)
          ·
            refine ⟨68499658027804235962729709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45666438685202823975153139 68499658027804235962729709)
            ·
              refine ⟨25687371760426588486023641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68499658027804235962729709 25687371760426588486023641)
              ·
                refine ⟨19265528820319941364517731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25687371760426588486023641 19265528820319941364517731)
                ·
                  refine ⟨28898293230479912046776597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19265528820319941364517731 28898293230479912046776597)
                  ·
                    refine ⟨1354607495178745877192653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28898293230479912046776597 1354607495178745877192653)
                    ·
                      rfl

theorem cell23_7914266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_7914266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914266 prefixEnd_7914266 := by exact prefixLift 7914266
  have htrace : WordTrace (prefixWord ++ tailWord_7914266) baseStart_7914266 baseEnd_7914266 := by
    simpa [prefixWord, tailWord_7914266, baseEnd_7914266] using wordTrace_append hprefix tailTrace_7914266
  have hstable : (prefixWord ++ tailWord_7914266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914266).length < 2 ^ (prefixWord ++ tailWord_7914266).sum := by decide
  have hdescent : baseEnd_7914266 < baseStart_7914266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914290 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_7914290 : Nat := 118140960795 + 7914290 * 2 ^ 59
def prefixEnd_7914290 : Nat := 4983230072969 + 3 ^ 40 * 7914290 * 2
def baseEnd_7914290 : Nat := 4063834809071945537677849

theorem tailTrace_7914290 : CollatzResearch.WordTrace tailWord_7914290 prefixEnd_7914290 4063834809071945537677849 := by
  unfold tailWord_7914290
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164467624471614491627081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192438580331924305311005549 72164467624471614491627081)
  ·
    refine ⟨54123350718353710868720311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72164467624471614491627081 54123350718353710868720311)
    ·
      refine ⟨81185026077530566303080467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54123350718353710868720311 81185026077530566303080467)
      ·
        refine ⟨121777539116295849454620701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81185026077530566303080467 121777539116295849454620701)
        ·
          refine ⟨45666577168610943545482763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121777539116295849454620701 45666577168610943545482763)
          ·
            refine ⟨68499865752916415318224145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45666577168610943545482763 68499865752916415318224145)
            ·
              refine ⟨51374899314687311488668109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68499865752916415318224145 51374899314687311488668109)
              ·
                refine ⟨19265587243007741808250541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51374899314687311488668109 19265587243007741808250541)
                ·
                  refine ⟨7224595216127903178093953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19265587243007741808250541 7224595216127903178093953)
                  ·
                    refine ⟨5418446412095927383570465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224595216127903178093953 5418446412095927383570465)
                    ·
                      refine ⟨4063834809071945537677849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418446412095927383570465 4063834809071945537677849)
                      ·
                        rfl

theorem cell23_7914290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_7914290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914290 prefixEnd_7914290 := by exact prefixLift 7914290
  have htrace : WordTrace (prefixWord ++ tailWord_7914290) baseStart_7914290 baseEnd_7914290 := by
    simpa [prefixWord, tailWord_7914290, baseEnd_7914290] using wordTrace_append hprefix tailTrace_7914290
  have hstable : (prefixWord ++ tailWord_7914290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914290).length < 2 ^ (prefixWord ++ tailWord_7914290).sum := by decide
  have hdescent : baseEnd_7914290 < baseStart_7914290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914293 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_7914293 : Nat := 118140960795 + 7914293 * 2 ^ 59
def prefixEnd_7914293 : Nat := 4983230072969 + 3 ^ 40 * 7914293 * 2
def baseEnd_7914293 : Nat := 4063836349513909025940335

theorem tailTrace_7914293 : CollatzResearch.WordTrace tailWord_7914293 prefixEnd_7914293 4063836349513909025940335 := by
  unfold tailWord_7914293
  simp only [CollatzResearch.WordTrace]
  refine ⟨288657979916875589478867533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192438653277917059652578355 288657979916875589478867533)
  ·
    refine ⟨108246742468828346054575325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288657979916875589478867533 108246742468828346054575325)
    ·
      refine ⟨40592528425810629770465747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108246742468828346054575325 40592528425810629770465747)
      ·
        refine ⟨60888792638715944655698621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40592528425810629770465747 60888792638715944655698621)
        ·
          refine ⟨22833297239518479245886983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60888792638715944655698621 22833297239518479245886983)
          ·
            refine ⟨34249945859277718868830475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833297239518479245886983 34249945859277718868830475)
            ·
              refine ⟨51374918788916578303245713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34249945859277718868830475 51374918788916578303245713)
              ·
                refine ⟨38531189091687433727434285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51374918788916578303245713 38531189091687433727434285)
                ·
                  refine ⟨14449195909382787647787857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38531189091687433727434285 14449195909382787647787857)
                  ·
                    refine ⟨10836896932037090735840893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14449195909382787647787857 10836896932037090735840893)
                    ·
                      refine ⟨4063836349513909025940335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836896932037090735840893 4063836349513909025940335)
                      ·
                        rfl

theorem cell23_7914293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_7914293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914293 prefixEnd_7914293 := by exact prefixLift 7914293
  have htrace : WordTrace (prefixWord ++ tailWord_7914293) baseStart_7914293 baseEnd_7914293 := by
    simpa [prefixWord, tailWord_7914293, baseEnd_7914293] using wordTrace_append hprefix tailTrace_7914293
  have hstable : (prefixWord ++ tailWord_7914293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914293).length < 2 ^ (prefixWord ++ tailWord_7914293).sum := by decide
  have hdescent : baseEnd_7914293 < baseStart_7914293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914303 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_7914303 : Nat := 118140960795 + 7914303 * 2 ^ 59
def prefixEnd_7914303 : Nat := 4983230072969 + 3 ^ 40 * 7914303 * 2
def baseEnd_7914303 : Nat := 4063841484320453986815289

theorem tailTrace_7914303 : CollatzResearch.WordTrace tailWord_7914303 prefixEnd_7914303 4063841484320453986815289 := by
  unfold tailWord_7914303
  simp only [CollatzResearch.WordTrace]
  refine ⟨288658344646839361186731563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192438896431226240791154375 288658344646839361186731563)
  ·
    refine ⟨432987516970259041780097345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288658344646839361186731563 432987516970259041780097345)
    ·
      refine ⟨324740637727694281335073009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432987516970259041780097345 324740637727694281335073009)
      ·
        refine ⟨243555478295770711001304757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324740637727694281335073009 243555478295770711001304757)
        ·
          refine ⟨22833326090228504156372321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243555478295770711001304757 22833326090228504156372321)
          ·
            refine ⟨17124994567671378117279241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22833326090228504156372321 17124994567671378117279241)
            ·
              refine ⟨12843745925753533587959431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17124994567671378117279241 12843745925753533587959431)
              ·
                refine ⟨19265618888630300381939147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12843745925753533587959431 19265618888630300381939147)
                ·
                  refine ⟨28898428332945450572908721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19265618888630300381939147 28898428332945450572908721)
                  ·
                    refine ⟨21673821249709087929681541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28898428332945450572908721 21673821249709087929681541)
                    ·
                      refine ⟨4063841484320453986815289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21673821249709087929681541 4063841484320453986815289)
                      ·
                        rfl

theorem cell23_7914303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_7914303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914303 prefixEnd_7914303 := by exact prefixLift 7914303
  have htrace : WordTrace (prefixWord ++ tailWord_7914303) baseStart_7914303 baseEnd_7914303 := by
    simpa [prefixWord, tailWord_7914303, baseEnd_7914303] using wordTrace_append hprefix tailTrace_7914303
  have hstable : (prefixWord ++ tailWord_7914303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914303).length < 2 ^ (prefixWord ++ tailWord_7914303).sum := by decide
  have hdescent : baseEnd_7914303 < baseStart_7914303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914324 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_7914324 : Nat := 118140960795 + 7914324 * 2 ^ 59
def prefixEnd_7914324 : Nat := 4983230072969 + 3 ^ 40 * 7914324 * 2
def baseEnd_7914324 : Nat := 4063852267414198404652693

theorem tailTrace_7914324 : CollatzResearch.WordTrace tailWord_7914324 prefixEnd_7914324 4063852267414198404652693 := by
  unfold tailWord_7914324
  simp only [CollatzResearch.WordTrace]
  refine ⟨144329555289881640886623013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192439407053175521182164017 144329555289881640886623013)
  ·
    refine ⟨27061791616852807666241815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144329555289881640886623013 27061791616852807666241815)
    ·
      refine ⟨40592687425279211499362723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061791616852807666241815 40592687425279211499362723)
      ·
        refine ⟨60889031137918817249044085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40592687425279211499362723 60889031137918817249044085)
        ·
          refine ⟨5708346669179889117097883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60889031137918817249044085 5708346669179889117097883)
          ·
            refine ⟨8562520003769833675646825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708346669179889117097883 8562520003769833675646825)
            ·
              refine ⟨6421890002827375256735119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562520003769833675646825 6421890002827375256735119)
              ·
                refine ⟨9632835004241062885102679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421890002827375256735119 9632835004241062885102679)
                ·
                  refine ⟨14449252506361594327654019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632835004241062885102679 14449252506361594327654019)
                  ·
                    refine ⟨21673878759542391491481029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449252506361594327654019 21673878759542391491481029)
                    ·
                      refine ⟨4063852267414198404652693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21673878759542391491481029 4063852267414198404652693)
                      ·
                        rfl

theorem cell23_7914324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_7914324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914324 prefixEnd_7914324 := by exact prefixLift 7914324
  have htrace : WordTrace (prefixWord ++ tailWord_7914324) baseStart_7914324 baseEnd_7914324 := by
    simpa [prefixWord, tailWord_7914324, baseEnd_7914324] using wordTrace_append hprefix tailTrace_7914324
  have hstable : (prefixWord ++ tailWord_7914324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914324).length < 2 ^ (prefixWord ++ tailWord_7914324).sum := by decide
  have hdescent : baseEnd_7914324 < baseStart_7914324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914327 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_7914327 : Nat := 118140960795 + 7914327 * 2 ^ 59
def prefixEnd_7914327 : Nat := 4983230072969 + 3 ^ 40 * 7914327 * 2
def baseEnd_7914327 : Nat := 4063853807856161892915179

theorem tailTrace_7914327 : CollatzResearch.WordTrace tailWord_7914327 prefixEnd_7914327 4063853807856161892915179 := by
  unfold tailWord_7914327
  simp only [CollatzResearch.WordTrace]
  refine ⟨288659219998752413285605235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192439479999168275523736823 288659219998752413285605235)
  ·
    refine ⟨432988829998128619928407853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288659219998752413285605235 432988829998128619928407853)
    ·
      refine ⟨162370811249298232473152945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432988829998128619928407853 162370811249298232473152945)
      ·
        refine ⟨121778108436973674354864709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162370811249298232473152945 121778108436973674354864709)
        ·
          refine ⟨22833395331932563941537133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121778108436973674354864709 22833395331932563941537133)
          ·
            refine ⟨8562523249474711478076425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22833395331932563941537133 8562523249474711478076425)
            ·
              refine ⟨6421892437106033608557319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562523249474711478076425 6421892437106033608557319)
              ·
                refine ⟨9632838655659050412835979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421892437106033608557319 9632838655659050412835979)
                ·
                  refine ⟨14449257983488575619253969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632838655659050412835979 14449257983488575619253969)
                  ·
                    refine ⟨10836943487616431714440477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14449257983488575619253969 10836943487616431714440477)
                    ·
                      refine ⟨4063853807856161892915179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836943487616431714440477 4063853807856161892915179)
                      ·
                        rfl

theorem cell23_7914327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_7914327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914327 prefixEnd_7914327 := by exact prefixLift 7914327
  have htrace : WordTrace (prefixWord ++ tailWord_7914327) baseStart_7914327 baseEnd_7914327 := by
    simpa [prefixWord, tailWord_7914327, baseEnd_7914327] using wordTrace_append hprefix tailTrace_7914327
  have hstable : (prefixWord ++ tailWord_7914327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914327).length < 2 ^ (prefixWord ++ tailWord_7914327).sum := by decide
  have hdescent : baseEnd_7914327 < baseStart_7914327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914340 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_7914340 : Nat := 118140960795 + 7914340 * 2 ^ 59
def prefixEnd_7914340 : Nat := 4983230072969 + 3 ^ 40 * 7914340 * 2
def baseEnd_7914340 : Nat := 4063860483104670342052619

theorem tailTrace_7914340 : CollatzResearch.WordTrace tailWord_7914340 prefixEnd_7914340 4063860483104670342052619 := by
  unfold tailWord_7914340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144329847073852658252914237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192439796098470211003885649 144329847073852658252914237)
  ·
    refine ⟨54123692652694746844842839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144329847073852658252914237 54123692652694746844842839)
    ·
      refine ⟨81185538979042120267264259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54123692652694746844842839 81185538979042120267264259)
      ·
        refine ⟨121778308468563180400896389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81185538979042120267264259 121778308468563180400896389)
        ·
          refine ⟨22833432837855596325168073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121778308468563180400896389 22833432837855596325168073)
          ·
            refine ⟨17125074628391697243876055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22833432837855596325168073 17125074628391697243876055)
            ·
              refine ⟨25687611942587545865814083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17125074628391697243876055 25687611942587545865814083)
              ·
                refine ⟨38531417913881318798721125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25687611942587545865814083 38531417913881318798721125)
                ·
                  refine ⟨7224640858852747274760211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38531417913881318798721125 7224640858852747274760211)
                  ·
                    refine ⟨10836961288279120912140317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224640858852747274760211 10836961288279120912140317)
                    ·
                      refine ⟨4063860483104670342052619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10836961288279120912140317 4063860483104670342052619)
                      ·
                        rfl

theorem cell23_7914340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_7914340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914340 prefixEnd_7914340 := by exact prefixLift 7914340
  have htrace : WordTrace (prefixWord ++ tailWord_7914340) baseStart_7914340 baseEnd_7914340 := by
    simpa [prefixWord, tailWord_7914340, baseEnd_7914340] using wordTrace_append hprefix tailTrace_7914340
  have hstable : (prefixWord ++ tailWord_7914340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914340).length < 2 ^ (prefixWord ++ tailWord_7914340).sum := by decide
  have hdescent : baseEnd_7914340 < baseStart_7914340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914380 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_7914380 : Nat := 118140960795 + 7914380 * 2 ^ 59
def prefixEnd_7914380 : Nat := 4983230072969 + 3 ^ 40 * 7914380 * 2
def baseEnd_7914380 : Nat := 4063881022330850185552435

theorem tailTrace_7914380 : CollatzResearch.WordTrace tailWord_7914380 prefixEnd_7914380 4063881022330850185552435 := by
  unfold tailWord_7914380
  simp only [CollatzResearch.WordTrace]
  refine ⟨144330576533780201668642297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192440768711706935558189729 144330576533780201668642297)
  ·
    refine ⟨108247932400335151251481723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144330576533780201668642297 108247932400335151251481723)
    ·
      refine ⟨162371898600502726877222585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108247932400335151251481723 162371898600502726877222585)
      ·
        refine ⟨121778923950377045157916939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162371898600502726877222585 121778923950377045157916939)
        ·
          refine ⟨182668385925565567736875409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121778923950377045157916939 182668385925565567736875409)
          ·
            refine ⟨137001289444174175802656557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182668385925565567736875409 137001289444174175802656557)
            ·
              refine ⟨51375483541565315925996209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137001289444174175802656557 51375483541565315925996209)
              ·
                refine ⟨38531612656173986944497157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51375483541565315925996209 38531612656173986944497157)
                ·
                  refine ⟨7224677373032622552093217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38531612656173986944497157 7224677373032622552093217)
                  ·
                    refine ⟨5418508029774466914069913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224677373032622552093217 5418508029774466914069913)
                    ·
                      refine ⟨4063881022330850185552435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418508029774466914069913 4063881022330850185552435)
                      ·
                        rfl

theorem cell23_7914380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_7914380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914380 prefixEnd_7914380 := by exact prefixLift 7914380
  have htrace : WordTrace (prefixWord ++ tailWord_7914380) baseStart_7914380 baseEnd_7914380 := by
    simpa [prefixWord, tailWord_7914380, baseEnd_7914380] using wordTrace_append hprefix tailTrace_7914380
  have hstable : (prefixWord ++ tailWord_7914380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914380).length < 2 ^ (prefixWord ++ tailWord_7914380).sum := by decide
  have hdescent : baseEnd_7914380 < baseStart_7914380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914397 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_7914397 : Nat := 118140960795 + 7914397 * 2 ^ 59
def prefixEnd_7914397 : Nat := 4983230072969 + 3 ^ 40 * 7914397 * 2
def baseEnd_7914397 : Nat := 4063889751501976619039857

theorem tailTrace_7914397 : CollatzResearch.WordTrace tailWord_7914397 prefixEnd_7914397 4063889751501976619039857 := by
  unfold tailWord_7914397
  simp only [CollatzResearch.WordTrace]
  refine ⟨288661773108498815240653445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192441182072332543493768963 288661773108498815240653445)
  ·
    refine ⟨54124082457843527857622521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288661773108498815240653445 54124082457843527857622521)
    ·
      refine ⟨40593061843382645893216891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54124082457843527857622521 40593061843382645893216891)
      ·
        refine ⟨60889592765073968839825337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40593061843382645893216891 60889592765073968839825337)
        ·
          refine ⟨45667194573805476629869003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60889592765073968839825337 45667194573805476629869003)
          ·
            refine ⟨68500791860708214944803505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45667194573805476629869003 68500791860708214944803505)
            ·
              refine ⟨51375593895531161208602629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68500791860708214944803505 51375593895531161208602629)
              ·
                refine ⟨9632923855412092726612993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51375593895531161208602629 9632923855412092726612993)
                ·
                  refine ⟨7224692891559069544959745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632923855412092726612993 7224692891559069544959745)
                  ·
                    refine ⟨5418519668669302158719809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224692891559069544959745 5418519668669302158719809)
                    ·
                      refine ⟨4063889751501976619039857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418519668669302158719809 4063889751501976619039857)
                      ·
                        rfl

theorem cell23_7914397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_7914397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914397 prefixEnd_7914397 := by exact prefixLift 7914397
  have htrace : WordTrace (prefixWord ++ tailWord_7914397) baseStart_7914397 baseEnd_7914397 := by
    simpa [prefixWord, tailWord_7914397, baseEnd_7914397] using wordTrace_append hprefix tailTrace_7914397
  have hstable : (prefixWord ++ tailWord_7914397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914397).length < 2 ^ (prefixWord ++ tailWord_7914397).sum := by decide
  have hdescent : baseEnd_7914397 < baseStart_7914397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914403 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 5]
def baseStart_7914403 : Nat := 118140960795 + 7914403 * 2 ^ 59
def prefixEnd_7914403 : Nat := 4983230072969 + 3 ^ 40 * 7914403 * 2
def baseEnd_7914403 : Nat := 451543648042878177284981

theorem tailTrace_7914403 : CollatzResearch.WordTrace tailWord_7914403 prefixEnd_7914403 451543648042878177284981 := by
  unfold tailWord_7914403
  simp only [CollatzResearch.WordTrace]
  refine ⟨288661991946477078265371863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192441327964318052176914575 288661991946477078265371863)
  ·
    refine ⟨432992987919715617398057795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288661991946477078265371863 432992987919715617398057795)
    ·
      refine ⟨649489481879573426097086693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432992987919715617398057795 649489481879573426097086693)
      ·
        refine ⟨121779277852420017393203755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649489481879573426097086693 121779277852420017393203755)
        ·
          refine ⟨182668916778630026089805633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121779277852420017393203755 182668916778630026089805633)
          ·
            refine ⟨137001687583972519567354225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182668916778630026089805633 137001687583972519567354225)
            ·
              refine ⟨102751265687979389675515669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137001687583972519567354225 102751265687979389675515669)
              ·
                refine ⟨4816465579124033891039797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102751265687979389675515669 4816465579124033891039797)
                ·
                  refine ⟨451543648042878177284981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816465579124033891039797 451543648042878177284981)
                  ·
                    rfl

theorem cell23_7914403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 5].length) (baseStart_7914403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914403 prefixEnd_7914403 := by exact prefixLift 7914403
  have htrace : WordTrace (prefixWord ++ tailWord_7914403) baseStart_7914403 baseEnd_7914403 := by
    simpa [prefixWord, tailWord_7914403, baseEnd_7914403] using wordTrace_append hprefix tailTrace_7914403
  have hstable : (prefixWord ++ tailWord_7914403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914403).length < 2 ^ (prefixWord ++ tailWord_7914403).sum := by decide
  have hdescent : baseEnd_7914403 < baseStart_7914403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914426 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_7914426 : Nat := 118140960795 + 7914426 * 2 ^ 59
def prefixEnd_7914426 : Nat := 4983230072969 + 3 ^ 40 * 7914426 * 2
def baseEnd_7914426 : Nat := 4063904642440957005577223

theorem tailTrace_7914426 : CollatzResearch.WordTrace tailWord_7914426 prefixEnd_7914426 4063904642440957005577223 := by
  unfold tailWord_7914426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165707706348438298364783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192441887216929168795639421 72165707706348438298364783)
  ·
    refine ⟨108248561559522657447547175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72165707706348438298364783 108248561559522657447547175)
    ·
      refine ⟨162372842339283986171320763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108248561559522657447547175 162372842339283986171320763)
      ·
        refine ⟨243559263508925979256981145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162372842339283986171320763 243559263508925979256981145)
        ·
          refine ⟨182669447631694484442735859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243559263508925979256981145 182669447631694484442735859)
          ·
            refine ⟨274004171447541726664103789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182669447631694484442735859 274004171447541726664103789)
            ·
              refine ⟨102751564292828147499038921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274004171447541726664103789 102751564292828147499038921)
              ·
                refine ⟨77063673219621110624279191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102751564292828147499038921 77063673219621110624279191)
                ·
                  refine ⟨115595509829431665936418787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77063673219621110624279191 115595509829431665936418787)
                  ·
                    refine ⟨173393264744147498904628181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115595509829431665936418787 173393264744147498904628181)
                    ·
                      refine ⟨4063904642440957005577223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173393264744147498904628181 4063904642440957005577223)
                      ·
                        rfl

theorem cell23_7914426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_7914426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914426 prefixEnd_7914426 := by exact prefixLift 7914426
  have htrace : WordTrace (prefixWord ++ tailWord_7914426) baseStart_7914426 baseEnd_7914426 := by
    simpa [prefixWord, tailWord_7914426, baseEnd_7914426] using wordTrace_append hprefix tailTrace_7914426
  have hstable : (prefixWord ++ tailWord_7914426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914426).length < 2 ^ (prefixWord ++ tailWord_7914426).sum := by decide
  have hdescent : baseEnd_7914426 < baseStart_7914426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914450 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_7914450 : Nat := 118140960795 + 7914450 * 2 ^ 59
def prefixEnd_7914450 : Nat := 4983230072969 + 3 ^ 40 * 7914450 * 2
def baseEnd_7914450 : Nat := 1354638988658888303892371

theorem tailTrace_7914450 : CollatzResearch.WordTrace tailWord_7914450 prefixEnd_7914450 1354638988658888303892371 := by
  unfold tailWord_7914450
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165926544326701323083201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192442470784871203528221869 72165926544326701323083201)
  ·
    refine ⟨54124444908245025992312401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72165926544326701323083201 54124444908245025992312401)
    ·
      refine ⟨40593333681183769494234301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54124444908245025992312401 40593333681183769494234301)
      ·
        refine ⟨15222500130443913560337863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40593333681183769494234301 15222500130443913560337863)
        ·
          refine ⟨22833750195665870340506795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222500130443913560337863 22833750195665870340506795)
          ·
            refine ⟨34250625293498805510760193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833750195665870340506795 34250625293498805510760193)
            ·
              refine ⟨25687968970124104133070145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34250625293498805510760193 25687968970124104133070145)
              ·
                refine ⟨19265976727593078099802609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25687968970124104133070145 19265976727593078099802609)
                ·
                  refine ⟨14449482545694808574851957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19265976727593078099802609 14449482545694808574851957)
                  ·
                    refine ⟨1354638988658888303892371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14449482545694808574851957 1354638988658888303892371)
                    ·
                      rfl

theorem cell23_7914450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_7914450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914450 prefixEnd_7914450 := by exact prefixLift 7914450
  have htrace : WordTrace (prefixWord ++ tailWord_7914450) baseStart_7914450 baseEnd_7914450 := by
    simpa [prefixWord, tailWord_7914450, baseEnd_7914450] using wordTrace_append hprefix tailTrace_7914450
  have hstable : (prefixWord ++ tailWord_7914450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914450).length < 2 ^ (prefixWord ++ tailWord_7914450).sum := by decide
  have hdescent : baseEnd_7914450 < baseStart_7914450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914454 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_7914454 : Nat := 118140960795 + 7914454 * 2 ^ 59
def prefixEnd_7914454 : Nat := 4983230072969 + 3 ^ 40 * 7914454 * 2
def baseEnd_7914454 : Nat := 451546557766586988447455

theorem tailTrace_7914454 : CollatzResearch.WordTrace tailWord_7914454 prefixEnd_7914454 451546557766586988447455 := by
  unfold tailWord_7914454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041490754330769623467401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192442568046194875983652277 18041490754330769623467401)
  ·
    refine ⟨13531118065748077217600551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18041490754330769623467401 13531118065748077217600551)
    ·
      refine ⟨20296677098622115826400827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13531118065748077217600551 20296677098622115826400827)
      ·
        refine ⟨30445015647933173739601241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20296677098622115826400827 30445015647933173739601241)
        ·
          refine ⟨22833761735949880304700931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30445015647933173739601241 22833761735949880304700931)
          ·
            refine ⟨34250642603924820457051397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833761735949880304700931 34250642603924820457051397)
            ·
              refine ⟨6421995488235903835697137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34250642603924820457051397 6421995488235903835697137)
              ·
                refine ⟨4816496616176927876772853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421995488235903835697137 4816496616176927876772853)
                ·
                  refine ⟨451546557766586988447455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816496616176927876772853 451546557766586988447455)
                  ·
                    rfl

theorem cell23_7914454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_7914454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914454 prefixEnd_7914454 := by exact prefixLift 7914454
  have htrace : WordTrace (prefixWord ++ tailWord_7914454) baseStart_7914454 baseEnd_7914454 := by
    simpa [prefixWord, tailWord_7914454, baseEnd_7914454] using wordTrace_append hprefix tailTrace_7914454
  have hstable : (prefixWord ++ tailWord_7914454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914454).length < 2 ^ (prefixWord ++ tailWord_7914454).sum := by decide
  have hdescent : baseEnd_7914454 < baseStart_7914454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914476 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 12]
def baseStart_7914476 : Nat := 118140960795 + 7914476 * 2 ^ 59
def prefixEnd_7914476 : Nat := 4983230072969 + 3 ^ 40 * 7914476 * 2
def baseEnd_7914476 : Nat := 451547812941520201105777

theorem tailTrace_7914476 : CollatzResearch.WordTrace tailWord_7914476 prefixEnd_7914476 451547812941520201105777 := by
  unfold tailWord_7914476
  simp only [CollatzResearch.WordTrace]
  refine ⟨144332327237606305866389641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192443102983475074488519521 144332327237606305866389641)
  ·
    refine ⟨108249245428204729399792231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144332327237606305866389641 108249245428204729399792231)
    ·
      refine ⟨162373868142307094099688347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108249245428204729399792231 162373868142307094099688347)
      ·
        refine ⟨243560802213460641149532521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162373868142307094099688347 243560802213460641149532521)
        ·
          refine ⟨182670601660095480862149391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243560802213460641149532521 182670601660095480862149391)
          ·
            refine ⟨274005902490143221293224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182670601660095480862149391 274005902490143221293224087)
            ·
              refine ⟨411008853735214831939836131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274005902490143221293224087 411008853735214831939836131)
              ·
                refine ⟨616513280602822247909754197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411008853735214831939836131 616513280602822247909754197)
                ·
                  refine ⟨451547812941520201105777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 616513280602822247909754197 451547812941520201105777)
                  ·
                    rfl

theorem cell23_7914476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_7914476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914476 prefixEnd_7914476 := by exact prefixLift 7914476
  have htrace : WordTrace (prefixWord ++ tailWord_7914476) baseStart_7914476 baseEnd_7914476 := by
    simpa [prefixWord, tailWord_7914476, baseEnd_7914476] using wordTrace_append hprefix tailTrace_7914476
  have hstable : (prefixWord ++ tailWord_7914476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914476).length < 2 ^ (prefixWord ++ tailWord_7914476).sum := by decide
  have hdescent : baseEnd_7914476 < baseStart_7914476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914497 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 1, 4]
def baseStart_7914497 : Nat := 118140960795 + 7914497 * 2 ^ 59
def prefixEnd_7914497 : Nat := 4983230072969 + 3 ^ 40 * 7914497 * 2
def baseEnd_7914497 : Nat := 1354647033189142075929799

theorem tailTrace_7914497 : CollatzResearch.WordTrace tailWord_7914497 prefixEnd_7914497 1354647033189142075929799 := by
  unfold tailWord_7914497
  simp only [CollatzResearch.WordTrace]
  refine ⟨288665420408136532319293745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192443613605424354879529163 288665420408136532319293745)
  ·
    refine ⟨216499065306102399239470309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288665420408136532319293745 216499065306102399239470309)
    ·
      refine ⟨40593574744894199857400683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216499065306102399239470309 40593574744894199857400683)
      ·
        refine ⟨60890362117341299786101025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40593574744894199857400683 60890362117341299786101025)
        ·
          refine ⟨45667771588005974839575769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60890362117341299786101025 45667771588005974839575769)
          ·
            refine ⟨34250828691004481129681827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45667771588005974839575769 34250828691004481129681827)
            ·
              refine ⟨51376243036506721694522741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34250828691004481129681827 51376243036506721694522741)
              ·
                refine ⟨4816522784672505158861507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51376243036506721694522741 4816522784672505158861507)
                ·
                  refine ⟨7224784177008757738292261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816522784672505158861507 7224784177008757738292261)
                  ·
                    refine ⟨1354647033189142075929799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224784177008757738292261 1354647033189142075929799)
                    ·
                      rfl

theorem cell23_7914497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_7914497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914497 prefixEnd_7914497 := by exact prefixLift 7914497
  have htrace : WordTrace (prefixWord ++ tailWord_7914497) baseStart_7914497 baseEnd_7914497 := by
    simpa [prefixWord, tailWord_7914497, baseEnd_7914497] using wordTrace_append hprefix tailTrace_7914497
  have hstable : (prefixWord ++ tailWord_7914497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914497).length < 2 ^ (prefixWord ++ tailWord_7914497).sum := by decide
  have hdescent : baseEnd_7914497 < baseStart_7914497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914510 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_7914510 : Nat := 118140960795 + 7914510 * 2 ^ 59
def prefixEnd_7914510 : Nat := 4983230072969 + 3 ^ 40 * 7914510 * 2
def baseEnd_7914510 : Nat := 451549752757326075214093

theorem tailTrace_7914510 : CollatzResearch.WordTrace tailWord_7914510 prefixEnd_7914510 451549752757326075214093 := by
  unfold tailWord_7914510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36083236819636179442439623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192443929704726290359677989 36083236819636179442439623)
  ·
    refine ⟨54124855229454269163659435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36083236819636179442439623 54124855229454269163659435)
    ·
      refine ⟨81187282844181403745489153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54124855229454269163659435 81187282844181403745489153)
      ·
        refine ⟨60890462133136052809116865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81187282844181403745489153 60890462133136052809116865)
        ·
          refine ⟨45667846599852039606837649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60890462133136052809116865 45667846599852039606837649)
          ·
            refine ⟨34250884949889029705128237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45667846599852039606837649 34250884949889029705128237)
            ·
              refine ⟨12844081856208386139423089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34250884949889029705128237 12844081856208386139423089)
              ·
                refine ⟨9633061392156289604567317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844081856208386139423089 9633061392156289604567317)
                ·
                  refine ⟨451549752757326075214093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9633061392156289604567317 451549752757326075214093)
                  ·
                    rfl

theorem cell23_7914510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_7914510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914510 prefixEnd_7914510 := by exact prefixLift 7914510
  have htrace : WordTrace (prefixWord ++ tailWord_7914510) baseStart_7914510 baseEnd_7914510 := by
    simpa [prefixWord, tailWord_7914510, baseEnd_7914510] using wordTrace_append hprefix tailTrace_7914510
  have hstable : (prefixWord ++ tailWord_7914510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914510).length < 2 ^ (prefixWord ++ tailWord_7914510).sum := by decide
  have hdescent : baseEnd_7914510 < baseStart_7914510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914540 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_7914540 : Nat := 118140960795 + 7914540 * 2 ^ 59
def prefixEnd_7914540 : Nat := 4983230072969 + 3 ^ 40 * 7914540 * 2
def baseEnd_7914540 : Nat := 1354654393078523186517233

theorem tailTrace_7914540 : CollatzResearch.WordTrace tailWord_7914540 prefixEnd_7914540 1354654393078523186517233 := by
  unfold tailWord_7914540
  simp only [CollatzResearch.WordTrace]
  refine ⟨144333494373490375331554537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192444659164653833775406049 144333494373490375331554537)
  ·
    refine ⟨108250120780117781498665903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144333494373490375331554537 108250120780117781498665903)
    ·
      refine ⟨162375181170176672247998855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108250120780117781498665903 162375181170176672247998855)
      ·
        refine ⟨243562771755265008371998283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162375181170176672247998855 243562771755265008371998283)
        ·
          refine ⟨365344157632897512557997425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243562771755265008371998283 365344157632897512557997425)
          ·
            refine ⟨274008118224673134418498069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365344157632897512557997425 274008118224673134418498069)
            ·
              refine ⟨12844130541781553175867097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274008118224673134418498069 12844130541781553175867097)
              ·
                refine ⟨9633097906336164881900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844130541781553175867097 9633097906336164881900323)
                ·
                  refine ⟨14449646859504247322850485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633097906336164881900323 14449646859504247322850485)
                  ·
                    refine ⟨1354654393078523186517233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14449646859504247322850485 1354654393078523186517233)
                    ·
                      rfl

theorem cell23_7914540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_7914540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914540 prefixEnd_7914540 := by exact prefixLift 7914540
  have htrace : WordTrace (prefixWord ++ tailWord_7914540) baseStart_7914540 baseEnd_7914540 := by
    simpa [prefixWord, tailWord_7914540, baseEnd_7914540] using wordTrace_append hprefix tailTrace_7914540
  have hstable : (prefixWord ++ tailWord_7914540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914540).length < 2 ^ (prefixWord ++ tailWord_7914540).sum := by decide
  have hdescent : baseEnd_7914540 < baseStart_7914540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914543 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_7914543 : Nat := 118140960795 + 7914543 * 2 ^ 59
def prefixEnd_7914543 : Nat := 4983230072969 + 3 ^ 40 * 7914543 * 2
def baseEnd_7914543 : Nat := 4063964719677533047814185

theorem tailTrace_7914543 : CollatzResearch.WordTrace tailWord_7914543 prefixEnd_7914543 4063964719677533047814185 := by
  unfold tailWord_7914543
  simp only [CollatzResearch.WordTrace]
  refine ⟨288667098165969882175468283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192444732110646588116978855 288667098165969882175468283)
  ·
    refine ⟨433000647248954823263202425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288667098165969882175468283 433000647248954823263202425)
    ·
      refine ⟨324750485436716117447401819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433000647248954823263202425 324750485436716117447401819)
      ·
        refine ⟨487125728155074176171102729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324750485436716117447401819 487125728155074176171102729)
        ·
          refine ⟨365344296116305632128327047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487125728155074176171102729 365344296116305632128327047)
          ·
            refine ⟨548016444174458448192490571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365344296116305632128327047 548016444174458448192490571)
            ·
              refine ⟨822024666261687672288735857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548016444174458448192490571 822024666261687672288735857)
              ·
                refine ⟨616518499696265754216551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822024666261687672288735857 616518499696265754216551893)
                ·
                  refine ⟨14449652336631228614450435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 616518499696265754216551893 14449652336631228614450435)
                  ·
                    refine ⟨21674478504946842921675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449652336631228614450435 21674478504946842921675653)
                    ·
                      refine ⟨4063964719677533047814185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21674478504946842921675653 4063964719677533047814185)
                      ·
                        rfl

theorem cell23_7914543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_7914543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914543 prefixEnd_7914543 := by exact prefixLift 7914543
  have htrace : WordTrace (prefixWord ++ tailWord_7914543) baseStart_7914543 baseEnd_7914543 := by
    simpa [prefixWord, tailWord_7914543, baseEnd_7914543] using wordTrace_append hprefix tailTrace_7914543
  have hstable : (prefixWord ++ tailWord_7914543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914543).length < 2 ^ (prefixWord ++ tailWord_7914543).sum := by decide
  have hdescent : baseEnd_7914543 < baseStart_7914543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914554 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_7914554 : Nat := 118140960795 + 7914554 * 2 ^ 59
def prefixEnd_7914554 : Nat := 4983230072969 + 3 ^ 40 * 7914554 * 2
def baseEnd_7914554 : Nat := 4063970367964732504776635

theorem tailTrace_7914554 : CollatzResearch.WordTrace tailWord_7914554 prefixEnd_7914554 4063970367964732504776635 := by
  unfold tailWord_7914554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72166874842232507763529679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192444999579286687369412477 72166874842232507763529679)
  ·
    refine ⟨108250312263348761645294519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72166874842232507763529679 108250312263348761645294519)
    ·
      refine ⟨162375468395023142467941779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108250312263348761645294519 162375468395023142467941779)
      ·
        refine ⟨243563202592534713701912669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162375468395023142467941779 243563202592534713701912669)
        ·
          refine ⟨91336200972200517638217251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243563202592534713701912669 91336200972200517638217251)
          ·
            refine ⟨137004301458300776457325877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91336200972200517638217251 137004301458300776457325877)
            ·
              refine ⟨12844153261715697792874301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137004301458300776457325877 12844153261715697792874301)
              ·
                refine ⟨4816557473143386672327863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12844153261715697792874301 4816557473143386672327863)
                ·
                  refine ⟨7224836209715080008491795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816557473143386672327863 7224836209715080008491795)
                  ·
                    refine ⟨10837254314572620012737693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224836209715080008491795 10837254314572620012737693)
                    ·
                      refine ⟨4063970367964732504776635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10837254314572620012737693 4063970367964732504776635)
                      ·
                        rfl

theorem cell23_7914554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_7914554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914554 prefixEnd_7914554 := by exact prefixLift 7914554
  have htrace : WordTrace (prefixWord ++ tailWord_7914554) baseStart_7914554 baseEnd_7914554 := by
    simpa [prefixWord, tailWord_7914554, baseEnd_7914554] using wordTrace_append hprefix tailTrace_7914554
  have hstable : (prefixWord ++ tailWord_7914554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914554).length < 2 ^ (prefixWord ++ tailWord_7914554).sum := by decide
  have hdescent : baseEnd_7914554 < baseStart_7914554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914560 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_7914560 : Nat := 118140960795 + 7914560 * 2 ^ 59
def prefixEnd_7914560 : Nat := 4983230072969 + 3 ^ 40 * 7914560 * 2
def baseEnd_7914560 : Nat := 4063973448848659481301607

theorem tailTrace_7914560 : CollatzResearch.WordTrace tailWord_7914560 prefixEnd_7914560 4063973448848659481301607 := by
  unfold tailWord_7914560
  simp only [CollatzResearch.WordTrace]
  refine ⟨144333859103454147039418567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192445145471272196052558089 144333859103454147039418567)
  ·
    refine ⟨216500788655181220559127851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144333859103454147039418567 216500788655181220559127851)
    ·
      refine ⟨324751182982771830838691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216500788655181220559127851 324751182982771830838691777)
      ·
        refine ⟨243563387237078873129018833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324751182982771830838691777 243563387237078873129018833)
        ·
          refine ⟨182672540427809154846764125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243563387237078873129018833 182672540427809154846764125)
          ·
            refine ⟨68502202660428433067536547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182672540427809154846764125 68502202660428433067536547)
            ·
              refine ⟨102753303990642649601304821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68502202660428433067536547 102753303990642649601304821)
              ·
                refine ⟨9633122249122748400122327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102753303990642649601304821 9633122249122748400122327)
                ·
                  refine ⟨14449683373684122600183491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633122249122748400122327 14449683373684122600183491)
                  ·
                    refine ⟨21674525060526183900275237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449683373684122600183491 21674525060526183900275237)
                    ·
                      refine ⟨4063973448848659481301607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21674525060526183900275237 4063973448848659481301607)
                      ·
                        rfl

theorem cell23_7914560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_7914560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914560 prefixEnd_7914560 := by exact prefixLift 7914560
  have htrace : WordTrace (prefixWord ++ tailWord_7914560) baseStart_7914560 baseEnd_7914560 := by
    simpa [prefixWord, tailWord_7914560, baseEnd_7914560] using wordTrace_append hprefix tailTrace_7914560
  have hstable : (prefixWord ++ tailWord_7914560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914560).length < 2 ^ (prefixWord ++ tailWord_7914560).sum := by decide
  have hdescent : baseEnd_7914560 < baseStart_7914560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914570 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_7914570 : Nat := 118140960795 + 7914570 * 2 ^ 59
def prefixEnd_7914570 : Nat := 4983230072969 + 3 ^ 40 * 7914570 * 2
def baseEnd_7914570 : Nat := 1354659527885068147392187

theorem tailTrace_7914570 : CollatzResearch.WordTrace tailWord_7914570 prefixEnd_7914570 1354659527885068147392187 := by
  unfold tailWord_7914570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167020734218016446675291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192445388624581377191134109 72167020734218016446675291)
  ·
    refine ⟨108250531101327024670012937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72167020734218016446675291 108250531101327024670012937)
    ·
      refine ⟨81187898325995268502509703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108250531101327024670012937 81187898325995268502509703)
      ·
        refine ⟨121781847488992902753764555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81187898325995268502509703 121781847488992902753764555)
        ·
          refine ⟨182672771233489354130646833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121781847488992902753764555 182672771233489354130646833)
          ·
            refine ⟨137004578425117015597985125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182672771233489354130646833 137004578425117015597985125)
            ·
              refine ⟨25688358454709440424622211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137004578425117015597985125 25688358454709440424622211)
              ·
                refine ⟨38532537682064160636933317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25688358454709440424622211 38532537682064160636933317)
                ·
                  refine ⟨7224850815387030119424997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38532537682064160636933317 7224850815387030119424997)
                  ·
                    refine ⟨1354659527885068147392187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224850815387030119424997 1354659527885068147392187)
                    ·
                      rfl

theorem cell23_7914570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_7914570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914570 prefixEnd_7914570 := by exact prefixLift 7914570
  have htrace : WordTrace (prefixWord ++ tailWord_7914570) baseStart_7914570 baseEnd_7914570 := by
    simpa [prefixWord, tailWord_7914570, baseEnd_7914570] using wordTrace_append hprefix tailTrace_7914570
  have hstable : (prefixWord ++ tailWord_7914570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914570).length < 2 ^ (prefixWord ++ tailWord_7914570).sum := by decide
  have hdescent : baseEnd_7914570 < baseStart_7914570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914580 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7914580 : Nat := 118140960795 + 7914580 * 2 ^ 59
def prefixEnd_7914580 : Nat := 4983230072969 + 3 ^ 40 * 7914580 * 2
def baseEnd_7914580 : Nat := 4063983718461749403051515

theorem tailTrace_7914580 : CollatzResearch.WordTrace tailWord_7914580 prefixEnd_7914580 4063983718461749403051515 := by
  unfold tailWord_7914580
  simp only [CollatzResearch.WordTrace]
  refine ⟨144334223833417918747282597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192445631777890558329710129 144334223833417918747282597)
  ·
    refine ⟨27062666968765859765115487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144334223833417918747282597 27062666968765859765115487)
    ·
      refine ⟨40594000453148789647673231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27062666968765859765115487 40594000453148789647673231)
      ·
        refine ⟨60891000679723184471509847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40594000453148789647673231 60891000679723184471509847)
        ·
          refine ⟨91336501019584776707264771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60891000679723184471509847 91336501019584776707264771)
          ·
            refine ⟨137004751529377165060897157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91336501019584776707264771 137004751529377165060897157)
            ·
              refine ⟨25688390911758218448918217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137004751529377165060897157 25688390911758218448918217)
              ·
                refine ⟨19266293183818663836688663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25688390911758218448918217 19266293183818663836688663)
                ·
                  refine ⟨28899439775727995755032995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19266293183818663836688663 28899439775727995755032995)
                  ·
                    refine ⟨43349159663591993632549493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28899439775727995755032995 43349159663591993632549493)
                    ·
                      refine ⟨4063983718461749403051515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43349159663591993632549493 4063983718461749403051515)
                      ·
                        rfl

theorem cell23_7914580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7914580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914580 prefixEnd_7914580 := by exact prefixLift 7914580
  have htrace : WordTrace (prefixWord ++ tailWord_7914580) baseStart_7914580 baseEnd_7914580 := by
    simpa [prefixWord, tailWord_7914580, baseEnd_7914580] using wordTrace_append hprefix tailTrace_7914580
  have hstable : (prefixWord ++ tailWord_7914580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914580).length < 2 ^ (prefixWord ++ tailWord_7914580).sum := by decide
  have hdescent : baseEnd_7914580 < baseStart_7914580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914594 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7914594 : Nat := 118140960795 + 7914594 * 2 ^ 59
def prefixEnd_7914594 : Nat := 4983230072969 + 3 ^ 40 * 7914594 * 2
def baseEnd_7914594 : Nat := 4063990907190912348276451

theorem tailTrace_7914594 : CollatzResearch.WordTrace tailWord_7914594 prefixEnd_7914594 4063990907190912348276451 := by
  unfold tailWord_7914594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167239572196279471393709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192445972192523411923716557 72167239572196279471393709)
  ·
    refine ⟨27062714839573604801772641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72167239572196279471393709 27062714839573604801772641)
    ·
      refine ⟨20297036129680203601329481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27062714839573604801772641 20297036129680203601329481)
      ·
        refine ⟨15222777097260152700997111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20297036129680203601329481 15222777097260152700997111)
        ·
          refine ⟨22834165645890229051495667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222777097260152700997111 22834165645890229051495667)
          ·
            refine ⟨34251248468835343577243501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22834165645890229051495667 34251248468835343577243501)
            ·
              refine ⟨12844218175813253841466313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34251248468835343577243501 12844218175813253841466313)
              ·
                refine ⟨9633163631859940381099735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844218175813253841466313 9633163631859940381099735)
                ·
                  refine ⟨14449745447789910571649603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633163631859940381099735 14449745447789910571649603)
                  ·
                    refine ⟨21674618171684865857474405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14449745447789910571649603 21674618171684865857474405)
                    ·
                      refine ⟨4063990907190912348276451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21674618171684865857474405 4063990907190912348276451)
                      ·
                        rfl

theorem cell23_7914594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7914594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914594 prefixEnd_7914594 := by exact prefixLift 7914594
  have htrace : WordTrace (prefixWord ++ tailWord_7914594) baseStart_7914594 baseEnd_7914594 := by
    simpa [prefixWord, tailWord_7914594, baseEnd_7914594] using wordTrace_append hprefix tailTrace_7914594
  have hstable : (prefixWord ++ tailWord_7914594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914594).length < 2 ^ (prefixWord ++ tailWord_7914594).sum := by decide
  have hdescent : baseEnd_7914594 < baseStart_7914594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914628 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7914628 : Nat := 118140960795 + 7914628 * 2 ^ 59
def prefixEnd_7914628 : Nat := 4983230072969 + 3 ^ 40 * 7914628 * 2
def baseEnd_7914628 : Nat := 4064008365533165215251295

theorem tailTrace_7914628 : CollatzResearch.WordTrace tailWord_7914628 prefixEnd_7914628 4064008365533165215251295 := by
  unfold tailWord_7914628
  simp only [CollatzResearch.WordTrace]
  refine ⟨144335099185330970846156269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192446798913774627794875025 144335099185330970846156269)
  ·
    refine ⟨54125662194499114067308601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144335099185330970846156269 54125662194499114067308601)
    ·
      refine ⟨40594246645874335550481451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54125662194499114067308601 40594246645874335550481451)
      ·
        refine ⟨60891369968811503325722177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40594246645874335550481451 60891369968811503325722177)
        ·
          refine ⟨45668527476608627494291633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60891369968811503325722177 45668527476608627494291633)
          ·
            refine ⟨34251395607456470620718725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45668527476608627494291633 34251395607456470620718725)
            ·
              refine ⟨6422136676398088241384761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34251395607456470620718725 6422136676398088241384761)
              ·
                refine ⟨4816602507298566181038571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422136676398088241384761 4816602507298566181038571)
                ·
                  refine ⟨7224903760947849271557857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816602507298566181038571 7224903760947849271557857)
                  ·
                    refine ⟨5418677820710886953668393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224903760947849271557857 5418677820710886953668393)
                    ·
                      refine ⟨4064008365533165215251295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418677820710886953668393 4064008365533165215251295)
                      ·
                        rfl

theorem cell23_7914628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7914628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914628 prefixEnd_7914628 := by exact prefixLift 7914628
  have htrace : WordTrace (prefixWord ++ tailWord_7914628) baseStart_7914628 baseEnd_7914628 := by
    simpa [prefixWord, tailWord_7914628, baseEnd_7914628] using wordTrace_append hprefix tailTrace_7914628
  have hstable : (prefixWord ++ tailWord_7914628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914628).length < 2 ^ (prefixWord ++ tailWord_7914628).sum := by decide
  have hdescent : baseEnd_7914628 < baseStart_7914628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914643 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 8]
def baseStart_7914643 : Nat := 118140960795 + 7914643 * 2 ^ 59
def prefixEnd_7914643 : Nat := 4983230072969 + 3 ^ 40 * 7914643 * 2
def baseEnd_7914643 : Nat := 1354672022580994218854575

theorem tailTrace_7914643 : CollatzResearch.WordTrace tailWord_7914643 prefixEnd_7914643 1354672022580994218854575 := by
  unfold tailWord_7914643
  simp only [CollatzResearch.WordTrace]
  refine ⟨288670745465607599254108583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192447163643738399502739055 288670745465607599254108583)
  ·
    refine ⟨433006118198411398881162875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288670745465607599254108583 433006118198411398881162875)
    ·
      refine ⟨649509177297617098321744313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433006118198411398881162875 649509177297617098321744313)
      ·
        refine ⟨487131882973212823741308235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649509177297617098321744313 487131882973212823741308235)
        ·
          refine ⟨730697824459819235611962353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487131882973212823741308235 730697824459819235611962353)
          ·
            refine ⟨548023368344864426708971765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730697824459819235611962353 548023368344864426708971765)
            ·
              refine ⟨51377190782331040003966103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 548023368344864426708971765 51377190782331040003966103)
              ·
                refine ⟨77065786173496560005949155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51377190782331040003966103 77065786173496560005949155)
                ·
                  refine ⟨115598679260244840008923733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77065786173496560005949155 115598679260244840008923733)
                  ·
                    refine ⟨1354672022580994218854575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115598679260244840008923733 1354672022580994218854575)
                    ·
                      rfl

theorem cell23_7914643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_7914643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914643 prefixEnd_7914643 := by exact prefixLift 7914643
  have htrace : WordTrace (prefixWord ++ tailWord_7914643) baseStart_7914643 baseEnd_7914643 := by
    simpa [prefixWord, tailWord_7914643, baseEnd_7914643] using wordTrace_append hprefix tailTrace_7914643
  have hstable : (prefixWord ++ tailWord_7914643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914643).length < 2 ^ (prefixWord ++ tailWord_7914643).sum := by decide
  have hdescent : baseEnd_7914643 < baseStart_7914643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914678 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7914678 : Nat := 118140960795 + 7914678 * 2 ^ 59
def prefixEnd_7914678 : Nat := 4983230072969 + 3 ^ 40 * 7914678 * 2
def baseEnd_7914678 : Nat := 4064034039565890019626065

theorem tailTrace_7914678 : CollatzResearch.WordTrace tailWord_7914678 prefixEnd_7914678 4064034039565890019626065 := by
  unfold tailWord_7914678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042001376280050014477043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192448014680320533487755125 18042001376280050014477043)
  ·
    refine ⟨27063002064420075021715565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042001376280050014477043 27063002064420075021715565)
    ·
      refine ⟨10148625774157528133143337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27063002064420075021715565 10148625774157528133143337)
      ·
        refine ⟨7611469330618146099857503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10148625774157528133143337 7611469330618146099857503)
        ·
          refine ⟨11417203995927219149786255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611469330618146099857503 11417203995927219149786255)
          ·
            refine ⟨17125805993890828724679383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417203995927219149786255 17125805993890828724679383)
            ·
              refine ⟨25688708990836243087019075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17125805993890828724679383 25688708990836243087019075)
              ·
                refine ⟨38533063486254364630528613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25688708990836243087019075 38533063486254364630528613)
                ·
                  refine ⟨7224949403672693368224115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38533063486254364630528613 7224949403672693368224115)
                  ·
                    refine ⟨10837424105509040052336173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224949403672693368224115 10837424105509040052336173)
                    ·
                      refine ⟨4064034039565890019626065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10837424105509040052336173 4064034039565890019626065)
                      ·
                        rfl

theorem cell23_7914678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7914678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914678 prefixEnd_7914678 := by exact prefixLift 7914678
  have htrace : WordTrace (prefixWord ++ tailWord_7914678) baseStart_7914678 baseEnd_7914678 := by
    simpa [prefixWord, tailWord_7914678, baseEnd_7914678] using wordTrace_append hprefix tailTrace_7914678
  have hstable : (prefixWord ++ tailWord_7914678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914678).length < 2 ^ (prefixWord ++ tailWord_7914678).sum := by decide
  have hdescent : baseEnd_7914678 < baseStart_7914678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_7914683 : Nat := 118140960795 + 7914683 * 2 ^ 59
def prefixEnd_7914683 : Nat := 4983230072969 + 3 ^ 40 * 7914683 * 2
def baseEnd_7914683 : Nat := 4064036606969162500063541

theorem tailTrace_7914683 : CollatzResearch.WordTrace tailWord_7914683 prefixEnd_7914683 4064036606969162500063541 := by
  unfold tailWord_7914683
  simp only [CollatzResearch.WordTrace]
  refine ⟨288672204385462686085564703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192448136256975124057043135 288672204385462686085564703)
  ·
    refine ⟨433008306578194029128347055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288672204385462686085564703 433008306578194029128347055)
    ·
      refine ⟨649512459867291043692520583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433008306578194029128347055 649512459867291043692520583)
      ·
        refine ⟨974268689800936565538780875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649512459867291043692520583 974268689800936565538780875)
        ·
          refine ⟨1461403034701404848308171313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974268689800936565538780875 1461403034701404848308171313)
          ·
            refine ⟨1096052276026053636231128485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461403034701404848308171313 1096052276026053636231128485)
            ·
              refine ⟨205509801754885056793336591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096052276026053636231128485 205509801754885056793336591)
              ·
                refine ⟨308264702632327585190004887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205509801754885056793336591 308264702632327585190004887)
                ·
                  refine ⟨462397053948491377785007331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308264702632327585190004887 462397053948491377785007331)
                  ·
                    refine ⟨693595580922737066677510997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462397053948491377785007331 693595580922737066677510997)
                    ·
                      refine ⟨4064036606969162500063541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 693595580922737066677510997 4064036606969162500063541)
                      ·
                        rfl

theorem cell23_7914683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_7914683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914683 prefixEnd_7914683 := by exact prefixLift 7914683
  have htrace : WordTrace (prefixWord ++ tailWord_7914683) baseStart_7914683 baseEnd_7914683 := by
    simpa [prefixWord, tailWord_7914683, baseEnd_7914683] using wordTrace_append hprefix tailTrace_7914683
  have hstable : (prefixWord ++ tailWord_7914683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914683).length < 2 ^ (prefixWord ++ tailWord_7914683).sum := by decide
  have hdescent : baseEnd_7914683 < baseStart_7914683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914720 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_7914720 : Nat := 118140960795 + 7914720 * 2 ^ 59
def prefixEnd_7914720 : Nat := 4983230072969 + 3 ^ 40 * 7914720 * 2
def baseEnd_7914720 : Nat := 1354685201917792951766957

theorem tailTrace_7914720 : CollatzResearch.WordTrace tailWord_7914720 prefixEnd_7914720 1354685201917792951766957 := by
  unfold tailWord_7914720
  simp only [CollatzResearch.WordTrace]
  refine ⟨144336776943164320702330807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192449035924219094269774409 144336776943164320702330807)
  ·
    refine ⟨216505165414746481053496211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144336776943164320702330807 216505165414746481053496211)
    ·
      refine ⟨324757748122119721580244317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216505165414746481053496211 324757748122119721580244317)
      ·
        refine ⟨121784155545794895592591619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324757748122119721580244317 121784155545794895592591619)
        ·
          refine ⟨182676233318692343388887429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121784155545794895592591619 182676233318692343388887429)
          ·
            refine ⟨34251793747254814385416393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182676233318692343388887429 34251793747254814385416393)
            ·
              refine ⟨25688845310441110789062295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34251793747254814385416393 25688845310441110789062295)
              ·
                refine ⟨38533267965661666183593443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25688845310441110789062295 38533267965661666183593443)
                ·
                  refine ⟨57799901948492499275390165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38533267965661666183593443 57799901948492499275390165)
                  ·
                    refine ⟨1354685201917792951766957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57799901948492499275390165 1354685201917792951766957)
                    ·
                      rfl

theorem cell23_7914720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_7914720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914720 prefixEnd_7914720 := by exact prefixLift 7914720
  have htrace : WordTrace (prefixWord ++ tailWord_7914720) baseStart_7914720 baseEnd_7914720 := by
    simpa [prefixWord, tailWord_7914720, baseEnd_7914720] using wordTrace_append hprefix tailTrace_7914720
  have hstable : (prefixWord ++ tailWord_7914720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914720).length < 2 ^ (prefixWord ++ tailWord_7914720).sum := by decide
  have hdescent : baseEnd_7914720 < baseStart_7914720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914757 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_7914757 : Nat := 118140960795 + 7914757 * 2 ^ 59
def prefixEnd_7914757 : Nat := 4983230072969 + 3 ^ 40 * 7914757 * 2
def baseEnd_7914757 : Nat := 4064074604537595210538201

theorem tailTrace_7914757 : CollatzResearch.WordTrace tailWord_7914757 prefixEnd_7914757 4064074604537595210538201 := by
  unfold tailWord_7914757
  simp only [CollatzResearch.WordTrace]
  refine ⟨288674903387194596723758525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192449935591463064482505683 288674903387194596723758525)
  ·
    refine ⟨108253088770197973771409447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288674903387194596723758525 108253088770197973771409447)
    ·
      refine ⟨162379633155296960657114171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108253088770197973771409447 162379633155296960657114171)
      ·
        refine ⟨243569449732945440985671257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162379633155296960657114171 243569449732945440985671257)
        ·
          refine ⟨182677087299709080739253443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243569449732945440985671257 182677087299709080739253443)
          ·
            refine ⟨274015630949563621108880165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182677087299709080739253443 274015630949563621108880165)
            ·
              refine ⟨51377930803043178957915031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274015630949563621108880165 51377930803043178957915031)
              ·
                refine ⟨77066896204564768436872547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51377930803043178957915031 77066896204564768436872547)
                ·
                  refine ⟨115600344306847152655308821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77066896204564768436872547 115600344306847152655308821)
                  ·
                    refine ⟨5418766139383460280717601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115600344306847152655308821 5418766139383460280717601)
                    ·
                      refine ⟨4064074604537595210538201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418766139383460280717601 4064074604537595210538201)
                      ·
                        rfl

theorem cell23_7914757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_7914757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914757 prefixEnd_7914757 := by exact prefixLift 7914757
  have htrace : WordTrace (prefixWord ++ tailWord_7914757) baseStart_7914757 baseEnd_7914757 := by
    simpa [prefixWord, tailWord_7914757, baseEnd_7914757] using wordTrace_append hprefix tailTrace_7914757
  have hstable : (prefixWord ++ tailWord_7914757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914757).length < 2 ^ (prefixWord ++ tailWord_7914757).sum := by decide
  have hdescent : baseEnd_7914757 < baseStart_7914757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914780 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 10]
def baseStart_7914780 : Nat := 118140960795 + 7914780 * 2 ^ 59
def prefixEnd_7914780 : Nat := 4983230072969 + 3 ^ 40 * 7914780 * 2
def baseEnd_7914780 : Nat := 451565157176960957838955

theorem tailTrace_7914780 : CollatzResearch.WordTrace tailWord_7914780 prefixEnd_7914780 451565157176960957838955 := by
  unfold tailWord_7914780
  simp only [CollatzResearch.WordTrace]
  refine ⟨144337871133055635825922897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192450494844074181101230529 144337871133055635825922897)
  ·
    refine ⟨108253403349791726869442173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144337871133055635825922897 108253403349791726869442173)
    ·
      refine ⟨40595026256171897576040815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108253403349791726869442173 40595026256171897576040815)
      ·
        refine ⟨60892539384257846364061223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40595026256171897576040815 60892539384257846364061223)
        ·
          refine ⟨91338809076386769546091835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60892539384257846364061223 91338809076386769546091835)
          ·
            refine ⟨137008213614580154319137753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91338809076386769546091835 137008213614580154319137753)
            ·
              refine ⟨102756160210935115739353315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137008213614580154319137753 102756160210935115739353315)
              ·
                refine ⟨154134240316402673609029973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102756160210935115739353315 154134240316402673609029973)
                ·
                  refine ⟨451565157176960957838955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154134240316402673609029973 451565157176960957838955)
                  ·
                    rfl

theorem cell23_7914780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_7914780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914780 prefixEnd_7914780 := by exact prefixLift 7914780
  have htrace : WordTrace (prefixWord ++ tailWord_7914780) baseStart_7914780 baseEnd_7914780 := by
    simpa [prefixWord, tailWord_7914780, baseEnd_7914780] using wordTrace_append hprefix tailTrace_7914780
  have hstable : (prefixWord ++ tailWord_7914780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914780).length < 2 ^ (prefixWord ++ tailWord_7914780).sum := by decide
  have hdescent : baseEnd_7914780 < baseStart_7914780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914800 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_7914800 : Nat := 118140960795 + 7914800 * 2 ^ 59
def prefixEnd_7914800 : Nat := 4983230072969 + 3 ^ 40 * 7914800 * 2
def baseEnd_7914800 : Nat := 4064096684205738542300503

theorem tailTrace_7914800 : CollatzResearch.WordTrace tailWord_7914800 prefixEnd_7914800 4064096684205738542300503 := by
  unfold tailWord_7914800
  simp only [CollatzResearch.WordTrace]
  refine ⟨144338235863019407533786927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192450981150692543378382569 144338235863019407533786927)
  ·
    refine ⟨216507353794529111300680391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144338235863019407533786927 216507353794529111300680391)
    ·
      refine ⟨324761030691793666951020587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216507353794529111300680391 324761030691793666951020587)
      ·
        refine ⟨487141546037690500426530881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324761030691793666951020587 487141546037690500426530881)
        ·
          refine ⟨365356159528267875319898161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487141546037690500426530881 365356159528267875319898161)
          ·
            refine ⟨274017119646200906489923621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365356159528267875319898161 274017119646200906489923621)
            ·
              refine ⟨51378209933662669966860679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274017119646200906489923621 51378209933662669966860679)
              ·
                refine ⟨77067314900494004950291019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51378209933662669966860679 77067314900494004950291019)
                ·
                  refine ⟨115600972350741007425436529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77067314900494004950291019 115600972350741007425436529)
                  ·
                    refine ⟨86700729263055755569077397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115600972350741007425436529 86700729263055755569077397)
                    ·
                      refine ⟨4064096684205738542300503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86700729263055755569077397 4064096684205738542300503)
                      ·
                        rfl

theorem cell23_7914800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_7914800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914800 prefixEnd_7914800 := by exact prefixLift 7914800
  have htrace : WordTrace (prefixWord ++ tailWord_7914800) baseStart_7914800 baseEnd_7914800 := by
    simpa [prefixWord, tailWord_7914800, baseEnd_7914800] using wordTrace_append hprefix tailTrace_7914800
  have hstable : (prefixWord ++ tailWord_7914800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914800).length < 2 ^ (prefixWord ++ tailWord_7914800).sum := by decide
  have hdescent : baseEnd_7914800 < baseStart_7914800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914801 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 1, 4]
def baseStart_7914801 : Nat := 118140960795 + 7914801 * 2 ^ 59
def prefixEnd_7914801 : Nat := 4983230072969 + 3 ^ 40 * 7914801 * 2
def baseEnd_7914801 : Nat := 1354699065895464346129333

theorem tailTrace_7914801 : CollatzResearch.WordTrace tailWord_7914801 prefixEnd_7914801 1354699065895464346129333 := by
  unfold tailWord_7914801
  simp only [CollatzResearch.WordTrace]
  refine ⟨288676508199035192238360257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192451005466023461492240171 288676508199035192238360257)
  ·
    refine ⟨216507381149276394178770193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288676508199035192238360257 216507381149276394178770193)
    ·
      refine ⟨162380535861957295634077645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216507381149276394178770193 162380535861957295634077645)
      ·
        refine ⟨60892700948233985862779117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162380535861957295634077645 60892700948233985862779117)
        ·
          refine ⟨22834762855587744698542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60892700948233985862779117 22834762855587744698542169)
          ·
            refine ⟨17126072141690808523906627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22834762855587744698542169 17126072141690808523906627)
            ·
              refine ⟨25689108212536212785859941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126072141690808523906627 25689108212536212785859941)
              ·
                refine ⟨4816707789850539897348739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25689108212536212785859941 4816707789850539897348739)
                ·
                  refine ⟨7225061684775809846023109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816707789850539897348739 7225061684775809846023109)
                  ·
                    refine ⟨1354699065895464346129333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225061684775809846023109 1354699065895464346129333)
                    ·
                      rfl

theorem cell23_7914801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_7914801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914801 prefixEnd_7914801 := by exact prefixLift 7914801
  have htrace : WordTrace (prefixWord ++ tailWord_7914801) baseStart_7914801 baseEnd_7914801 := by
    simpa [prefixWord, tailWord_7914801, baseEnd_7914801] using wordTrace_append hprefix tailTrace_7914801
  have hstable : (prefixWord ++ tailWord_7914801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914801).length < 2 ^ (prefixWord ++ tailWord_7914801).sum := by decide
  have hdescent : baseEnd_7914801 < baseStart_7914801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914841 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 1, 1, 3]
def baseStart_7914841 : Nat := 118140960795 + 7914841 * 2 ^ 59
def prefixEnd_7914841 : Nat := 4983230072969 + 3 ^ 40 * 7914841 * 2
def baseEnd_7914841 : Nat := 4064117736912572881887815

theorem tailTrace_7914841 : CollatzResearch.WordTrace tailWord_7914841 prefixEnd_7914841 4064117736912572881887815 := by
  unfold tailWord_7914841
  simp only [CollatzResearch.WordTrace]
  refine ⟨288677967118890279069816377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192451978079260186046544251 288677967118890279069816377)
  ·
    refine ⟨216508475339167709302362283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288677967118890279069816377 216508475339167709302362283)
    ·
      refine ⟨324762713008751563953543425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216508475339167709302362283 324762713008751563953543425)
      ·
        refine ⟨243572034756563672965157569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324762713008751563953543425 243572034756563672965157569)
        ·
          refine ⟨182679026067422754723868177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243572034756563672965157569 182679026067422754723868177)
          ·
            refine ⟨137009269550567066042901133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182679026067422754723868177 137009269550567066042901133)
            ·
              refine ⟨51378476081462649766087925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137009269550567066042901133 51378476081462649766087925)
              ·
                refine ⟨4816732132637123415570743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51378476081462649766087925 4816732132637123415570743)
                ·
                  refine ⟨7225098198955685123356115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816732132637123415570743 7225098198955685123356115)
                  ·
                    refine ⟨10837647298433527685034173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7225098198955685123356115 10837647298433527685034173)
                    ·
                      refine ⟨4064117736912572881887815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10837647298433527685034173 4064117736912572881887815)
                      ·
                        rfl

theorem cell23_7914841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_7914841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914841 prefixEnd_7914841 := by exact prefixLift 7914841
  have htrace : WordTrace (prefixWord ++ tailWord_7914841) baseStart_7914841 baseEnd_7914841 := by
    simpa [prefixWord, tailWord_7914841, baseEnd_7914841] using wordTrace_append hprefix tailTrace_7914841
  have hstable : (prefixWord ++ tailWord_7914841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914841).length < 2 ^ (prefixWord ++ tailWord_7914841).sum := by decide
  have hdescent : baseEnd_7914841 < baseStart_7914841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914858 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7914858 : Nat := 118140960795 + 7914858 * 2 ^ 59
def prefixEnd_7914858 : Nat := 4983230072969 + 3 ^ 40 * 7914858 * 2
def baseEnd_7914858 : Nat := 4064126466083699315375237

theorem tailTrace_7914858 : CollatzResearch.WordTrace tailWord_7914858 prefixEnd_7914858 4064126466083699315375237 := by
  unfold tailWord_7914858
  simp only [CollatzResearch.WordTrace]
  refine ⟨72169646789957172743296307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192452391439885793982123485 72169646789957172743296307)
  ·
    refine ⟨108254470184935759114944461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72169646789957172743296307 108254470184935759114944461)
    ·
      refine ⟨40595426319350909668104173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108254470184935759114944461 40595426319350909668104173)
      ·
        refine ⟨15223284869756591125539065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40595426319350909668104173 15223284869756591125539065)
        ·
          refine ⟨11417463652317443344154299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223284869756591125539065 11417463652317443344154299)
          ·
            refine ⟨17126195478476165016231449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417463652317443344154299 17126195478476165016231449)
            ·
              refine ⟨12844646608857123762173587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126195478476165016231449 12844646608857123762173587)
              ·
                refine ⟨19266969913285685643260381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844646608857123762173587 19266969913285685643260381)
                ·
                  refine ⟨7225113717482132116222643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19266969913285685643260381 7225113717482132116222643)
                  ·
                    refine ⟨10837670576223198174333965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7225113717482132116222643 10837670576223198174333965)
                    ·
                      refine ⟨4064126466083699315375237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10837670576223198174333965 4064126466083699315375237)
                      ·
                        rfl

theorem cell23_7914858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7914858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914858 prefixEnd_7914858 := by exact prefixLift 7914858
  have htrace : WordTrace (prefixWord ++ tailWord_7914858) baseStart_7914858 baseEnd_7914858 := by
    simpa [prefixWord, tailWord_7914858, baseEnd_7914858] using wordTrace_append hprefix tailTrace_7914858
  have hstable : (prefixWord ++ tailWord_7914858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914858).length < 2 ^ (prefixWord ++ tailWord_7914858).sum := by decide
  have hdescent : baseEnd_7914858 < baseStart_7914858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914877 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_7914877 : Nat := 118140960795 + 7914877 * 2 ^ 59
def prefixEnd_7914877 : Nat := 4983230072969 + 3 ^ 40 * 7914877 * 2
def baseEnd_7914877 : Nat := 4064136222216134741037649

theorem tailTrace_7914877 : CollatzResearch.WordTrace tailWord_7914877 prefixEnd_7914877 4064136222216134741037649 := by
  unfold tailWord_7914877
  simp only [CollatzResearch.WordTrace]
  refine ⟨288679280146759857218126885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192452853431173238145417923 288679280146759857218126885)
  ·
    refine ⟨54127365027517473228398791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288679280146759857218126885 54127365027517473228398791)
    ·
      refine ⟨81191047541276209842598187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54127365027517473228398791 81191047541276209842598187)
      ·
        refine ⟨121786571311914314763897281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81191047541276209842598187 121786571311914314763897281)
        ·
          refine ⟨91339928483935736072922961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121786571311914314763897281 91339928483935736072922961)
          ·
            refine ⟨68504946362951802054692221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91339928483935736072922961 68504946362951802054692221)
            ·
              refine ⟨25689354886106925770509583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68504946362951802054692221 25689354886106925770509583)
              ·
                refine ⟨38534032329160388655764375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689354886106925770509583 38534032329160388655764375)
                ·
                  refine ⟨57801048493740582983646563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38534032329160388655764375 57801048493740582983646563)
                  ·
                    refine ⟨86701572740610874475469845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57801048493740582983646563 86701572740610874475469845)
                    ·
                      refine ⟨4064136222216134741037649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86701572740610874475469845 4064136222216134741037649)
                      ·
                        rfl

theorem cell23_7914877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_7914877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914877 prefixEnd_7914877 := by exact prefixLift 7914877
  have htrace : WordTrace (prefixWord ++ tailWord_7914877) baseStart_7914877 baseEnd_7914877 := by
    simpa [prefixWord, tailWord_7914877, baseEnd_7914877] using wordTrace_append hprefix tailTrace_7914877
  have hstable : (prefixWord ++ tailWord_7914877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914877).length < 2 ^ (prefixWord ++ tailWord_7914877).sum := by decide
  have hdescent : baseEnd_7914877 < baseStart_7914877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914887 : List Nat := [1, 1, 4, 2, 2, 3, 1, 9]
def baseStart_7914887 : Nat := 118140960795 + 7914887 * 2 ^ 59
def prefixEnd_7914887 : Nat := 4983230072969 + 3 ^ 40 * 7914887 * 2
def baseEnd_7914887 : Nat := 150523753963802951922689

theorem tailTrace_7914887 : CollatzResearch.WordTrace tailWord_7914887 prefixEnd_7914887 150523753963802951922689 := by
  unfold tailWord_7914887
  simp only [CollatzResearch.WordTrace]
  refine ⟨288679644876723628925990915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192453096584482419283993943 288679644876723628925990915)
  ·
    refine ⟨433019467315085443388986373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288679644876723628925990915 433019467315085443388986373)
    ·
      refine ⟨81191150121578520635434945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433019467315085443388986373 81191150121578520635434945)
      ·
        refine ⟨60893362591183890476576209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81191150121578520635434945 60893362591183890476576209)
        ·
          refine ⟨45670021943387917857432157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60893362591183890476576209 45670021943387917857432157)
          ·
            refine ⟨17126258228770469196537059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45670021943387917857432157 17126258228770469196537059)
            ·
              refine ⟨25689387343155703794805589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126258228770469196537059 25689387343155703794805589)
              ·
                refine ⟨150523753963802951922689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25689387343155703794805589 150523753963802951922689)
                ·
                  rfl

theorem cell23_7914887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 9].length) (baseStart_7914887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914887 prefixEnd_7914887 := by exact prefixLift 7914887
  have htrace : WordTrace (prefixWord ++ tailWord_7914887) baseStart_7914887 baseEnd_7914887 := by
    simpa [prefixWord, tailWord_7914887, baseEnd_7914887] using wordTrace_append hprefix tailTrace_7914887
  have hstable : (prefixWord ++ tailWord_7914887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914887).length < 2 ^ (prefixWord ++ tailWord_7914887).sum := by decide
  have hdescent : baseEnd_7914887 < baseStart_7914887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914904 : List Nat := [2, 1, 2, 5, 2, 2, 9]
def baseStart_7914904 : Nat := 118140960795 + 7914904 * 2 ^ 59
def prefixEnd_7914904 : Nat := 4983230072969 + 3 ^ 40 * 7914904 * 2
def baseEnd_7914904 : Nat := 50174692422145754758025

theorem tailTrace_7914904 : CollatzResearch.WordTrace tailWord_7914904 prefixEnd_7914904 50174692422145754758025 := by
  unfold tailWord_7914904
  simp only [CollatzResearch.WordTrace]
  refine ⟨144340132458831020414679883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192453509945108027219573177 144340132458831020414679883)
  ·
    refine ⟨216510198688246530622019825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144340132458831020414679883 216510198688246530622019825)
    ·
      refine ⟨162382649016184897966514869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216510198688246530622019825 162382649016184897966514869)
      ·
        refine ⟨15223373345267334184360769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162382649016184897966514869 15223373345267334184360769)
        ·
          refine ⟨11417530008950500638270577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223373345267334184360769 11417530008950500638270577)
          ·
            refine ⟨8563147506712875478702933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417530008950500638270577 8563147506712875478702933)
            ·
              refine ⟨50174692422145754758025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8563147506712875478702933 50174692422145754758025)
              ·
                rfl

theorem cell23_7914904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 9].length) (baseStart_7914904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914904 prefixEnd_7914904 := by exact prefixLift 7914904
  have htrace : WordTrace (prefixWord ++ tailWord_7914904) baseStart_7914904 baseEnd_7914904 := by
    simpa [prefixWord, tailWord_7914904, baseEnd_7914904] using wordTrace_append hprefix tailTrace_7914904
  have hstable : (prefixWord ++ tailWord_7914904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914904).length < 2 ^ (prefixWord ++ tailWord_7914904).sum := by decide
  have hdescent : baseEnd_7914904 < baseStart_7914904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914915 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 1, 2, 2]
def baseStart_7914915 : Nat := 118140960795 + 7914915 * 2 ^ 59
def prefixEnd_7914915 : Nat := 4983230072969 + 3 ^ 40 * 7914915 * 2
def baseEnd_7914915 : Nat := 4064155734481005592362475

theorem tailTrace_7914915 : CollatzResearch.WordTrace tailWord_7914915 prefixEnd_7914915 4064155734481005592362475 := by
  unfold tailWord_7914915
  simp only [CollatzResearch.WordTrace]
  refine ⟨288680666120622189708010199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192453777413748126472006799 288680666120622189708010199)
  ·
    refine ⟨433020999180933284562015299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288680666120622189708010199 433020999180933284562015299)
    ·
      refine ⟨649531498771399926843022949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433020999180933284562015299 649531498771399926843022949)
      ·
        refine ⟨121787156019637486283066803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649531498771399926843022949 121787156019637486283066803)
        ·
          refine ⟨182680734029456229424600205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121787156019637486283066803 182680734029456229424600205)
          ·
            refine ⟨68505275261046086034225077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182680734029456229424600205 68505275261046086034225077)
            ·
              refine ⟨6422369555723070565708601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68505275261046086034225077 6422369555723070565708601)
              ·
                refine ⟨4816777166792302924281451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422369555723070565708601 4816777166792302924281451)
                ·
                  refine ⟨7225165750188454386422177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816777166792302924281451 7225165750188454386422177)
                  ·
                    refine ⟨5418874312641340789816633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225165750188454386422177 5418874312641340789816633)
                    ·
                      refine ⟨4064155734481005592362475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418874312641340789816633 4064155734481005592362475)
                      ·
                        rfl

theorem cell23_7914915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_7914915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914915 prefixEnd_7914915 := by exact prefixLift 7914915
  have htrace : WordTrace (prefixWord ++ tailWord_7914915) baseStart_7914915 baseEnd_7914915 := by
    simpa [prefixWord, tailWord_7914915, baseEnd_7914915] using wordTrace_append hprefix tailTrace_7914915
  have hstable : (prefixWord ++ tailWord_7914915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914915).length < 2 ^ (prefixWord ++ tailWord_7914915).sum := by decide
  have hdescent : baseEnd_7914915 < baseStart_7914915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914925 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7914925 : Nat := 118140960795 + 7914925 * 2 ^ 59
def prefixEnd_7914925 : Nat := 4983230072969 + 3 ^ 40 * 7914925 * 2
def baseEnd_7914925 : Nat := 1354720289762516851079143

theorem tailTrace_7914925 : CollatzResearch.WordTrace tailWord_7914925 prefixEnd_7914925 1354720289762516851079143 := by
  unfold tailWord_7914925
  simp only [CollatzResearch.WordTrace]
  refine ⟨288681030850585961415874229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192454020567057307610582819 288681030850585961415874229)
  ·
    refine ⟨27063846642242433882738209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288681030850585961415874229 27063846642242433882738209)
    ·
      refine ⟨20297884981681825412053657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27063846642242433882738209 20297884981681825412053657)
      ·
        refine ⟨15223413736261369059040243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20297884981681825412053657 15223413736261369059040243)
        ·
          refine ⟨22835120604392053588560365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223413736261369059040243 22835120604392053588560365)
          ·
            refine ⟨8563170226647020095710137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22835120604392053588560365 8563170226647020095710137)
            ·
              refine ⟨6422377669985265071782603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8563170226647020095710137 6422377669985265071782603)
              ·
                refine ⟨9633566504977897607673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422377669985265071782603 9633566504977897607673905)
                ·
                  refine ⟨7225174878733423205755429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633566504977897607673905 7225174878733423205755429)
                  ·
                    refine ⟨1354720289762516851079143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225174878733423205755429 1354720289762516851079143)
                    ·
                      rfl

theorem cell23_7914925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7914925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914925 prefixEnd_7914925 := by exact prefixLift 7914925
  have htrace : WordTrace (prefixWord ++ tailWord_7914925) baseStart_7914925 baseEnd_7914925 := by
    simpa [prefixWord, tailWord_7914925, baseEnd_7914925] using wordTrace_append hprefix tailTrace_7914925
  have hstable : (prefixWord ++ tailWord_7914925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914925).length < 2 ^ (prefixWord ++ tailWord_7914925).sum := by decide
  have hdescent : baseEnd_7914925 < baseStart_7914925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914941 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7914941 : Nat := 118140960795 + 7914941 * 2 ^ 59
def prefixEnd_7914941 : Nat := 4983230072969 + 3 ^ 40 * 7914941 * 2
def baseEnd_7914941 : Nat := 4064169084978022490637355

theorem tailTrace_7914941 : CollatzResearch.WordTrace tailWord_7914941 prefixEnd_7914941 4064169084978022490637355 := by
  unfold tailWord_7914941
  simp only [CollatzResearch.WordTrace]
  refine ⟨288681614418527996148456677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192454409612351997432304451 288681614418527996148456677)
  ·
    refine ⟨54127802703473999277835627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288681614418527996148456677 54127802703473999277835627)
    ·
      refine ⟨81191704055210998916753441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54127802703473999277835627 81191704055210998916753441)
      ·
        refine ⟨60893778041408249187565081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81191704055210998916753441 60893778041408249187565081)
        ·
          refine ⟨45670333531056186890673811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60893778041408249187565081 45670333531056186890673811)
          ·
            refine ⟨68505500296584280336010717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45670333531056186890673811 68505500296584280336010717)
            ·
              refine ⟨25689562611219105126004019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68505500296584280336010717 25689562611219105126004019)
              ·
                refine ⟨38534343916828657689006029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689562611219105126004019 38534343916828657689006029)
                ·
                  refine ⟨14450378968810746633377261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38534343916828657689006029 14450378968810746633377261)
                  ·
                    refine ⟨5418892113304029987516473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14450378968810746633377261 5418892113304029987516473)
                    ·
                      refine ⟨4064169084978022490637355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418892113304029987516473 4064169084978022490637355)
                      ·
                        rfl

theorem cell23_7914941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7914941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914941 prefixEnd_7914941 := by exact prefixLift 7914941
  have htrace : WordTrace (prefixWord ++ tailWord_7914941) baseStart_7914941 baseEnd_7914941 := by
    simpa [prefixWord, tailWord_7914941, baseEnd_7914941] using wordTrace_append hprefix tailTrace_7914941
  have hstable : (prefixWord ++ tailWord_7914941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914941).length < 2 ^ (prefixWord ++ tailWord_7914941).sum := by decide
  have hdescent : baseEnd_7914941 < baseStart_7914941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914967 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7914967 : Nat := 118140960795 + 7914967 * 2 ^ 59
def prefixEnd_7914967 : Nat := 4983230072969 + 3 ^ 40 * 7914967 * 2
def baseEnd_7914967 : Nat := 4064182435475039388912235

theorem tailTrace_7914967 : CollatzResearch.WordTrace tailWord_7914967 prefixEnd_7914967 4064182435475039388912235 := by
  unfold tailWord_7914967
  simp only [CollatzResearch.WordTrace]
  refine ⟨288682562716433802588903155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192455041810955868392602103 288682562716433802588903155)
  ·
    refine ⟨433023844074650703883354733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288682562716433802588903155 433023844074650703883354733)
    ·
      refine ⟨162383941527994013956258025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433023844074650703883354733 162383941527994013956258025)
      ·
        refine ⟨121787956145995510467193519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162383941527994013956258025 121787956145995510467193519)
        ·
          refine ⟨182681934218993265700790279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121787956145995510467193519 182681934218993265700790279)
          ·
            refine ⟨274022901328489898551185419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182681934218993265700790279 274022901328489898551185419)
            ·
              refine ⟨411034351992734847826778129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274022901328489898551185419 411034351992734847826778129)
              ·
                refine ⟨308275763994551135870083597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411034351992734847826778129 308275763994551135870083597)
                ·
                  refine ⟨115603411497956675951281349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308275763994551135870083597 115603411497956675951281349)
                  ·
                    refine ⟨21675639655866876740865253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115603411497956675951281349 21675639655866876740865253)
                    ·
                      refine ⟨4064182435475039388912235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21675639655866876740865253 4064182435475039388912235)
                      ·
                        rfl

theorem cell23_7914967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7914967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914967 prefixEnd_7914967 := by exact prefixLift 7914967
  have htrace : WordTrace (prefixWord ++ tailWord_7914967) baseStart_7914967 baseEnd_7914967 := by
    simpa [prefixWord, tailWord_7914967, baseEnd_7914967] using wordTrace_append hprefix tailTrace_7914967
  have hstable : (prefixWord ++ tailWord_7914967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914967).length < 2 ^ (prefixWord ++ tailWord_7914967).sum := by decide
  have hdescent : baseEnd_7914967 < baseStart_7914967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914984 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7914984 : Nat := 118140960795 + 7914984 * 2 ^ 59
def prefixEnd_7914984 : Nat := 4983230072969 + 3 ^ 40 * 7914984 * 2
def baseEnd_7914984 : Nat := 4064191164646165822399657

theorem tailTrace_7914984 : CollatzResearch.WordTrace tailWord_7914984 prefixEnd_7914984 4064191164646165822399657 := by
  unfold tailWord_7914984
  simp only [CollatzResearch.WordTrace]
  refine ⟨144341591378686107246136003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192455455171581476328181337 144341591378686107246136003)
  ·
    refine ⟨216512387068029160869204005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144341591378686107246136003 216512387068029160869204005)
    ·
      refine ⟨40596072575255467662975751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216512387068029160869204005 40596072575255467662975751)
      ·
        refine ⟨60894108862883201494463627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40596072575255467662975751 60894108862883201494463627)
        ·
          refine ⟨91341163294324802241695441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60894108862883201494463627 91341163294324802241695441)
          ·
            refine ⟨68505872470743601681271581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91341163294324802241695441 68505872470743601681271581)
            ·
              refine ⟨25689702176528850630476843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68505872470743601681271581 25689702176528850630476843)
              ·
                refine ⟨38534553264793275945715265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689702176528850630476843 38534553264793275945715265)
                ·
                  refine ⟨28900914948594956959286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38534553264793275945715265 28900914948594956959286449)
                  ·
                    refine ⟨21675686211446217719464837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28900914948594956959286449 21675686211446217719464837)
                    ·
                      refine ⟨4064191164646165822399657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21675686211446217719464837 4064191164646165822399657)
                      ·
                        rfl

theorem cell23_7914984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7914984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914984 prefixEnd_7914984 := by exact prefixLift 7914984
  have htrace : WordTrace (prefixWord ++ tailWord_7914984) baseStart_7914984 baseEnd_7914984 := by
    simpa [prefixWord, tailWord_7914984, baseEnd_7914984] using wordTrace_append hprefix tailTrace_7914984
  have hstable : (prefixWord ++ tailWord_7914984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914984).length < 2 ^ (prefixWord ++ tailWord_7914984).sum := by decide
  have hdescent : baseEnd_7914984 < baseStart_7914984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7914994 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_7914994 : Nat := 118140960795 + 7914994 * 2 ^ 59
def prefixEnd_7914994 : Nat := 4983230072969 + 3 ^ 40 * 7914994 * 2
def baseEnd_7914994 : Nat := 451577366605856753697179

theorem tailTrace_7914994 : CollatzResearch.WordTrace tailWord_7914994 prefixEnd_7914994 451577366605856753697179 := by
  unfold tailWord_7914994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72170886871833996550034009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192455698324890657466757357 72170886871833996550034009)
  ·
    refine ⟨54128165153875497412525507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72170886871833996550034009 54128165153875497412525507)
    ·
      refine ⟨81192247730813246118788261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54128165153875497412525507 81192247730813246118788261)
      ·
        refine ⟨15223546449527483647272799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81192247730813246118788261 15223546449527483647272799)
        ·
          refine ⟨22835319674291225470909199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223546449527483647272799 22835319674291225470909199)
          ·
            refine ⟨34252979511436838206363799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22835319674291225470909199 34252979511436838206363799)
            ·
              refine ⟨51379469267155257309545699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34252979511436838206363799 51379469267155257309545699)
              ·
                refine ⟨77069203900732885964318549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51379469267155257309545699 77069203900732885964318549)
                ·
                  refine ⟨451577366605856753697179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77069203900732885964318549 451577366605856753697179)
                  ·
                    rfl

theorem cell23_7914994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_7914994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7914994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7914994 prefixEnd_7914994 := by exact prefixLift 7914994
  have htrace : WordTrace (prefixWord ++ tailWord_7914994) baseStart_7914994 baseEnd_7914994 := by
    simpa [prefixWord, tailWord_7914994, baseEnd_7914994] using wordTrace_append hprefix tailTrace_7914994
  have hstable : (prefixWord ++ tailWord_7914994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7914994).length < 2 ^ (prefixWord ++ tailWord_7914994).sum := by decide
  have hdescent : baseEnd_7914994 < baseStart_7914994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7914994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915022 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7915022 : Nat := 118140960795 + 7915022 * 2 ^ 59
def prefixEnd_7915022 : Nat := 4983230072969 + 3 ^ 40 * 7915022 * 2
def baseEnd_7915022 : Nat := 4064210676911036673724483

theorem tailTrace_7915022 : CollatzResearch.WordTrace tailWord_7915022 prefixEnd_7915022 4064210676911036673724483 := by
  unfold tailWord_7915022
  simp only [CollatzResearch.WordTrace]
  refine ⟨36085571091404318372769415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192456379154156364654770213 36085571091404318372769415)
  ·
    refine ⟨54128356637106477559154123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36085571091404318372769415 54128356637106477559154123)
    ·
      refine ⟨81192534955659716338731185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54128356637106477559154123 81192534955659716338731185)
      ·
        refine ⟨60894401216744787254048389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81192534955659716338731185 60894401216744787254048389)
        ·
          refine ⟨11417700228139647610134073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60894401216744787254048389 11417700228139647610134073)
          ·
            refine ⟨8563275171104735707600555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417700228139647610134073 8563275171104735707600555)
            ·
              refine ⟨12844912756657103561400833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563275171104735707600555 12844912756657103561400833)
              ·
                refine ⟨9633684567492827671050625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844912756657103561400833 9633684567492827671050625)
                ·
                  refine ⟨7225263425619620753287969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633684567492827671050625 7225263425619620753287969)
                  ·
                    refine ⟨5418947569214715564965977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225263425619620753287969 5418947569214715564965977)
                    ·
                      refine ⟨4064210676911036673724483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5418947569214715564965977 4064210676911036673724483)
                      ·
                        rfl

theorem cell23_7915022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7915022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915022 prefixEnd_7915022 := by exact prefixLift 7915022
  have htrace : WordTrace (prefixWord ++ tailWord_7915022) baseStart_7915022 baseEnd_7915022 := by
    simpa [prefixWord, tailWord_7915022, baseEnd_7915022] using wordTrace_append hprefix tailTrace_7915022
  have hstable : (prefixWord ++ tailWord_7915022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915022).length < 2 ^ (prefixWord ++ tailWord_7915022).sum := by decide
  have hdescent : baseEnd_7915022 < baseStart_7915022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915028 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 7]
def baseStart_7915028 : Nat := 118140960795 + 7915028 * 2 ^ 59
def prefixEnd_7915028 : Nat := 4983230072969 + 3 ^ 40 * 7915028 * 2
def baseEnd_7915028 : Nat := 451579306421662627805495

theorem tailTrace_7915028 : CollatzResearch.WordTrace tailWord_7915028 prefixEnd_7915028 451579306421662627805495 := by
  unfold tailWord_7915028
  simp only [CollatzResearch.WordTrace]
  refine ⟨144342393784606405003436869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192456525046141873337915825 144342393784606405003436869)
  ·
    refine ⟨27064198834613700938144413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144342393784606405003436869 27064198834613700938144413)
    ·
      refine ⟨10149074562980137851804155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27064198834613700938144413 10149074562980137851804155)
      ·
        refine ⟨15223611844470206777706233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10149074562980137851804155 15223611844470206777706233)
        ·
          refine ⟨11417708883352655083279675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223611844470206777706233 11417708883352655083279675)
          ·
            refine ⟨17126563325028982624919513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417708883352655083279675 17126563325028982624919513)
            ·
              refine ⟨12844922493771736968689635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126563325028982624919513 12844922493771736968689635)
              ·
                refine ⟨19267383740657605453034453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844922493771736968689635 19267383740657605453034453)
                ·
                  refine ⟨451579306421662627805495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19267383740657605453034453 451579306421662627805495)
                  ·
                    rfl

theorem cell23_7915028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_7915028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915028 prefixEnd_7915028 := by exact prefixLift 7915028
  have htrace : WordTrace (prefixWord ++ tailWord_7915028) baseStart_7915028 baseEnd_7915028 := by
    simpa [prefixWord, tailWord_7915028, baseEnd_7915028] using wordTrace_append hprefix tailTrace_7915028
  have hstable : (prefixWord ++ tailWord_7915028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915028).length < 2 ^ (prefixWord ++ tailWord_7915028).sum := by decide
  have hdescent : baseEnd_7915028 < baseStart_7915028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915062 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_7915062 : Nat := 118140960795 + 7915062 * 2 ^ 59
def prefixEnd_7915062 : Nat := 4983230072969 + 3 ^ 40 * 7915062 * 2
def baseEnd_7915062 : Nat := 451581246237468501913811

theorem tailTrace_7915062 : CollatzResearch.WordTrace tailWord_7915062 prefixEnd_7915062 451581246237468501913811 := by
  unfold tailWord_7915062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042876728193102113350715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192457351767393089209074293 18042876728193102113350715)
  ·
    refine ⟨27064315092289653170026073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042876728193102113350715 27064315092289653170026073)
    ·
      refine ⟨20298236319217239877519555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27064315092289653170026073 20298236319217239877519555)
      ·
        refine ⟨30447354478825859816279333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20298236319217239877519555 30447354478825859816279333)
        ·
          refine ⟨5708878964779848715552375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30447354478825859816279333 5708878964779848715552375)
          ·
            refine ⟨8563318447169773073328563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708878964779848715552375 8563318447169773073328563)
            ·
              refine ⟨12844977670754659609992845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563318447169773073328563 12844977670754659609992845)
              ·
                refine ⟨4816866626532997353747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12844977670754659609992845 4816866626532997353747317)
                ·
                  refine ⟨451581246237468501913811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816866626532997353747317 451581246237468501913811)
                  ·
                    rfl

theorem cell23_7915062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_7915062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915062 prefixEnd_7915062 := by exact prefixLift 7915062
  have htrace : WordTrace (prefixWord ++ tailWord_7915062) baseStart_7915062 baseEnd_7915062 := by
    simpa [prefixWord, tailWord_7915062, baseEnd_7915062] using wordTrace_append hprefix tailTrace_7915062
  have hstable : (prefixWord ++ tailWord_7915062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915062).length < 2 ^ (prefixWord ++ tailWord_7915062).sum := by decide
  have hdescent : baseEnd_7915062 < baseStart_7915062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915084 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 8]
def baseStart_7915084 : Nat := 118140960795 + 7915084 * 2 ^ 59
def prefixEnd_7915084 : Nat := 4983230072969 + 3 ^ 40 * 7915084 * 2
def baseEnd_7915084 : Nat := 451582501412401714572133

theorem tailTrace_7915084 : CollatzResearch.WordTrace tailWord_7915084 prefixEnd_7915084 451582501412401714572133 := by
  unfold tailWord_7915084
  simp only [CollatzResearch.WordTrace]
  refine ⟨144343415028504965785456153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192457886704673287713941537 144343415028504965785456153)
  ·
    refine ⟨108257561271378724339092115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144343415028504965785456153 108257561271378724339092115)
    ·
      refine ⟨162386341907068086508638173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108257561271378724339092115 162386341907068086508638173)
      ·
        refine ⟨60894878215150532440739315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162386341907068086508638173 60894878215150532440739315)
        ·
          refine ⟨91342317322725798661108973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60894878215150532440739315 91342317322725798661108973)
          ·
            refine ⟨34253368996022174497915865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91342317322725798661108973 34253368996022174497915865)
            ·
              refine ⟨25690026747016630873436899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34253368996022174497915865 25690026747016630873436899)
              ·
                refine ⟨38535040120524946310155349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25690026747016630873436899 38535040120524946310155349)
                ·
                  refine ⟨451582501412401714572133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38535040120524946310155349 451582501412401714572133)
                  ·
                    rfl

theorem cell23_7915084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_7915084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915084 prefixEnd_7915084 := by exact prefixLift 7915084
  have htrace : WordTrace (prefixWord ++ tailWord_7915084) baseStart_7915084 baseEnd_7915084 := by
    simpa [prefixWord, tailWord_7915084, baseEnd_7915084] using wordTrace_append hprefix tailTrace_7915084
  have hstable : (prefixWord ++ tailWord_7915084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915084).length < 2 ^ (prefixWord ++ tailWord_7915084).sum := by decide
  have hdescent : baseEnd_7915084 < baseStart_7915084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915121 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_7915121 : Nat := 118140960795 + 7915121 * 2 ^ 59
def prefixEnd_7915121 : Nat := 4983230072969 + 3 ^ 40 * 7915121 * 2
def baseEnd_7915121 : Nat := 4064261511495831786386527

theorem tailTrace_7915121 : CollatzResearch.WordTrace tailWord_7915121 prefixEnd_7915121 4064261511495831786386527 := by
  unfold tailWord_7915121
  simp only [CollatzResearch.WordTrace]
  refine ⟨288688179557875886890009217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192458786371917257926672811 288688179557875886890009217)
  ·
    refine ⟨216516134668406915167506913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288688179557875886890009217 216516134668406915167506913)
    ·
      refine ⟨162387101001305186375630185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216516134668406915167506913 162387101001305186375630185)
      ·
        refine ⟨121790325750978889781722639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162387101001305186375630185 121790325750978889781722639)
        ·
          refine ⟨182685488626468334672583959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121790325750978889781722639 182685488626468334672583959)
          ·
            refine ⟨274028232939702502008875939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182685488626468334672583959 274028232939702502008875939)
            ·
              refine ⟨411042349409553753013313909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274028232939702502008875939 411042349409553753013313909)
              ·
                refine ⟨38535220257145664344998179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411042349409553753013313909 38535220257145664344998179)
                ·
                  refine ⟨57802830385718496517497269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38535220257145664344998179 57802830385718496517497269)
                  ·
                    refine ⟨5419015348661109048515369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57802830385718496517497269 5419015348661109048515369)
                    ·
                      refine ⟨4064261511495831786386527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419015348661109048515369 4064261511495831786386527)
                      ·
                        rfl

theorem cell23_7915121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_7915121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915121 prefixEnd_7915121 := by exact prefixLift 7915121
  have htrace : WordTrace (prefixWord ++ tailWord_7915121) baseStart_7915121 baseEnd_7915121 := by
    simpa [prefixWord, tailWord_7915121, baseEnd_7915121] using wordTrace_append hprefix tailTrace_7915121
  have hstable : (prefixWord ++ tailWord_7915121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915121).length < 2 ^ (prefixWord ++ tailWord_7915121).sum := by decide
  have hdescent : baseEnd_7915121 < baseStart_7915121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915171 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3]
def baseStart_7915171 : Nat := 118140960795 + 7915171 * 2 ^ 59
def prefixEnd_7915171 : Nat := 4983230072969 + 3 ^ 40 * 7915171 * 2
def baseEnd_7915171 : Nat := 4064287185528556590761297

theorem tailTrace_7915171 : CollatzResearch.WordTrace tailWord_7915171 prefixEnd_7915171 4064287185528556590761297 := by
  unfold tailWord_7915171
  simp only [CollatzResearch.WordTrace]
  refine ⟨288690003207694745429329367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192460002138463163619552911 288690003207694745429329367)
  ·
    refine ⟨433035004811542118143994051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288690003207694745429329367 433035004811542118143994051)
    ·
      refine ⟨649552507217313177215991077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433035004811542118143994051 649552507217313177215991077)
      ·
        refine ⟨121791095103246220727998327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649552507217313177215991077 121791095103246220727998327)
        ·
          refine ⟨182686642654869331091997491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121791095103246220727998327 182686642654869331091997491)
          ·
            refine ⟨274029963982303996637996237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182686642654869331091997491 274029963982303996637996237)
            ·
              refine ⟨102761236493363998739248589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274029963982303996637996237 102761236493363998739248589)
              ·
                refine ⟨38535463685011499527218221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102761236493363998739248589 38535463685011499527218221)
                ·
                  refine ⟨14450798881879312322706833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38535463685011499527218221 14450798881879312322706833)
                  ·
                    refine ⟨10838099161409484242030125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14450798881879312322706833 10838099161409484242030125)
                    ·
                      refine ⟨4064287185528556590761297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838099161409484242030125 4064287185528556590761297)
                      ·
                        rfl

theorem cell23_7915171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_7915171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915171 prefixEnd_7915171 := by exact prefixLift 7915171
  have htrace : WordTrace (prefixWord ++ tailWord_7915171) baseStart_7915171 baseEnd_7915171 := by
    simpa [prefixWord, tailWord_7915171, baseEnd_7915171] using wordTrace_append hprefix tailTrace_7915171
  have hstable : (prefixWord ++ tailWord_7915171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915171).length < 2 ^ (prefixWord ++ tailWord_7915171).sum := by decide
  have hdescent : baseEnd_7915171 < baseStart_7915171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915212 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_7915212 : Nat := 118140960795 + 7915212 * 2 ^ 59
def prefixEnd_7915212 : Nat := 4983230072969 + 3 ^ 40 * 7915212 * 2
def baseEnd_7915212 : Nat := 1354769412745130310116203

theorem tailTrace_7915212 : CollatzResearch.WordTrace tailWord_7915212 prefixEnd_7915212 1354769412745130310116203 := by
  unfold tailWord_7915212
  simp only [CollatzResearch.WordTrace]
  refine ⟨144345749300273104715785945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192460999067030806287714593 144345749300273104715785945)
  ·
    refine ⟨108259311975204828536839459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144345749300273104715785945 108259311975204828536839459)
    ·
      refine ⟨162388967962807242805259189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108259311975204828536839459 162388967962807242805259189)
      ·
        refine ⟨15223965746513179012993049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162388967962807242805259189 15223965746513179012993049)
        ·
          refine ⟨11417974309884884259744787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223965746513179012993049 11417974309884884259744787)
          ·
            refine ⟨17126961464827326389617181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417974309884884259744787 17126961464827326389617181)
            ·
              refine ⟨6422610549310247396106443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17126961464827326389617181 6422610549310247396106443)
              ·
                refine ⟨9633915823965371094159665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422610549310247396106443 9633915823965371094159665)
                ·
                  refine ⟨7225436867974028320619749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633915823965371094159665 7225436867974028320619749)
                  ·
                    refine ⟨1354769412745130310116203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225436867974028320619749 1354769412745130310116203)
                    ·
                      rfl

theorem cell23_7915212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_7915212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915212 prefixEnd_7915212 := by exact prefixLift 7915212
  have htrace : WordTrace (prefixWord ++ tailWord_7915212) baseStart_7915212 baseEnd_7915212 := by
    simpa [prefixWord, tailWord_7915212, baseEnd_7915212] using wordTrace_append hprefix tailTrace_7915212
  have hstable : (prefixWord ++ tailWord_7915212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915212).length < 2 ^ (prefixWord ++ tailWord_7915212).sum := by decide
  have hdescent : baseEnd_7915212 < baseStart_7915212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915270 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7915270 : Nat := 118140960795 + 7915270 * 2 ^ 59
def prefixEnd_7915270 : Nat := 4983230072969 + 3 ^ 40 * 7915270 * 2
def baseEnd_7915270 : Nat := 4064338020113351703423343

theorem tailTrace_7915270 : CollatzResearch.WordTrace tailWord_7915270 prefixEnd_7915270 4064338020113351703423343 := by
  unfold tailWord_7915270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021675438573002666786977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192462409356224056891455509 9021675438573002666786977)
  ·
    refine ⟨6766256578929752000090233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9021675438573002666786977 6766256578929752000090233)
    ·
      refine ⟨5074692434197314000067675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6766256578929752000090233 5074692434197314000067675)
      ·
        refine ⟨7612038651295971000101513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074692434197314000067675 7612038651295971000101513)
        ·
          refine ⟨5709028988471978250076135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7612038651295971000101513 5709028988471978250076135)
          ·
            refine ⟨8563543482707967375114203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709028988471978250076135 8563543482707967375114203)
            ·
              refine ⟨12845315224061951062671305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563543482707967375114203 12845315224061951062671305)
              ·
                refine ⟨9633986418046463297003479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12845315224061951062671305 9633986418046463297003479)
                ·
                  refine ⟨14450979627069694945505219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633986418046463297003479 14450979627069694945505219)
                  ·
                    refine ⟨21676469440604542418257829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14450979627069694945505219 21676469440604542418257829)
                    ·
                      refine ⟨4064338020113351703423343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21676469440604542418257829 4064338020113351703423343)
                      ·
                        rfl

theorem cell23_7915270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7915270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915270 prefixEnd_7915270 := by exact prefixLift 7915270
  have htrace : WordTrace (prefixWord ++ tailWord_7915270) baseStart_7915270 baseEnd_7915270 := by
    simpa [prefixWord, tailWord_7915270, baseEnd_7915270] using wordTrace_append hprefix tailTrace_7915270
  have hstable : (prefixWord ++ tailWord_7915270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915270).length < 2 ^ (prefixWord ++ tailWord_7915270).sum := by decide
  have hdescent : baseEnd_7915270 < baseStart_7915270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915291 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3]
def baseStart_7915291 : Nat := 118140960795 + 7915291 * 2 ^ 59
def prefixEnd_7915291 : Nat := 4983230072969 + 3 ^ 40 * 7915291 * 2
def baseEnd_7915291 : Nat := 4064348803207096121260745

theorem tailTrace_7915291 : CollatzResearch.WordTrace tailWord_7915291 prefixEnd_7915291 4064348803207096121260745 := by
  unfold tailWord_7915291
  simp only [CollatzResearch.WordTrace]
  refine ⟨288694379967260005923697727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192462919978173337282465151 288694379967260005923697727)
  ·
    refine ⟨433041569950890008885546591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288694379967260005923697727 433041569950890008885546591)
    ·
      refine ⟨649562354926335013328319887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433041569950890008885546591 649562354926335013328319887)
      ·
        refine ⟨974343532389502519992479831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649562354926335013328319887 974343532389502519992479831)
        ·
          refine ⟨1461515298584253779988719747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974343532389502519992479831 1461515298584253779988719747)
          ·
            refine ⟨2192272947876380669983079621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461515298584253779988719747 2192272947876380669983079621)
            ·
              refine ⟨411051177726821375621827429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2192272947876380669983079621 411051177726821375621827429)
              ·
                refine ⟨77072095823779007929092643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411051177726821375621827429 77072095823779007929092643)
                ·
                  refine ⟨115608143735668511893638965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77072095823779007929092643 115608143735668511893638965)
                  ·
                    refine ⟨10838263475218922990028653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115608143735668511893638965 10838263475218922990028653)
                    ·
                      refine ⟨4064348803207096121260745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838263475218922990028653 4064348803207096121260745)
                      ·
                        rfl

theorem cell23_7915291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].length) (baseStart_7915291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915291 prefixEnd_7915291 := by exact prefixLift 7915291
  have htrace : WordTrace (prefixWord ++ tailWord_7915291) baseStart_7915291 baseEnd_7915291 := by
    simpa [prefixWord, tailWord_7915291, baseEnd_7915291] using wordTrace_append hprefix tailTrace_7915291
  have hstable : (prefixWord ++ tailWord_7915291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915291).length < 2 ^ (prefixWord ++ tailWord_7915291).sum := by decide
  have hdescent : baseEnd_7915291 < baseStart_7915291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915315 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 5]
def baseStart_7915315 : Nat := 118140960795 + 7915315 * 2 ^ 59
def prefixEnd_7915315 : Nat := 4983230072969 + 3 ^ 40 * 7915315 * 2
def baseEnd_7915315 : Nat := 451595680749200447484515

theorem tailTrace_7915315 : CollatzResearch.WordTrace tailWord_7915315 prefixEnd_7915315 451595680749200447484515 := by
  unfold tailWord_7915315
  simp only [CollatzResearch.WordTrace]
  refine ⟨288695255319173058022571399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192463503546115372015047599 288695255319173058022571399)
  ·
    refine ⟨433042882978759587033857099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288695255319173058022571399 433042882978759587033857099)
    ·
      refine ⟨649564324468139380550785649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433042882978759587033857099 649564324468139380550785649)
      ·
        refine ⟨487173243351104535413089237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649564324468139380550785649 487173243351104535413089237)
        ·
          refine ⟨11418122891041512548744279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 487173243351104535413089237 11418122891041512548744279)
          ·
            refine ⟨17127184336562268823116419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418122891041512548744279 17127184336562268823116419)
            ·
              refine ⟨25690776504843403234674629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127184336562268823116419 25690776504843403234674629)
              ·
                refine ⟨4817020594658138106501493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25690776504843403234674629 4817020594658138106501493)
                ·
                  refine ⟨451595680749200447484515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4817020594658138106501493 451595680749200447484515)
                  ·
                    rfl

theorem cell23_7915315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 5].length) (baseStart_7915315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915315 prefixEnd_7915315 := by exact prefixLift 7915315
  have htrace : WordTrace (prefixWord ++ tailWord_7915315) baseStart_7915315 baseEnd_7915315 := by
    simpa [prefixWord, tailWord_7915315, baseEnd_7915315] using wordTrace_append hprefix tailTrace_7915315
  have hstable : (prefixWord ++ tailWord_7915315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915315).length < 2 ^ (prefixWord ++ tailWord_7915315).sum := by decide
  have hdescent : baseEnd_7915315 < baseStart_7915315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915325 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7915325 : Nat := 118140960795 + 7915325 * 2 ^ 59
def prefixEnd_7915325 : Nat := 4983230072969 + 3 ^ 40 * 7915325 * 2
def baseEnd_7915325 : Nat := 4064366261549348988235589

theorem tailTrace_7915325 : CollatzResearch.WordTrace tailWord_7915325 prefixEnd_7915325 4064366261549348988235589 := by
  unfold tailWord_7915325
  simp only [CollatzResearch.WordTrace]
  refine ⟨288695620049136829730435429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192463746699424553153623619 288695620049136829730435429)
  ·
    refine ⟨54130428759213155574456643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288695620049136829730435429 54130428759213155574456643)
    ·
      refine ⟨81195643138819733361684965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54130428759213155574456643 81195643138819733361684965)
      ·
        refine ⟨15224183088528700005315931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81195643138819733361684965 15224183088528700005315931)
        ·
          refine ⟨22836274632793050007973897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15224183088528700005315931 22836274632793050007973897)
          ·
            refine ⟨17127205974594787505980423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22836274632793050007973897 17127205974594787505980423)
            ·
              refine ⟨25690808961892181258970635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127205974594787505980423 25690808961892181258970635)
              ·
                refine ⟨38536213442838271888455953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25690808961892181258970635 38536213442838271888455953)
                ·
                  refine ⟨28902160082128703916341965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38536213442838271888455953 28902160082128703916341965)
                  ·
                    refine ⟨10838310030798263968628237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28902160082128703916341965 10838310030798263968628237)
                    ·
                      refine ⟨4064366261549348988235589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838310030798263968628237 4064366261549348988235589)
                      ·
                        rfl

theorem cell23_7915325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7915325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915325 prefixEnd_7915325 := by exact prefixLift 7915325
  have htrace : WordTrace (prefixWord ++ tailWord_7915325) baseStart_7915325 baseEnd_7915325 := by
    simpa [prefixWord, tailWord_7915325, baseEnd_7915325] using wordTrace_append hprefix tailTrace_7915325
  have hstable : (prefixWord ++ tailWord_7915325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915325).length < 2 ^ (prefixWord ++ tailWord_7915325).sum := by decide
  have hdescent : baseEnd_7915325 < baseStart_7915325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915345 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_7915345 : Nat := 118140960795 + 7915345 * 2 ^ 59
def prefixEnd_7915345 : Nat := 4983230072969 + 3 ^ 40 * 7915345 * 2
def baseEnd_7915345 : Nat := 1354792177054146303328499

theorem tailTrace_7915345 : CollatzResearch.WordTrace tailWord_7915345 prefixEnd_7915345 1354792177054146303328499 := by
  unfold tailWord_7915345
  simp only [CollatzResearch.WordTrace]
  refine ⟨288696349509064373146163489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192464233006042915430775659 288696349509064373146163489)
  ·
    refine ⟨216522262131798279859622617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288696349509064373146163489 216522262131798279859622617)
    ·
      refine ⟨162391696598848709894716963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216522262131798279859622617 162391696598848709894716963)
      ·
        refine ⟨243587544898273064842075445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162391696598848709894716963 243587544898273064842075445)
        ·
          refine ⟨22836332334213099828944573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243587544898273064842075445 22836332334213099828944573)
          ·
            refine ⟨8563624625329912435854215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22836332334213099828944573 8563624625329912435854215)
            ·
              refine ⟨12845436937994868653781323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563624625329912435854215 12845436937994868653781323)
              ·
                refine ⟨19268155406992302980671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845436937994868653781323 19268155406992302980671985)
                ·
                  refine ⟨14451116555244227235503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19268155406992302980671985 14451116555244227235503989)
                  ·
                    refine ⟨1354792177054146303328499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14451116555244227235503989 1354792177054146303328499)
                    ·
                      rfl

theorem cell23_7915345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_7915345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915345 prefixEnd_7915345 := by exact prefixLift 7915345
  have htrace : WordTrace (prefixWord ++ tailWord_7915345) baseStart_7915345 baseEnd_7915345 := by
    simpa [prefixWord, tailWord_7915345, baseEnd_7915345] using wordTrace_append hprefix tailTrace_7915345
  have hstable : (prefixWord ++ tailWord_7915345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915345).length < 2 ^ (prefixWord ++ tailWord_7915345).sum := by decide
  have hdescent : baseEnd_7915345 < baseStart_7915345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915361 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7915361 : Nat := 118140960795 + 7915361 * 2 ^ 59
def prefixEnd_7915361 : Nat := 4983230072969 + 3 ^ 40 * 7915361 * 2
def baseEnd_7915361 : Nat := 4064384746852910847385423

theorem tailTrace_7915361 : CollatzResearch.WordTrace tailWord_7915361 prefixEnd_7915361 4064384746852910847385423 := by
  unfold tailWord_7915361
  simp only [CollatzResearch.WordTrace]
  refine ⟨288696933077006407878745937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192464622051337605252497291 288696933077006407878745937)
  ·
    refine ⟨216522699807754805909059453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288696933077006407878745937 216522699807754805909059453)
    ·
      refine ⟨81196012427908052215897295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216522699807754805909059453 81196012427908052215897295)
      ·
        refine ⟨121794018641862078323845943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81196012427908052215897295 121794018641862078323845943)
        ·
          refine ⟨182691027962793117485768915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121794018641862078323845943 182691027962793117485768915)
          ·
            refine ⟨274036541944189676228653373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182691027962793117485768915 274036541944189676228653373)
            ·
              refine ⟨102763703229071128585745015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274036541944189676228653373 102763703229071128585745015)
              ·
                refine ⟨154145554843606692878617523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102763703229071128585745015 154145554843606692878617523)
                ·
                  refine ⟨231218332265410039317926285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154145554843606692878617523 231218332265410039317926285)
                  ·
                    refine ⟨86706874599528764744222357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231218332265410039317926285 86706874599528764744222357)
                    ·
                      refine ⟨4064384746852910847385423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86706874599528764744222357 4064384746852910847385423)
                      ·
                        rfl

theorem cell23_7915361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7915361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915361 prefixEnd_7915361 := by exact prefixLift 7915361
  have htrace : WordTrace (prefixWord ++ tailWord_7915361) baseStart_7915361 baseEnd_7915361 := by
    simpa [prefixWord, tailWord_7915361, baseEnd_7915361] using wordTrace_append hprefix tailTrace_7915361
  have hstable : (prefixWord ++ tailWord_7915361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915361).length < 2 ^ (prefixWord ++ tailWord_7915361).sum := by decide
  have hdescent : baseEnd_7915361 < baseStart_7915361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915391 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_7915391 : Nat := 118140960795 + 7915391 * 2 ^ 59
def prefixEnd_7915391 : Nat := 4983230072969 + 3 ^ 40 * 7915391 * 2
def baseEnd_7915391 : Nat := 4064400151272545730010285

theorem tailTrace_7915391 : CollatzResearch.WordTrace tailWord_7915391 prefixEnd_7915391 4064400151272545730010285 := by
  unfold tailWord_7915391
  simp only [CollatzResearch.WordTrace]
  refine ⟨288698027266897723002338027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192465351511265148668225351 288698027266897723002338027)
  ·
    refine ⟨433047040900346584503507041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288698027266897723002338027 433047040900346584503507041)
    ·
      refine ⟨324785280675259938377630281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433047040900346584503507041 324785280675259938377630281)
      ·
        refine ⟨243588960506444953783222711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324785280675259938377630281 243588960506444953783222711)
        ·
          refine ⟨365383440759667430674834067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243588960506444953783222711 365383440759667430674834067)
          ·
            refine ⟨548075161139501146012251101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365383440759667430674834067 548075161139501146012251101)
            ·
              refine ⟨205528185427312929754594163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548075161139501146012251101 205528185427312929754594163)
              ·
                refine ⟨308292278140969394631891245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205528185427312929754594163 308292278140969394631891245)
                ·
                  refine ⟨115609604302863522986959217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308292278140969394631891245 115609604302863522986959217)
                  ·
                    refine ⟨86707203227147642240219413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115609604302863522986959217 86707203227147642240219413)
                    ·
                      refine ⟨4064400151272545730010285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86707203227147642240219413 4064400151272545730010285)
                      ·
                        rfl

theorem cell23_7915391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_7915391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915391 prefixEnd_7915391 := by exact prefixLift 7915391
  have htrace : WordTrace (prefixWord ++ tailWord_7915391) baseStart_7915391 baseEnd_7915391 := by
    simpa [prefixWord, tailWord_7915391, baseEnd_7915391] using wordTrace_append hprefix tailTrace_7915391
  have hstable : (prefixWord ++ tailWord_7915391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915391).length < 2 ^ (prefixWord ++ tailWord_7915391).sum := by decide
  have hdescent : baseEnd_7915391 < baseStart_7915391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915411 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_7915411 : Nat := 118140960795 + 7915411 * 2 ^ 59
def prefixEnd_7915411 : Nat := 4983230072969 + 3 ^ 40 * 7915411 * 2
def baseEnd_7915411 : Nat := 4064410420885635651760193

theorem tailTrace_7915411 : CollatzResearch.WordTrace tailWord_7915411 prefixEnd_7915411 4064410420885635651760193 := by
  unfold tailWord_7915411
  simp only [CollatzResearch.WordTrace]
  refine ⟨288698756726825266418066087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192465837817883510945377391 288698756726825266418066087)
  ·
    refine ⟨433048135090237899627099131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288698756726825266418066087 433048135090237899627099131)
    ·
      refine ⟨649572202635356849440648697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433048135090237899627099131 649572202635356849440648697)
      ·
        refine ⟨487179151976517637080486523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649572202635356849440648697 487179151976517637080486523)
        ·
          refine ⟨730768727964776455620729785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487179151976517637080486523 730768727964776455620729785)
          ·
            refine ⟨548076545973582341715547339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730768727964776455620729785 548076545973582341715547339)
            ·
              refine ⟨822114818960373512573321009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548076545973582341715547339 822114818960373512573321009)
              ·
                refine ⟨616586114220280134429990757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822114818960373512573321009 616586114220280134429990757)
                ·
                  refine ⟨115609896416302525205623267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616586114220280134429990757 115609896416302525205623267)
                  ·
                    refine ⟨173414844624453787808434901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115609896416302525205623267 173414844624453787808434901)
                    ·
                      refine ⟨4064410420885635651760193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173414844624453787808434901 4064410420885635651760193)
                      ·
                        rfl

theorem cell23_7915411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_7915411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915411 prefixEnd_7915411 := by exact prefixLift 7915411
  have htrace : WordTrace (prefixWord ++ tailWord_7915411) baseStart_7915411 baseEnd_7915411 := by
    simpa [prefixWord, tailWord_7915411, baseEnd_7915411] using wordTrace_append hprefix tailTrace_7915411
  have hstable : (prefixWord ++ tailWord_7915411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915411).length < 2 ^ (prefixWord ++ tailWord_7915411).sum := by decide
  have hdescent : baseEnd_7915411 < baseStart_7915411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915426 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_7915426 : Nat := 118140960795 + 7915426 * 2 ^ 59
def prefixEnd_7915426 : Nat := 4983230072969 + 3 ^ 40 * 7915426 * 2
def baseEnd_7915426 : Nat := 1354806041031817697690875

theorem tailTrace_7915426 : CollatzResearch.WordTrace tailWord_7915426 prefixEnd_7915426 1354806041031817697690875 := by
  unfold tailWord_7915426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72174825955442730994965533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192466202547847282653241421 72174825955442730994965533)
  ·
    refine ⟨27065559733291024123112075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72174825955442730994965533 27065559733291024123112075)
    ·
      refine ⟨40598339599936536184668113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27065559733291024123112075 40598339599936536184668113)
      ·
        refine ⟨30448754699952402138501085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40598339599936536184668113 30448754699952402138501085)
        ·
          refine ⟨11418283012482150801937907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30448754699952402138501085 11418283012482150801937907)
          ·
            refine ⟨17127424518723226202906861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418283012482150801937907 17127424518723226202906861)
            ·
              refine ⟨6422784194521209826090073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17127424518723226202906861 6422784194521209826090073)
              ·
                refine ⟨4817088145890907369567555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422784194521209826090073 4817088145890907369567555)
                ·
                  refine ⟨7225632218836361054351333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817088145890907369567555 7225632218836361054351333)
                  ·
                    refine ⟨1354806041031817697690875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225632218836361054351333 1354806041031817697690875)
                    ·
                      rfl

theorem cell23_7915426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_7915426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915426 prefixEnd_7915426 := by exact prefixLift 7915426
  have htrace : WordTrace (prefixWord ++ tailWord_7915426) baseStart_7915426 baseEnd_7915426 := by
    simpa [prefixWord, tailWord_7915426, baseEnd_7915426] using wordTrace_append hprefix tailTrace_7915426
  have hstable : (prefixWord ++ tailWord_7915426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915426).length < 2 ^ (prefixWord ++ tailWord_7915426).sum := by decide
  have hdescent : baseEnd_7915426 < baseStart_7915426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915448 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 6]
def baseStart_7915448 : Nat := 118140960795 + 7915448 * 2 ^ 59
def prefixEnd_7915448 : Nat := 4983230072969 + 3 ^ 40 * 7915448 * 2
def baseEnd_7915448 : Nat := 1354809806556617335665841

theorem tailTrace_7915448 : CollatzResearch.WordTrace tailWord_7915448 prefixEnd_7915448 1354809806556617335665841 := by
  unfold tailWord_7915448
  simp only [CollatzResearch.WordTrace]
  refine ⟨144350053113845610868581499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192466737485127481158108665 144350053113845610868581499)
  ·
    refine ⟨216525079670768416302872249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144350053113845610868581499 216525079670768416302872249)
    ·
      refine ⟨162393809753076312227154187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216525079670768416302872249 162393809753076312227154187)
      ·
        refine ⟨243590714629614468340731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162393809753076312227154187 243590714629614468340731281)
        ·
          refine ⟨182693035972210851255548461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243590714629614468340731281 182693035972210851255548461)
          ·
            refine ⟨68509888489579069220830673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182693035972210851255548461 68509888489579069220830673)
            ·
              refine ⟨51382416367184301915623005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68509888489579069220830673 51382416367184301915623005)
              ·
                refine ⟨19268406137694113218358627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51382416367184301915623005 19268406137694113218358627)
                ·
                  refine ⟨28902609206541169827537941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19268406137694113218358627 28902609206541169827537941)
                  ·
                    refine ⟨1354809806556617335665841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28902609206541169827537941 1354809806556617335665841)
                    ·
                      rfl

theorem cell23_7915448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_7915448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915448 prefixEnd_7915448 := by exact prefixLift 7915448
  have htrace : WordTrace (prefixWord ++ tailWord_7915448) baseStart_7915448 baseEnd_7915448 := by
    simpa [prefixWord, tailWord_7915448, baseEnd_7915448] using wordTrace_append hprefix tailTrace_7915448
  have hstable : (prefixWord ++ tailWord_7915448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915448).length < 2 ^ (prefixWord ++ tailWord_7915448).sum := by decide
  have hdescent : baseEnd_7915448 < baseStart_7915448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915452 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_7915452 : Nat := 118140960795 + 7915452 * 2 ^ 59
def prefixEnd_7915452 : Nat := 4983230072969 + 3 ^ 40 * 7915452 * 2
def baseEnd_7915452 : Nat := 1354810491197489997115835

theorem tailTrace_7915452 : CollatzResearch.WordTrace tailWord_7915452 prefixEnd_7915452 1354810491197489997115835 := by
  unfold tailWord_7915452
  simp only [CollatzResearch.WordTrace]
  refine ⟨144350126059838365210154305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192466834746451153613539073 144350126059838365210154305)
  ·
    refine ⟨108262594544878773907615729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144350126059838365210154305 108262594544878773907615729)
    ·
      refine ⟨81196945908659080430711797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108262594544878773907615729 81196945908659080430711797)
      ·
        refine ⟨7612213678936788790379231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81196945908659080430711797 7612213678936788790379231)
        ·
          refine ⟨11418320518405183185568847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612213678936788790379231 11418320518405183185568847)
          ·
            refine ⟨17127480777607774778353271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418320518405183185568847 17127480777607774778353271)
            ·
              refine ⟨25691221166411662167529907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127480777607774778353271 25691221166411662167529907)
              ·
                refine ⟨38536831749617493251294861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25691221166411662167529907 38536831749617493251294861)
                ·
                  refine ⟨14451311906106559969235573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38536831749617493251294861 14451311906106559969235573)
                  ·
                    refine ⟨1354810491197489997115835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14451311906106559969235573 1354810491197489997115835)
                    ·
                      rfl

theorem cell23_7915452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_7915452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915452 prefixEnd_7915452 := by exact prefixLift 7915452
  have htrace : WordTrace (prefixWord ++ tailWord_7915452) baseStart_7915452 baseEnd_7915452 := by
    simpa [prefixWord, tailWord_7915452, baseEnd_7915452] using wordTrace_append hprefix tailTrace_7915452
  have hstable : (prefixWord ++ tailWord_7915452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915452).length < 2 ^ (prefixWord ++ tailWord_7915452).sum := by decide
  have hdescent : baseEnd_7915452 < baseStart_7915452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915502 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_7915502 : Nat := 118140960795 + 7915502 * 2 ^ 59
def prefixEnd_7915502 : Nat := 4983230072969 + 3 ^ 40 * 7915502 * 2
def baseEnd_7915502 : Nat := 4064457147625194795722275

theorem tailTrace_7915502 : CollatzResearch.WordTrace tailWord_7915502 prefixEnd_7915502 4064457147625194795722275 := by
  unfold tailWord_7915502
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087759471186948619953595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192468050512997059306419173 36087759471186948619953595)
  ·
    refine ⟨54131639206780422929930393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36087759471186948619953595 54131639206780422929930393)
    ·
      refine ⟨40598729405085317197447795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54131639206780422929930393 40598729405085317197447795)
      ·
        refine ⟨60898094107627975796171693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40598729405085317197447795 60898094107627975796171693)
        ·
          refine ⟨22836785290360490923564385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60898094107627975796171693 22836785290360490923564385)
          ·
            refine ⟨17127588967770368192673289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22836785290360490923564385 17127588967770368192673289)
            ·
              refine ⟨12845691725827776144504967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127588967770368192673289 12845691725827776144504967)
              ·
                refine ⟨19268537588741664216757451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845691725827776144504967 19268537588741664216757451)
                ·
                  refine ⟨28902806383112496325136177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19268537588741664216757451 28902806383112496325136177)
                  ·
                    refine ⟨21677104787334372243852133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28902806383112496325136177 21677104787334372243852133)
                    ·
                      refine ⟨4064457147625194795722275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21677104787334372243852133 4064457147625194795722275)
                      ·
                        rfl

theorem cell23_7915502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_7915502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915502 prefixEnd_7915502 := by exact prefixLift 7915502
  have htrace : WordTrace (prefixWord ++ tailWord_7915502) baseStart_7915502 baseEnd_7915502 := by
    simpa [prefixWord, tailWord_7915502, baseEnd_7915502] using wordTrace_append hprefix tailTrace_7915502
  have hstable : (prefixWord ++ tailWord_7915502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915502).length < 2 ^ (prefixWord ++ tailWord_7915502).sum := by decide
  have hdescent : baseEnd_7915502 < baseStart_7915502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915556 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7915556 : Nat := 118140960795 + 7915556 * 2 ^ 59
def prefixEnd_7915556 : Nat := 4983230072969 + 3 ^ 40 * 7915556 * 2
def baseEnd_7915556 : Nat := 4064484875580537584447027

theorem tailTrace_7915556 : CollatzResearch.WordTrace tailWord_7915556 prefixEnd_7915556 4064484875580537584447027 := by
  unfold tailWord_7915556
  simp only [CollatzResearch.WordTrace]
  refine ⟨144352022655649978091047261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192469363540866637454729681 144352022655649978091047261)
  ·
    refine ⟨54132008495868741784142723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144352022655649978091047261 54132008495868741784142723)
    ·
      refine ⟨81198012743803112676214085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54132008495868741784142723 81198012743803112676214085)
      ·
        refine ⟨15224627389463083626790141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81198012743803112676214085 15224627389463083626790141)
        ·
          refine ⟨5709235271048656360046303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15224627389463083626790141 5709235271048656360046303)
          ·
            refine ⟨8563852906572984540069455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709235271048656360046303 8563852906572984540069455)
            ·
              refine ⟨12845779359859476810104183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563852906572984540069455 12845779359859476810104183)
              ·
                refine ⟨19268669039789215215156275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845779359859476810104183 19268669039789215215156275)
                ·
                  refine ⟨28903003559683822822734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19268669039789215215156275 28903003559683822822734413)
                  ·
                    refine ⟨10838626334881433558525405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28903003559683822822734413 10838626334881433558525405)
                    ·
                      refine ⟨4064484875580537584447027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838626334881433558525405 4064484875580537584447027)
                      ·
                        rfl

theorem cell23_7915556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7915556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915556 prefixEnd_7915556 := by exact prefixLift 7915556
  have htrace : WordTrace (prefixWord ++ tailWord_7915556) baseStart_7915556 baseEnd_7915556 := by
    simpa [prefixWord, tailWord_7915556, baseEnd_7915556] using wordTrace_append hprefix tailTrace_7915556
  have hstable : (prefixWord ++ tailWord_7915556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915556).length < 2 ^ (prefixWord ++ tailWord_7915556).sum := by decide
  have hdescent : baseEnd_7915556 < baseStart_7915556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915566 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7915566 : Nat := 118140960795 + 7915566 * 2 ^ 59
def prefixEnd_7915566 : Nat := 4983230072969 + 3 ^ 40 * 7915566 * 2
def baseEnd_7915566 : Nat := 4064490010387082545321981

theorem tailTrace_7915566 : CollatzResearch.WordTrace tailWord_7915566 prefixEnd_7915566 4064490010387082545321981 := by
  unfold tailWord_7915566
  simp only [CollatzResearch.WordTrace]
  refine ⟨36088051255157965986244819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192469606694175818593305701 36088051255157965986244819)
  ·
    refine ⟨54132076882736948979367229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36088051255157965986244819 54132076882736948979367229)
    ·
      refine ⟨20299528831026355867262711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54132076882736948979367229 20299528831026355867262711)
      ·
        refine ⟨30449293246539533800894067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20299528831026355867262711 30449293246539533800894067)
        ·
          refine ⟨45673939869809300701341101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30449293246539533800894067 45673939869809300701341101)
          ·
            refine ⟨17127727451178487763002913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45673939869809300701341101 17127727451178487763002913)
            ·
              refine ⟨12845795588383865822252185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127727451178487763002913 12845795588383865822252185)
              ·
                refine ⟨9634346691287899366689139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12845795588383865822252185 9634346691287899366689139)
                ·
                  refine ⟨14451520036931849050033709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634346691287899366689139 14451520036931849050033709)
                  ·
                    refine ⟨5419320013849443393762641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14451520036931849050033709 5419320013849443393762641)
                    ·
                      refine ⟨4064490010387082545321981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419320013849443393762641 4064490010387082545321981)
                      ·
                        rfl

theorem cell23_7915566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7915566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915566 prefixEnd_7915566 := by exact prefixLift 7915566
  have htrace : WordTrace (prefixWord ++ tailWord_7915566) baseStart_7915566 baseEnd_7915566 := by
    simpa [prefixWord, tailWord_7915566, baseEnd_7915566] using wordTrace_append hprefix tailTrace_7915566
  have hstable : (prefixWord ++ tailWord_7915566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915566).length < 2 ^ (prefixWord ++ tailWord_7915566).sum := by decide
  have hdescent : baseEnd_7915566 < baseStart_7915566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915613 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7915613 : Nat := 118140960795 + 7915613 * 2 ^ 59
def prefixEnd_7915613 : Nat := 4983230072969 + 3 ^ 40 * 7915613 * 2
def baseEnd_7915613 : Nat := 4064514143977843861434265

theorem tailTrace_7915613 : CollatzResearch.WordTrace tailWord_7915613 prefixEnd_7915613 4064514143977843861434265 := by
  unfold tailWord_7915613
  simp only [CollatzResearch.WordTrace]
  refine ⟨288706124272093454916919493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192470749514728969944612995 288706124272093454916919493)
  ·
    refine ⟨54132398301017522796922405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288706124272093454916919493 54132398301017522796922405)
    ·
      refine ⟨10149824681440785524422951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54132398301017522796922405 10149824681440785524422951)
      ·
        refine ⟨15224737022161178286634427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10149824681440785524422951 15224737022161178286634427)
        ·
          refine ⟨22837105533241767429951641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15224737022161178286634427 22837105533241767429951641)
          ·
            refine ⟨17127829149931325572463731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22837105533241767429951641 17127829149931325572463731)
            ·
              refine ⟨25691743724896988358695597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127829149931325572463731 25691743724896988358695597)
              ·
                refine ⟨9634403896836370634510849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25691743724896988358695597 9634403896836370634510849)
                ·
                  refine ⟨7225802922627277975883137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9634403896836370634510849 7225802922627277975883137)
                  ·
                    refine ⟨5419352191970458481912353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225802922627277975883137 5419352191970458481912353)
                    ·
                      refine ⟨4064514143977843861434265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419352191970458481912353 4064514143977843861434265)
                      ·
                        rfl

theorem cell23_7915613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7915613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915613 prefixEnd_7915613 := by exact prefixLift 7915613
  have htrace : WordTrace (prefixWord ++ tailWord_7915613) baseStart_7915613 baseEnd_7915613 := by
    simpa [prefixWord, tailWord_7915613, baseEnd_7915613] using wordTrace_append hprefix tailTrace_7915613
  have hstable : (prefixWord ++ tailWord_7915613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915613).length < 2 ^ (prefixWord ++ tailWord_7915613).sum := by decide
  have hdescent : baseEnd_7915613 < baseStart_7915613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915632 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 2, 5]
def baseStart_7915632 : Nat := 118140960795 + 7915632 * 2 ^ 59
def prefixEnd_7915632 : Nat := 4983230072969 + 3 ^ 40 * 7915632 * 2
def baseEnd_7915632 : Nat := 1354841300036759762365559

theorem tailTrace_7915632 : CollatzResearch.WordTrace tailWord_7915632 prefixEnd_7915632 1354841300036759762365559 := by
  unfold tailWord_7915632
  simp only [CollatzResearch.WordTrace]
  refine ⟨144353408629512310580930575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192471211506016414107907433 144353408629512310580930575)
  ·
    refine ⟨216530112944268465871395863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144353408629512310580930575 216530112944268465871395863)
    ·
      refine ⟨324795169416402698807093795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216530112944268465871395863 324795169416402698807093795)
      ·
        refine ⟨487192754124604048210640693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324795169416402698807093795 487192754124604048210640693)
        ·
          refine ⟨45674320699181629519747565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487192754124604048210640693 45674320699181629519747565)
          ·
            refine ⟨17127870262193111069905337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45674320699181629519747565 17127870262193111069905337)
            ·
              refine ⟨12845902696644833302429003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127870262193111069905337 12845902696644833302429003)
              ·
                refine ⟨19268854044967249953643505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12845902696644833302429003 19268854044967249953643505)
                ·
                  refine ⟨14451640533725437465232629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19268854044967249953643505 14451640533725437465232629)
                  ·
                    refine ⟨1354841300036759762365559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14451640533725437465232629 1354841300036759762365559)
                    ·
                      rfl

theorem cell23_7915632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_7915632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915632 prefixEnd_7915632 := by exact prefixLift 7915632
  have htrace : WordTrace (prefixWord ++ tailWord_7915632) baseStart_7915632 baseEnd_7915632 := by
    simpa [prefixWord, tailWord_7915632, baseEnd_7915632] using wordTrace_append hprefix tailTrace_7915632
  have hstable : (prefixWord ++ tailWord_7915632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915632).length < 2 ^ (prefixWord ++ tailWord_7915632).sum := by decide
  have hdescent : baseEnd_7915632 < baseStart_7915632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915652 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7915652 : Nat := 118140960795 + 7915652 * 2 ^ 59
def prefixEnd_7915652 : Nat := 4983230072969 + 3 ^ 40 * 7915652 * 2
def baseEnd_7915652 : Nat := 4064534169723369208846585

theorem tailTrace_7915652 : CollatzResearch.WordTrace tailWord_7915652 prefixEnd_7915652 4064534169723369208846585 := by
  unfold tailWord_7915652
  simp only [CollatzResearch.WordTrace]
  refine ⟨144353773359476082288794605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192471697812634776385059473 144353773359476082288794605)
  ·
    refine ⟨54132665009803530858297977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144353773359476082288794605 54132665009803530858297977)
    ·
      refine ⟨40599498757352648143723483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54132665009803530858297977 40599498757352648143723483)
      ·
        refine ⟨60899248136028972215585225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40599498757352648143723483 60899248136028972215585225)
        ·
          refine ⟨45674436102021729161688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60899248136028972215585225 45674436102021729161688919)
          ·
            refine ⟨68511654153032593742533379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45674436102021729161688919 68511654153032593742533379)
            ·
              refine ⟨102767481229548890613800069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68511654153032593742533379 102767481229548890613800069)
              ·
                refine ⟨19268902730540416990087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102767481229548890613800069 19268902730540416990087513)
                ·
                  refine ⟨14451677047905312742565635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19268902730540416990087513 14451677047905312742565635)
                  ·
                    refine ⟨21677515571857969113848453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14451677047905312742565635 21677515571857969113848453)
                    ·
                      refine ⟨4064534169723369208846585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21677515571857969113848453 4064534169723369208846585)
                      ·
                        rfl

theorem cell23_7915652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7915652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915652 prefixEnd_7915652 := by exact prefixLift 7915652
  have htrace : WordTrace (prefixWord ++ tailWord_7915652) baseStart_7915652 baseEnd_7915652 := by
    simpa [prefixWord, tailWord_7915652, baseEnd_7915652] using wordTrace_append hprefix tailTrace_7915652
  have hstable : (prefixWord ++ tailWord_7915652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915652).length < 2 ^ (prefixWord ++ tailWord_7915652).sum := by decide
  have hdescent : baseEnd_7915652 < baseStart_7915652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915675 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 6]
def baseStart_7915675 : Nat := 118140960795 + 7915675 * 2 ^ 59
def prefixEnd_7915675 : Nat := 4983230072969 + 3 ^ 40 * 7915675 * 2
def baseEnd_7915675 : Nat := 451616219975380290984331

theorem tailTrace_7915675 : CollatzResearch.WordTrace tailWord_7915675 prefixEnd_7915675 451616219975380290984331 := by
  unfold tailWord_7915675
  simp only [CollatzResearch.WordTrace]
  refine ⟨288708385597868839505676479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192472257065245893003784319 288708385597868839505676479)
  ·
    refine ⟨433062578396803259258514719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288708385597868839505676479 433062578396803259258514719)
    ·
      refine ⟨649593867595204888887772079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433062578396803259258514719 649593867595204888887772079)
      ·
        refine ⟨974390801392807333331658119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649593867595204888887772079 974390801392807333331658119)
        ·
          refine ⟨1461586202089210999997487179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974390801392807333331658119 1461586202089210999997487179)
          ·
            refine ⟨2192379303133816499996230769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461586202089210999997487179 2192379303133816499996230769)
            ·
              refine ⟨1644284477350362374997173077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192379303133816499996230769 1644284477350362374997173077)
              ·
                refine ⟨9634479359474779540999061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1644284477350362374997173077 9634479359474779540999061)
                ·
                  refine ⟨451616219975380290984331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9634479359474779540999061 451616219975380290984331)
                  ·
                    rfl

theorem cell23_7915675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 6].length) (baseStart_7915675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915675 prefixEnd_7915675 := by exact prefixLift 7915675
  have htrace : WordTrace (prefixWord ++ tailWord_7915675) baseStart_7915675 baseEnd_7915675 := by
    simpa [prefixWord, tailWord_7915675, baseEnd_7915675] using wordTrace_append hprefix tailTrace_7915675
  have hstable : (prefixWord ++ tailWord_7915675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915675).length < 2 ^ (prefixWord ++ tailWord_7915675).sum := by decide
  have hdescent : baseEnd_7915675 < baseStart_7915675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915679 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 3, 4]
def baseStart_7915679 : Nat := 118140960795 + 7915679 * 2 ^ 59
def prefixEnd_7915679 : Nat := 4983230072969 + 3 ^ 40 * 7915679 * 2
def baseEnd_7915679 : Nat := 1354849344567013534402987

theorem tailTrace_7915679 : CollatzResearch.WordTrace tailWord_7915679 prefixEnd_7915679 1354849344567013534402987 := by
  unfold tailWord_7915679
  simp only [CollatzResearch.WordTrace]
  refine ⟨288708531489854348188822091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192472354326569565459214727 288708531489854348188822091)
  ·
    refine ⟨433062797234781522283233137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288708531489854348188822091 433062797234781522283233137)
    ·
      refine ⟨324797097926086141712424853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433062797234781522283233137 324797097926086141712424853)
      ·
        refine ⟨15224863965285287892769915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324797097926086141712424853 15224863965285287892769915)
        ·
          refine ⟨22837295947927931839154873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15224863965285287892769915 22837295947927931839154873)
          ·
            refine ⟨17127971960945948879366155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22837295947927931839154873 17127971960945948879366155)
            ·
              refine ⟨25691957941418923319049233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127971960945948879366155 25691957941418923319049233)
              ·
                refine ⟨19268968456064192489286925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25691957941418923319049233 19268968456064192489286925)
                ·
                  refine ⟨7225863171024072183482597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19268968456064192489286925 7225863171024072183482597)
                  ·
                    refine ⟨1354849344567013534402987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225863171024072183482597 1354849344567013534402987)
                    ·
                      rfl

theorem cell23_7915679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_7915679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915679 prefixEnd_7915679 := by exact prefixLift 7915679
  have htrace : WordTrace (prefixWord ++ tailWord_7915679) baseStart_7915679 baseEnd_7915679 := by
    simpa [prefixWord, tailWord_7915679, baseEnd_7915679] using wordTrace_append hprefix tailTrace_7915679
  have hstable : (prefixWord ++ tailWord_7915679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915679).length < 2 ^ (prefixWord ++ tailWord_7915679).sum := by decide
  have hdescent : baseEnd_7915679 < baseStart_7915679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915759 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_7915759 : Nat := 118140960795 + 7915759 * 2 ^ 59
def prefixEnd_7915759 : Nat := 4983230072969 + 3 ^ 40 * 7915759 * 2
def baseEnd_7915759 : Nat := 4064589112153400290208593

theorem tailTrace_7915759 : CollatzResearch.WordTrace tailWord_7915759 prefixEnd_7915759 4064589112153400290208593 := by
  unfold tailWord_7915759
  simp only [CollatzResearch.WordTrace]
  refine ⟨288711449329564521851734331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192474299553043014567822887 288711449329564521851734331)
  ·
    refine ⟨433067173994346782777601497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288711449329564521851734331 433067173994346782777601497)
    ·
      refine ⟨324800380495760087083201123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433067173994346782777601497 324800380495760087083201123)
      ·
        refine ⟨487200570743640130624801685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324800380495760087083201123 487200570743640130624801685)
        ·
          refine ⟨22837526753608131123037579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 487200570743640130624801685 22837526753608131123037579)
          ·
            refine ⟨34256290130412196684556369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837526753608131123037579 34256290130412196684556369)
            ·
              refine ⟨25692217597809147513417277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34256290130412196684556369 25692217597809147513417277)
              ·
                refine ⟨9634581599178430317531479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25692217597809147513417277 9634581599178430317531479)
                ·
                  refine ⟨14451872398767645476297219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634581599178430317531479 14451872398767645476297219)
                  ·
                    refine ⟨21677808598151468214445829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14451872398767645476297219 21677808598151468214445829)
                    ·
                      refine ⟨4064589112153400290208593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21677808598151468214445829 4064589112153400290208593)
                      ·
                        rfl

theorem cell23_7915759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_7915759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915759 prefixEnd_7915759 := by exact prefixLift 7915759
  have htrace : WordTrace (prefixWord ++ tailWord_7915759) baseStart_7915759 baseEnd_7915759 := by
    simpa [prefixWord, tailWord_7915759, baseEnd_7915759] using wordTrace_append hprefix tailTrace_7915759
  have hstable : (prefixWord ++ tailWord_7915759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915759).length < 2 ^ (prefixWord ++ tailWord_7915759).sum := by decide
  have hdescent : baseEnd_7915759 < baseStart_7915759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915772 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_7915772 : Nat := 118140960795 + 7915772 * 2 ^ 59
def prefixEnd_7915772 : Nat := 4983230072969 + 3 ^ 40 * 7915772 * 2
def baseEnd_7915772 : Nat := 4064595787401908739346033

theorem tailTrace_7915772 : CollatzResearch.WordTrace tailWord_7915772 prefixEnd_7915772 4064595787401908739346033 := by
  unfold tailWord_7915772
  simp only [CollatzResearch.WordTrace]
  refine ⟨144355961739258712535978785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192474615652344950047971713 144355961739258712535978785)
  ·
    refine ⟨108266971304444034401984089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144355961739258712535978785 108266971304444034401984089)
    ·
      refine ⟨81200228478333025801488067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108266971304444034401984089 81200228478333025801488067)
      ·
        refine ⟨121800342717499538702232101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81200228478333025801488067 121800342717499538702232101)
        ·
          refine ⟨22837564259531163506668519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121800342717499538702232101 22837564259531163506668519)
          ·
            refine ⟨34256346389296745260002779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837564259531163506668519 34256346389296745260002779)
            ·
              refine ⟨51384519583945117890004169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34256346389296745260002779 51384519583945117890004169)
              ·
                refine ⟨38538389687958838417503127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51384519583945117890004169 38538389687958838417503127)
                ·
                  refine ⟨57807584531938257626254691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38538389687958838417503127 57807584531938257626254691)
                  ·
                    refine ⟨86711376797907386439382037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57807584531938257626254691 86711376797907386439382037)
                    ·
                      refine ⟨4064595787401908739346033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86711376797907386439382037 4064595787401908739346033)
                      ·
                        rfl

theorem cell23_7915772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_7915772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915772 prefixEnd_7915772 := by exact prefixLift 7915772
  have htrace : WordTrace (prefixWord ++ tailWord_7915772) baseStart_7915772 baseEnd_7915772 := by
    simpa [prefixWord, tailWord_7915772, baseEnd_7915772] using wordTrace_append hprefix tailTrace_7915772
  have hstable : (prefixWord ++ tailWord_7915772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915772).length < 2 ^ (prefixWord ++ tailWord_7915772).sum := by decide
  have hdescent : baseEnd_7915772 < baseStart_7915772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915776 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2]
def baseStart_7915776 : Nat := 118140960795 + 7915776 * 2 ^ 59
def prefixEnd_7915776 : Nat := 4983230072969 + 3 ^ 40 * 7915776 * 2
def baseEnd_7915776 : Nat := 4064597841324526723696015

theorem tailTrace_7915776 : CollatzResearch.WordTrace tailWord_7915776 prefixEnd_7915776 4064597841324526723696015 := by
  unfold tailWord_7915776
  simp only [CollatzResearch.WordTrace]
  refine ⟨144356034685251466877551591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192474712913668622503402121 144356034685251466877551591)
  ·
    refine ⟨216534052027877200316327387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144356034685251466877551591 216534052027877200316327387)
    ·
      refine ⟨324801078041815800474491081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216534052027877200316327387 324801078041815800474491081)
      ·
        refine ⟨243600808531361850355868311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324801078041815800474491081 243600808531361850355868311)
        ·
          refine ⟨365401212797042775533802467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243600808531361850355868311 365401212797042775533802467)
          ·
            refine ⟨548101819195564163300703701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365401212797042775533802467 548101819195564163300703701)
            ·
              refine ⟨12846136387396035077360243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 548101819195564163300703701 12846136387396035077360243)
              ·
                refine ⟨19269204581094052616040365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846136387396035077360243 19269204581094052616040365)
                ·
                  refine ⟨7225951717910269731015137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19269204581094052616040365 7225951717910269731015137)
                  ·
                    refine ⟨5419463788432702298261353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7225951717910269731015137 5419463788432702298261353)
                    ·
                      refine ⟨4064597841324526723696015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419463788432702298261353 4064597841324526723696015)
                      ·
                        rfl

theorem cell23_7915776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_7915776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915776 prefixEnd_7915776 := by exact prefixLift 7915776
  have htrace : WordTrace (prefixWord ++ tailWord_7915776) baseStart_7915776 baseEnd_7915776 := by
    simpa [prefixWord, tailWord_7915776, baseEnd_7915776] using wordTrace_append hprefix tailTrace_7915776
  have hstable : (prefixWord ++ tailWord_7915776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915776).length < 2 ^ (prefixWord ++ tailWord_7915776).sum := by decide
  have hdescent : baseEnd_7915776 < baseStart_7915776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915786 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_7915786 : Nat := 118140960795 + 7915786 * 2 ^ 59
def prefixEnd_7915786 : Nat := 4983230072969 + 3 ^ 40 * 7915786 * 2
def baseEnd_7915786 : Nat := 1354867658710357228190323

theorem tailTrace_7915786 : CollatzResearch.WordTrace tailWord_7915786 prefixEnd_7915786 1354867658710357228190323 := by
  unfold tailWord_7915786
  simp only [CollatzResearch.WordTrace]
  refine ⟨72178108525116676365741803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192474956066977803641978141 72178108525116676365741803)
  ·
    refine ⟨108267162787675014548612705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72178108525116676365741803 108267162787675014548612705)
    ·
      refine ⟨81200372090756260911459529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108267162787675014548612705 81200372090756260911459529)
      ·
        refine ⟨60900279068067195683594647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81200372090756260911459529 60900279068067195683594647)
        ·
          refine ⟨91350418602100793525391971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60900279068067195683594647 91350418602100793525391971)
          ·
            refine ⟨137025627903151190288087957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91350418602100793525391971 137025627903151190288087957)
            ·
              refine ⟨6423076307960212044754123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137025627903151190288087957 6423076307960212044754123)
              ·
                refine ⟨9634614461940318067131185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423076307960212044754123 9634614461940318067131185)
                ·
                  refine ⟨7225960846455238550348389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9634614461940318067131185 7225960846455238550348389)
                  ·
                    refine ⟨1354867658710357228190323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225960846455238550348389 1354867658710357228190323)
                    ·
                      rfl

theorem cell23_7915786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_7915786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915786 prefixEnd_7915786 := by exact prefixLift 7915786
  have htrace : WordTrace (prefixWord ++ tailWord_7915786) baseStart_7915786 baseEnd_7915786 := by
    simpa [prefixWord, tailWord_7915786, baseEnd_7915786] using wordTrace_append hprefix tailTrace_7915786
  have hstable : (prefixWord ++ tailWord_7915786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915786).length < 2 ^ (prefixWord ++ tailWord_7915786).sum := by decide
  have hdescent : baseEnd_7915786 < baseStart_7915786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915806 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7915806 : Nat := 118140960795 + 7915806 * 2 ^ 59
def prefixEnd_7915806 : Nat := 4983230072969 + 3 ^ 40 * 7915806 * 2
def baseEnd_7915806 : Nat := 4064613245744161606320877

theorem tailTrace_7915806 : CollatzResearch.WordTrace tailWord_7915806 prefixEnd_7915806 4064613245744161606320877 := by
  unfold tailWord_7915806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36089145445049281109836909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192475442373596165919130181 36089145445049281109836909)
  ·
    refine ⟨13533429541893480416188841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36089145445049281109836909 13533429541893480416188841)
    ·
      refine ⟨10150072156420110312141631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13533429541893480416188841 10150072156420110312141631)
      ·
        refine ⟨15225108234630165468212447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10150072156420110312141631 15225108234630165468212447)
        ·
          refine ⟨22837662351945248202318671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15225108234630165468212447 22837662351945248202318671)
          ·
            refine ⟨34256493527917872303478007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837662351945248202318671 34256493527917872303478007)
            ·
              refine ⟨51384740291876808455217011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34256493527917872303478007 51384740291876808455217011)
              ·
                refine ⟨77077110437815212682825517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51384740291876808455217011 77077110437815212682825517)
                ·
                  refine ⟨28903916414180704756059569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77077110437815212682825517 28903916414180704756059569)
                  ·
                    refine ⟨21677937310635528567044677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28903916414180704756059569 21677937310635528567044677)
                    ·
                      refine ⟨4064613245744161606320877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21677937310635528567044677 4064613245744161606320877)
                      ·
                        rfl

theorem cell23_7915806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7915806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915806 prefixEnd_7915806 := by exact prefixLift 7915806
  have htrace : WordTrace (prefixWord ++ tailWord_7915806) baseStart_7915806 baseEnd_7915806 := by
    simpa [prefixWord, tailWord_7915806, baseEnd_7915806] using wordTrace_append hprefix tailTrace_7915806
  have hstable : (prefixWord ++ tailWord_7915806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915806).length < 2 ^ (prefixWord ++ tailWord_7915806).sum := by decide
  have hdescent : baseEnd_7915806 < baseStart_7915806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915809 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_7915809 : Nat := 118140960795 + 7915809 * 2 ^ 59
def prefixEnd_7915809 : Nat := 4983230072969 + 3 ^ 40 * 7915809 * 2
def baseEnd_7915809 : Nat := 4064614786186125094583363

theorem tailTrace_7915809 : CollatzResearch.WordTrace tailWord_7915809 prefixEnd_7915809 4064614786186125094583363 := by
  unfold tailWord_7915809
  simp only [CollatzResearch.WordTrace]
  refine ⟨288713272979383380391054481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192475515319588920260702987 288713272979383380391054481)
  ·
    refine ⟨216534954734537535293290861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288713272979383380391054481 216534954734537535293290861)
    ·
      refine ⟨81200608025451575734984073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216534954734537535293290861 81200608025451575734984073)
      ·
        refine ⟨60900456019088681801238055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81200608025451575734984073 60900456019088681801238055)
        ·
          refine ⟨91350684028633022701857083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60900456019088681801238055 91350684028633022701857083)
          ·
            refine ⟨137026026042949534052785625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91350684028633022701857083 137026026042949534052785625)
            ·
              refine ⟨102769519532212150539589219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137026026042949534052785625 102769519532212150539589219)
              ·
                refine ⟨154154279298318225809383829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102769519532212150539589219 154154279298318225809383829)
                ·
                  refine ⟨7225981842108666834814867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154154279298318225809383829 7225981842108666834814867)
                  ·
                    refine ⟨10838972763163000252222301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7225981842108666834814867 10838972763163000252222301)
                    ·
                      refine ⟨4064614786186125094583363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838972763163000252222301 4064614786186125094583363)
                      ·
                        rfl

theorem cell23_7915809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_7915809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915809 prefixEnd_7915809 := by exact prefixLift 7915809
  have htrace : WordTrace (prefixWord ++ tailWord_7915809) baseStart_7915809 baseEnd_7915809 := by
    simpa [prefixWord, tailWord_7915809, baseEnd_7915809] using wordTrace_append hprefix tailTrace_7915809
  have hstable : (prefixWord ++ tailWord_7915809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915809).length < 2 ^ (prefixWord ++ tailWord_7915809).sum := by decide
  have hdescent : baseEnd_7915809 < baseStart_7915809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915813 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_7915813 : Nat := 118140960795 + 7915813 * 2 ^ 59
def prefixEnd_7915813 : Nat := 4983230072969 + 3 ^ 40 * 7915813 * 2
def baseEnd_7915813 : Nat := 4064616840108743078933345

theorem tailTrace_7915813 : CollatzResearch.WordTrace tailWord_7915813 prefixEnd_7915813 4064616840108743078933345 := by
  unfold tailWord_7915813
  simp only [CollatzResearch.WordTrace]
  refine ⟨288713418871368889074200093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192475612580912592716133395 288713418871368889074200093)
  ·
    refine ⟨108267532076763333402825035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288713418871368889074200093 108267532076763333402825035)
    ·
      refine ⟨162401298115145000104237553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108267532076763333402825035 162401298115145000104237553)
      ·
        refine ⟨121800973586358750078178165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162401298115145000104237553 121800973586358750078178165)
        ·
          refine ⟨11418841273721132819829203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121800973586358750078178165 11418841273721132819829203)
          ·
            refine ⟨17128261910581699229743805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418841273721132819829203 17128261910581699229743805)
            ·
              refine ⟨6423098216468137211153927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17128261910581699229743805 6423098216468137211153927)
              ·
                refine ⟨9634647324702205816730891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423098216468137211153927 9634647324702205816730891)
                ·
                  refine ⟨14451970987053308725096337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634647324702205816730891 14451970987053308725096337)
                  ·
                    refine ⟨10838978240289981543822253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14451970987053308725096337 10838978240289981543822253)
                    ·
                      refine ⟨4064616840108743078933345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10838978240289981543822253 4064616840108743078933345)
                      ·
                        rfl

theorem cell23_7915813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_7915813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915813 prefixEnd_7915813 := by exact prefixLift 7915813
  have htrace : WordTrace (prefixWord ++ tailWord_7915813) baseStart_7915813 baseEnd_7915813 := by
    simpa [prefixWord, tailWord_7915813, baseEnd_7915813] using wordTrace_append hprefix tailTrace_7915813
  have hstable : (prefixWord ++ tailWord_7915813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915813).length < 2 ^ (prefixWord ++ tailWord_7915813).sum := by decide
  have hdescent : baseEnd_7915813 < baseStart_7915813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915832 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_7915832 : Nat := 118140960795 + 7915832 * 2 ^ 59
def prefixEnd_7915832 : Nat := 4983230072969 + 3 ^ 40 * 7915832 * 2
def baseEnd_7915832 : Nat := 4064626596241178504595757

theorem tailTrace_7915832 : CollatzResearch.WordTrace tailWord_7915832 prefixEnd_7915832 4064626596241178504595757 := by
  unfold tailWord_7915832
  simp only [CollatzResearch.WordTrace]
  refine ⟨144357055929150027659570875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192476074572200036879427833 144357055929150027659570875)
  ·
    refine ⟨216535583893725041489356313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144357055929150027659570875 216535583893725041489356313)
    ·
      refine ⟨162401687920293781117017235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216535583893725041489356313 162401687920293781117017235)
      ·
        refine ⟨243602531880440671675525853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162401687920293781117017235 243602531880440671675525853)
        ·
          refine ⟨91350949455165251878322195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243602531880440671675525853 91350949455165251878322195)
          ·
            refine ⟨137026424182747877817483293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91350949455165251878322195 137026424182747877817483293)
            ·
              refine ⟨51384909068530454181556235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137026424182747877817483293 51384909068530454181556235)
              ·
                refine ⟨77077363602795681272334353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51384909068530454181556235 77077363602795681272334353)
                ·
                  refine ⟨57808022702096760954250765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77077363602795681272334353 57808022702096760954250765)
                  ·
                    refine ⟨21678008513286285357844037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57808022702096760954250765 21678008513286285357844037)
                    ·
                      refine ⟨4064626596241178504595757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21678008513286285357844037 4064626596241178504595757)
                      ·
                        rfl

theorem cell23_7915832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_7915832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915832 prefixEnd_7915832 := by exact prefixLift 7915832
  have htrace : WordTrace (prefixWord ++ tailWord_7915832) baseStart_7915832 baseEnd_7915832 := by
    simpa [prefixWord, tailWord_7915832, baseEnd_7915832] using wordTrace_append hprefix tailTrace_7915832
  have hstable : (prefixWord ++ tailWord_7915832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915832).length < 2 ^ (prefixWord ++ tailWord_7915832).sum := by decide
  have hdescent : baseEnd_7915832 < baseStart_7915832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915866 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_7915866 : Nat := 118140960795 + 7915866 * 2 ^ 59
def prefixEnd_7915866 : Nat := 4983230072969 + 3 ^ 40 * 7915866 * 2
def baseEnd_7915866 : Nat := 4064644054583431371570601

theorem tailTrace_7915866 : CollatzResearch.WordTrace tailWord_7915866 prefixEnd_7915866 4064644054583431371570601 := by
  unfold tailWord_7915866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72178837985044219781469863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192476901293451252750586301 72178837985044219781469863)
  ·
    refine ⟨108268256977566329672204795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72178837985044219781469863 108268256977566329672204795)
    ·
      refine ⟨162402385466349494508307193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108268256977566329672204795 162402385466349494508307193)
      ·
        refine ⟨121801789099762120881230395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162402385466349494508307193 121801789099762120881230395)
        ·
          refine ⟨182702683649643181321845593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121801789099762120881230395 182702683649643181321845593)
          ·
            refine ⟨137027012737232385991384195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182702683649643181321845593 137027012737232385991384195)
            ·
              refine ⟨205540519105848578987076293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137027012737232385991384195 205540519105848578987076293)
              ·
                refine ⟨38538847332346608560076805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205540519105848578987076293 38538847332346608560076805)
                ·
                  refine ⟨7226033874814989105014401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38538847332346608560076805 7226033874814989105014401)
                  ·
                    refine ⟨5419525406111241828760801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226033874814989105014401 5419525406111241828760801)
                    ·
                      refine ⟨4064644054583431371570601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419525406111241828760801 4064644054583431371570601)
                      ·
                        rfl

theorem cell23_7915866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_7915866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915866 prefixEnd_7915866 := by exact prefixLift 7915866
  have htrace : WordTrace (prefixWord ++ tailWord_7915866) baseStart_7915866 baseEnd_7915866 := by
    simpa [prefixWord, tailWord_7915866, baseEnd_7915866] using wordTrace_append hprefix tailTrace_7915866
  have hstable : (prefixWord ++ tailWord_7915866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915866).length < 2 ^ (prefixWord ++ tailWord_7915866).sum := by decide
  have hdescent : baseEnd_7915866 < baseStart_7915866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915879 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_7915879 : Nat := 118140960795 + 7915879 * 2 ^ 59
def prefixEnd_7915879 : Nat := 4983230072969 + 3 ^ 40 * 7915879 * 2
def baseEnd_7915879 : Nat := 4064650729831939820708041

theorem tailTrace_7915879 : CollatzResearch.WordTrace tailWord_7915879 prefixEnd_7915879 4064650729831939820708041 := by
  unfold tailWord_7915879
  simp only [CollatzResearch.WordTrace]
  refine ⟨288715826089129782346102691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192477217392753188230735127 288715826089129782346102691)
  ·
    refine ⟨433073739133694673519154037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288715826089129782346102691 433073739133694673519154037)
    ·
      refine ⟨40600663043783875642420691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433073739133694673519154037 40600663043783875642420691)
      ·
        refine ⟨60900994565675813463631037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40600663043783875642420691 60900994565675813463631037)
        ·
          refine ⟨22837872962128430048861639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60900994565675813463631037 22837872962128430048861639)
          ·
            refine ⟨34256809443192645073292459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837872962128430048861639 34256809443192645073292459)
            ·
              refine ⟨51385214164788967609938689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34256809443192645073292459 51385214164788967609938689)
              ·
                refine ⟨38538910623591725707454017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51385214164788967609938689 38538910623591725707454017)
                ·
                  refine ⟨28904182967693794280590513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38538910623591725707454017 28904182967693794280590513)
                  ·
                    refine ⟨21678137225770345710442885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28904182967693794280590513 21678137225770345710442885)
                    ·
                      refine ⟨4064650729831939820708041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21678137225770345710442885 4064650729831939820708041)
                      ·
                        rfl

theorem cell23_7915879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_7915879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915879 prefixEnd_7915879 := by exact prefixLift 7915879
  have htrace : WordTrace (prefixWord ++ tailWord_7915879) baseStart_7915879 baseEnd_7915879 := by
    simpa [prefixWord, tailWord_7915879, baseEnd_7915879] using wordTrace_append hprefix tailTrace_7915879
  have hstable : (prefixWord ++ tailWord_7915879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915879).length < 2 ^ (prefixWord ++ tailWord_7915879).sum := by decide
  have hdescent : baseEnd_7915879 < baseStart_7915879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915899 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3]
def baseStart_7915899 : Nat := 118140960795 + 7915899 * 2 ^ 59
def prefixEnd_7915899 : Nat := 4983230072969 + 3 ^ 40 * 7915899 * 2
def baseEnd_7915899 : Nat := 4064660999445029742457949

theorem tailTrace_7915899 : CollatzResearch.WordTrace tailWord_7915899 prefixEnd_7915899 4064660999445029742457949 := by
  unfold tailWord_7915899
  simp only [CollatzResearch.WordTrace]
  refine ⟨288716555549057325761830751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192477703699371550507887167 288716555549057325761830751)
  ·
    refine ⟨433074833323585988642746127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288716555549057325761830751 433074833323585988642746127)
    ·
      refine ⟨649612249985378982964119191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433074833323585988642746127 649612249985378982964119191)
      ·
        refine ⟨974418374978068474446178787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649612249985378982964119191 974418374978068474446178787)
        ·
          refine ⟨1461627562467102711669268181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974418374978068474446178787 1461627562467102711669268181)
          ·
            refine ⟨34256895995322719804748473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1461627562467102711669268181 34256895995322719804748473)
            ·
              refine ⟨25692671996492039853561355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34256895995322719804748473 25692671996492039853561355)
              ·
                refine ⟨38539007994738059780342033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25692671996492039853561355 38539007994738059780342033)
                ·
                  refine ⟨28904255996053544835256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38539007994738059780342033 28904255996053544835256525)
                  ·
                    refine ⟨10839095998520079313221197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28904255996053544835256525 10839095998520079313221197)
                    ·
                      refine ⟨4064660999445029742457949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839095998520079313221197 4064660999445029742457949)
                      ·
                        rfl

theorem cell23_7915899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].length) (baseStart_7915899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915899 prefixEnd_7915899 := by exact prefixLift 7915899
  have htrace : WordTrace (prefixWord ++ tailWord_7915899) baseStart_7915899 baseEnd_7915899 := by
    simpa [prefixWord, tailWord_7915899, baseEnd_7915899] using wordTrace_append hprefix tailTrace_7915899
  have hstable : (prefixWord ++ tailWord_7915899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915899).length < 2 ^ (prefixWord ++ tailWord_7915899).sum := by decide
  have hdescent : baseEnd_7915899 < baseStart_7915899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915939 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7915939 : Nat := 118140960795 + 7915939 * 2 ^ 59
def prefixEnd_7915939 : Nat := 4983230072969 + 3 ^ 40 * 7915939 * 2
def baseEnd_7915939 : Nat := 4064681538671209585957765

theorem tailTrace_7915939 : CollatzResearch.WordTrace tailWord_7915939 prefixEnd_7915939 4064681538671209585957765 := by
  unfold tailWord_7915939
  simp only [CollatzResearch.WordTrace]
  refine ⟨288718014468912412593286871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192478676312608275062191247 288718014468912412593286871)
  ·
    refine ⟨433077021703368618889930307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288718014468912412593286871 433077021703368618889930307)
    ·
      refine ⟨649615532555052928334895461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433077021703368618889930307 649615532555052928334895461)
      ·
        refine ⟨121802912354072424062792899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649615532555052928334895461 121802912354072424062792899)
        ·
          refine ⟨182704368531108636094189349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121802912354072424062792899 182704368531108636094189349)
          ·
            refine ⟨34257069099582869267660503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182704368531108636094189349 34257069099582869267660503)
            ·
              refine ⟨51385603649374303901490755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34257069099582869267660503 51385603649374303901490755)
              ·
                refine ⟨77078405474061455852236133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51385603649374303901490755 77078405474061455852236133)
                ·
                  refine ⟨14452201026386522972294275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77078405474061455852236133 14452201026386522972294275)
                  ·
                    refine ⟨21678301539579784458441413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14452201026386522972294275 21678301539579784458441413)
                    ·
                      refine ⟨4064681538671209585957765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21678301539579784458441413 4064681538671209585957765)
                      ·
                        rfl

theorem cell23_7915939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7915939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915939 prefixEnd_7915939 := by exact prefixLift 7915939
  have htrace : WordTrace (prefixWord ++ tailWord_7915939) baseStart_7915939 baseEnd_7915939 := by
    simpa [prefixWord, tailWord_7915939, baseEnd_7915939] using wordTrace_append hprefix tailTrace_7915939
  have hstable : (prefixWord ++ tailWord_7915939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915939).length < 2 ^ (prefixWord ++ tailWord_7915939).sum := by decide
  have hdescent : baseEnd_7915939 < baseStart_7915939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_7915952 : Nat := 118140960795 + 7915952 * 2 ^ 59
def prefixEnd_7915952 : Nat := 4983230072969 + 3 ^ 40 * 7915952 * 2
def baseEnd_7915952 : Nat := 4064688213919718035095205

theorem tailTrace_7915952 : CollatzResearch.WordTrace tailWord_7915952 prefixEnd_7915952 4064688213919718035095205 := by
  unfold tailWord_7915952
  simp only [CollatzResearch.WordTrace]
  refine ⟨144359244308932657906755055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192478992411910210542340073 144359244308932657906755055)
  ·
    refine ⟨216538866463398986860132583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144359244308932657906755055 216538866463398986860132583)
    ·
      refine ⟨324808299695098480290198875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216538866463398986860132583 324808299695098480290198875)
      ·
        refine ⟨487212449542647720435298313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324808299695098480290198875 487212449542647720435298313)
        ·
          refine ⟨365409337156985790326473735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487212449542647720435298313 365409337156985790326473735)
          ·
            refine ⟨548114005735478685489710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365409337156985790326473735 548114005735478685489710603)
            ·
              refine ⟨822171008603218028234565905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548114005735478685489710603 822171008603218028234565905)
              ·
                refine ⟨616628256452413521175924429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822171008603218028234565905 616628256452413521175924429)
                ·
                  refine ⟨231235596169655070440971661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616628256452413521175924429 231235596169655070440971661)
                  ·
                    refine ⟨86713348563620651415364373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231235596169655070440971661 86713348563620651415364373)
                    ·
                      refine ⟨4064688213919718035095205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86713348563620651415364373 4064688213919718035095205)
                      ·
                        rfl

theorem cell23_7915952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_7915952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915952 prefixEnd_7915952 := by exact prefixLift 7915952
  have htrace : WordTrace (prefixWord ++ tailWord_7915952) baseStart_7915952 baseEnd_7915952 := by
    simpa [prefixWord, tailWord_7915952, baseEnd_7915952] using wordTrace_append hprefix tailTrace_7915952
  have hstable : (prefixWord ++ tailWord_7915952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915952).length < 2 ^ (prefixWord ++ tailWord_7915952).sum := by decide
  have hdescent : baseEnd_7915952 < baseStart_7915952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915966 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7915966 : Nat := 118140960795 + 7915966 * 2 ^ 59
def prefixEnd_7915966 : Nat := 4983230072969 + 3 ^ 40 * 7915966 * 2
def baseEnd_7915966 : Nat := 1354898467549626993440047

theorem tailTrace_7915966 : CollatzResearch.WordTrace tailWord_7915966 prefixEnd_7915966 1354898467549626993440047 := by
  unfold tailWord_7915966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36089874904976824525564969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192479332826543064136346501 36089874904976824525564969)
  ·
    refine ⟨27067406178732618394173727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36089874904976824525564969 27067406178732618394173727)
    ·
      refine ⟨40601109268098927591260591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067406178732618394173727 40601109268098927591260591)
      ·
        refine ⟨60901663902148391386890887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40601109268098927591260591 60901663902148391386890887)
        ·
          refine ⟨91352495853222587080336331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60901663902148391386890887 91352495853222587080336331)
          ·
            refine ⟨137028743779833880620504497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91352495853222587080336331 137028743779833880620504497)
            ·
              refine ⟨102771557834875410465378373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137028743779833880620504497 102771557834875410465378373)
              ·
                refine ⟨19269667094039139462258445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102771557834875410465378373 19269667094039139462258445)
                ·
                  refine ⟨7226125160264677298346917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19269667094039139462258445 7226125160264677298346917)
                  ·
                    refine ⟨1354898467549626993440047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7226125160264677298346917 1354898467549626993440047)
                    ·
                      rfl

theorem cell23_7915966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7915966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915966 prefixEnd_7915966 := by exact prefixLift 7915966
  have htrace : WordTrace (prefixWord ++ tailWord_7915966) baseStart_7915966 baseEnd_7915966 := by
    simpa [prefixWord, tailWord_7915966, baseEnd_7915966] using wordTrace_append hprefix tailTrace_7915966
  have hstable : (prefixWord ++ tailWord_7915966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915966).length < 2 ^ (prefixWord ++ tailWord_7915966).sum := by decide
  have hdescent : baseEnd_7915966 < baseStart_7915966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7915976 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_7915976 : Nat := 118140960795 + 7915976 * 2 ^ 59
def prefixEnd_7915976 : Nat := 4983230072969 + 3 ^ 40 * 7915976 * 2
def baseEnd_7915976 : Nat := 4064700537455425941195095

theorem tailTrace_7915976 : CollatzResearch.WordTrace tailWord_7915976 prefixEnd_7915976 4064700537455425941195095 := by
  unfold tailWord_7915976
  simp only [CollatzResearch.WordTrace]
  refine ⟨144359681984889183956191891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192479575979852245274922521 144359681984889183956191891)
  ·
    refine ⟨216539522977333775934287837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144359681984889183956191891 216539522977333775934287837)
    ·
      refine ⟨81202321116500165975357939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216539522977333775934287837 81202321116500165975357939)
      ·
        refine ⟨121803481674750248963036909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81202321116500165975357939 121803481674750248963036909)
        ·
          refine ⟨45676305628031343361138841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121803481674750248963036909 45676305628031343361138841)
          ·
            refine ⟨34257229221023507520854131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45676305628031343361138841 34257229221023507520854131)
            ·
              refine ⟨51385843831535261281281197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34257229221023507520854131 51385843831535261281281197)
              ·
                refine ⟨19269691436825722980480449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51385843831535261281281197 19269691436825722980480449)
                ·
                  refine ⟨14452268577619292235360337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19269691436825722980480449 14452268577619292235360337)
                  ·
                    refine ⟨10839201433214469176520253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14452268577619292235360337 10839201433214469176520253)
                    ·
                      refine ⟨4064700537455425941195095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839201433214469176520253 4064700537455425941195095)
                      ·
                        rfl

theorem cell23_7915976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_7915976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7915976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7915976 prefixEnd_7915976 := by exact prefixLift 7915976
  have htrace : WordTrace (prefixWord ++ tailWord_7915976) baseStart_7915976 baseEnd_7915976 := by
    simpa [prefixWord, tailWord_7915976, baseEnd_7915976] using wordTrace_append hprefix tailTrace_7915976
  have hstable : (prefixWord ++ tailWord_7915976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7915976).length < 2 ^ (prefixWord ++ tailWord_7915976).sum := by decide
  have hdescent : baseEnd_7915976 < baseStart_7915976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7915976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916016 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2]
def baseStart_7916016 : Nat := 118140960795 + 7916016 * 2 ^ 59
def prefixEnd_7916016 : Nat := 4983230072969 + 3 ^ 40 * 7916016 * 2
def baseEnd_7916016 : Nat := 4064721076681605784694911

theorem tailTrace_7916016 : CollatzResearch.WordTrace tailWord_7916016 prefixEnd_7916016 4064721076681605784694911 := by
  unfold tailWord_7916016
  simp only [CollatzResearch.WordTrace]
  refine ⟨144360411444816727371919951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192480548593088969829226601 144360411444816727371919951)
  ·
    refine ⟨216540617167225091057879927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144360411444816727371919951 216540617167225091057879927)
    ·
      refine ⟨324810925750837636586819891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216540617167225091057879927 324810925750837636586819891)
      ·
        refine ⟨487216388626256454880229837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324810925750837636586819891 487216388626256454880229837)
        ·
          refine ⟨182706145734846170580086189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487216388626256454880229837 182706145734846170580086189)
          ·
            refine ⟨68514804650567313967532321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182706145734846170580086189 68514804650567313967532321)
            ·
              refine ⟨51386103487925485475649241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68514804650567313967532321 51386103487925485475649241)
              ·
                refine ⟨38539577615944114106736931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51386103487925485475649241 38539577615944114106736931)
                ·
                  refine ⟨57809366423916171160105397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38539577615944114106736931 57809366423916171160105397)
                  ·
                    refine ⟨5419628102242141046259881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57809366423916171160105397 5419628102242141046259881)
                    ·
                      refine ⟨4064721076681605784694911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419628102242141046259881 4064721076681605784694911)
                      ·
                        rfl

theorem cell23_7916016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2].length) (baseStart_7916016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916016 prefixEnd_7916016 := by exact prefixLift 7916016
  have htrace : WordTrace (prefixWord ++ tailWord_7916016) baseStart_7916016 baseEnd_7916016 := by
    simpa [prefixWord, tailWord_7916016, baseEnd_7916016] using wordTrace_append hprefix tailTrace_7916016
  have hstable : (prefixWord ++ tailWord_7916016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916016).length < 2 ^ (prefixWord ++ tailWord_7916016).sum := by decide
  have hdescent : baseEnd_7916016 < baseStart_7916016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916033 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_7916033 : Nat := 118140960795 + 7916033 * 2 ^ 59
def prefixEnd_7916033 : Nat := 4983230072969 + 3 ^ 40 * 7916033 * 2
def baseEnd_7916033 : Nat := 4064729805852732218182333

theorem tailTrace_7916033 : CollatzResearch.WordTrace tailWord_7916033 prefixEnd_7916033 4064729805852732218182333 := by
  unfold tailWord_7916033
  simp only [CollatzResearch.WordTrace]
  refine ⟨288721442930571866647208753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192480961953714577764805835 288721442930571866647208753)
  ·
    refine ⟨216541082197928899985406565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288721442930571866647208753 216541082197928899985406565)
    ·
      refine ⟨40601452912111668747263731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216541082197928899985406565 40601452912111668747263731)
      ·
        refine ⟨60902179368167503120895597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40601452912111668747263731 60902179368167503120895597)
        ·
          refine ⟨22838317263062813670335849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60902179368167503120895597 22838317263062813670335849)
          ·
            refine ⟨17128737947297110252751887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22838317263062813670335849 17128737947297110252751887)
            ·
              refine ⟨25693106920945665379127831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17128737947297110252751887 25693106920945665379127831)
              ·
                refine ⟨38539660381418498068691747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25693106920945665379127831 38539660381418498068691747)
                ·
                  refine ⟨57809490572127747103037621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38539660381418498068691747 57809490572127747103037621)
                  ·
                    refine ⟨5419639741136976290909777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57809490572127747103037621 5419639741136976290909777)
                    ·
                      refine ⟨4064729805852732218182333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419639741136976290909777 4064729805852732218182333)
                      ·
                        rfl

theorem cell23_7916033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_7916033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916033 prefixEnd_7916033 := by exact prefixLift 7916033
  have htrace : WordTrace (prefixWord ++ tailWord_7916033) baseStart_7916033 baseEnd_7916033 := by
    simpa [prefixWord, tailWord_7916033, baseEnd_7916033] using wordTrace_append hprefix tailTrace_7916033
  have hstable : (prefixWord ++ tailWord_7916033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916033).length < 2 ^ (prefixWord ++ tailWord_7916033).sum := by decide
  have hdescent : baseEnd_7916033 < baseStart_7916033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916043 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 1, 5]
def baseStart_7916043 : Nat := 118140960795 + 7916043 * 2 ^ 59
def prefixEnd_7916043 : Nat := 4983230072969 + 3 ^ 40 * 7916043 * 2
def baseEnd_7916043 : Nat := 1354911646886425726352429

theorem tailTrace_7916043 : CollatzResearch.WordTrace tailWord_7916043 prefixEnd_7916043 1354911646886425726352429 := by
  unfold tailWord_7916043
  simp only [CollatzResearch.WordTrace]
  refine ⟨288721807660535638355072783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192481205107023758903381855 288721807660535638355072783)
  ·
    refine ⟨433082711490803457532609175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288721807660535638355072783 433082711490803457532609175)
    ·
      refine ⟨649624067236205186298913763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433082711490803457532609175 649624067236205186298913763)
      ·
        refine ⟨974436100854307779448370645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649624067236205186298913763 974436100854307779448370645)
        ·
          refine ⟨22838346113772838580821187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 974436100854307779448370645 22838346113772838580821187)
          ·
            refine ⟨34257519170659257871231781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22838346113772838580821187 34257519170659257871231781)
            ·
              refine ⟨6423284844498610850855959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34257519170659257871231781 6423284844498610850855959)
              ·
                refine ⟨9634927266747916276283939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423284844498610850855959 9634927266747916276283939)
                ·
                  refine ⟨14452390900121874414425909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634927266747916276283939 14452390900121874414425909)
                  ·
                    refine ⟨1354911646886425726352429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14452390900121874414425909 1354911646886425726352429)
                    ·
                      rfl

theorem cell23_7916043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 5].length) (baseStart_7916043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916043 prefixEnd_7916043 := by exact prefixLift 7916043
  have htrace : WordTrace (prefixWord ++ tailWord_7916043) baseStart_7916043 baseEnd_7916043 := by
    simpa [prefixWord, tailWord_7916043, baseEnd_7916043] using wordTrace_append hprefix tailTrace_7916043
  have hstable : (prefixWord ++ tailWord_7916043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916043).length < 2 ^ (prefixWord ++ tailWord_7916043).sum := by decide
  have hdescent : baseEnd_7916043 < baseStart_7916043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916083 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 3]
def baseStart_7916083 : Nat := 118140960795 + 7916083 * 2 ^ 59
def prefixEnd_7916083 : Nat := 4983230072969 + 3 ^ 40 * 7916083 * 2
def baseEnd_7916083 : Nat := 4064755479885457022557103

theorem tailTrace_7916083 : CollatzResearch.WordTrace tailWord_7916083 prefixEnd_7916083 4064755479885457022557103 := by
  unfold tailWord_7916083
  simp only [CollatzResearch.WordTrace]
  refine ⟨288723266580390725186528903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192482177720260483457685935 288723266580390725186528903)
  ·
    refine ⟨433084899870586087779793355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288723266580390725186528903 433084899870586087779793355)
    ·
      refine ⟨649627349805879131669690033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433084899870586087779793355 649627349805879131669690033)
      ·
        refine ⟨487220512354409348752267525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649627349805879131669690033 487220512354409348752267525)
        ·
          refine ⟨91353846066451752891050161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487220512354409348752267525 91353846066451752891050161)
          ·
            refine ⟨68515384549838814668287621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91353846066451752891050161 68515384549838814668287621)
            ·
              refine ⟨12846634603094777750303929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68515384549838814668287621 12846634603094777750303929)
              ·
                refine ⟨9634975952321083312727947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12846634603094777750303929 9634975952321083312727947)
                ·
                  refine ⟨14452463928481624969091921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634975952321083312727947 14452463928481624969091921)
                  ·
                    refine ⟨10839347946361218726818941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14452463928481624969091921 10839347946361218726818941)
                    ·
                      refine ⟨4064755479885457022557103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839347946361218726818941 4064755479885457022557103)
                      ·
                        rfl

theorem cell23_7916083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_7916083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916083 prefixEnd_7916083 := by exact prefixLift 7916083
  have htrace : WordTrace (prefixWord ++ tailWord_7916083) baseStart_7916083 baseEnd_7916083 := by
    simpa [prefixWord, tailWord_7916083, baseEnd_7916083] using wordTrace_append hprefix tailTrace_7916083
  have hstable : (prefixWord ++ tailWord_7916083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916083).length < 2 ^ (prefixWord ++ tailWord_7916083).sum := by decide
  have hdescent : baseEnd_7916083 < baseStart_7916083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916096 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_7916096 : Nat := 118140960795 + 7916096 * 2 ^ 59
def prefixEnd_7916096 : Nat := 4983230072969 + 3 ^ 40 * 7916096 * 2
def baseEnd_7916096 : Nat := 4064762155133965471694543

theorem tailTrace_7916096 : CollatzResearch.WordTrace tailWord_7916096 prefixEnd_7916096 4064762155133965471694543 := by
  unfold tailWord_7916096
  simp only [CollatzResearch.WordTrace]
  refine ⟨144361870364671814203376071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192482493819562418937834761 144361870364671814203376071)
  ·
    refine ⟨216542805547007721305064107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144361870364671814203376071 216542805547007721305064107)
    ·
      refine ⟨324814208320511581957596161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216542805547007721305064107 324814208320511581957596161)
      ·
        refine ⟨243610656240383686468197121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324814208320511581957596161 243610656240383686468197121)
        ·
          refine ⟨182707992180287764851147841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243610656240383686468197121 182707992180287764851147841)
          ·
            refine ⟨137030994135215823638360881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182707992180287764851147841 137030994135215823638360881)
            ·
              refine ⟨102773245601411867728770661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137030994135215823638360881 102773245601411867728770661)
              ·
                refine ⟨19269983550264725199144499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102773245601411867728770661 19269983550264725199144499)
                ·
                  refine ⟨28904975325397087798716749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19269983550264725199144499 28904975325397087798716749)
                  ·
                    refine ⟨10839365747023907924518781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28904975325397087798716749 10839365747023907924518781)
                    ·
                      refine ⟨4064762155133965471694543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839365747023907924518781 4064762155133965471694543)
                      ·
                        rfl

theorem cell23_7916096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_7916096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916096 prefixEnd_7916096 := by exact prefixLift 7916096
  have htrace : WordTrace (prefixWord ++ tailWord_7916096) baseStart_7916096 baseEnd_7916096 := by
    simpa [prefixWord, tailWord_7916096, baseEnd_7916096] using wordTrace_append hprefix tailTrace_7916096
  have hstable : (prefixWord ++ tailWord_7916096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916096).length < 2 ^ (prefixWord ++ tailWord_7916096).sum := by decide
  have hdescent : baseEnd_7916096 < baseStart_7916096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916113 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_7916113 : Nat := 118140960795 + 7916113 * 2 ^ 59
def prefixEnd_7916113 : Nat := 4983230072969 + 3 ^ 40 * 7916113 * 2
def baseEnd_7916113 : Nat := 4064770884305091905181965

theorem tailTrace_7916113 : CollatzResearch.WordTrace tailWord_7916113 prefixEnd_7916113 4064770884305091905181965 := by
  unfold tailWord_7916113
  simp only [CollatzResearch.WordTrace]
  refine ⟨288724360770282040310120993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192482907180188026873413995 288724360770282040310120993)
  ·
    refine ⟨216543270577711530232590745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288724360770282040310120993 216543270577711530232590745)
    ·
      refine ⟨162407452933283647674443059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216543270577711530232590745 162407452933283647674443059)
      ·
        refine ⟨243611179399925471511664589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162407452933283647674443059 243611179399925471511664589)
        ·
          refine ⟨91354192274972051816874221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243611179399925471511664589 91354192274972051816874221)
          ·
            refine ⟨34257822103114519431327833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91354192274972051816874221 34257822103114519431327833)
            ·
              refine ⟨25693366577335889573495875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34257822103114519431327833 25693366577335889573495875)
              ·
                refine ⟨38540049866003834360243813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25693366577335889573495875 38540049866003834360243813)
                ·
                  refine ⟨7226259349875718942545715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38540049866003834360243813 7226259349875718942545715)
                  ·
                    refine ⟨10839389024813578413818573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7226259349875718942545715 10839389024813578413818573)
                    ·
                      refine ⟨4064770884305091905181965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839389024813578413818573 4064770884305091905181965)
                      ·
                        rfl

theorem cell23_7916113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_7916113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916113 prefixEnd_7916113 := by exact prefixLift 7916113
  have htrace : WordTrace (prefixWord ++ tailWord_7916113) baseStart_7916113 baseEnd_7916113 := by
    simpa [prefixWord, tailWord_7916113, baseEnd_7916113] using wordTrace_append hprefix tailTrace_7916113
  have hstable : (prefixWord ++ tailWord_7916113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916113).length < 2 ^ (prefixWord ++ tailWord_7916113).sum := by decide
  have hdescent : baseEnd_7916113 < baseStart_7916113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916114 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_7916114 : Nat := 118140960795 + 7916114 * 2 ^ 59
def prefixEnd_7916114 : Nat := 4983230072969 + 3 ^ 40 * 7916114 * 2
def baseEnd_7916114 : Nat := 4064771397785746401269461

theorem tailTrace_7916114 : CollatzResearch.WordTrace tailWord_7916114 prefixEnd_7916114 4064771397785746401269461 := by
  unfold tailWord_7916114
  simp only [CollatzResearch.WordTrace]
  refine ⟨72181099310819604370226849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192482931495518944987271597 72181099310819604370226849)
  ·
    refine ⟨54135824483114703277670137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72181099310819604370226849 54135824483114703277670137)
    ·
      refine ⟨40601868362336027458252603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54135824483114703277670137 40601868362336027458252603)
      ·
        refine ⟨60902802543504041187378905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40601868362336027458252603 60902802543504041187378905)
        ·
          refine ⟨45677101907628030890534179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60902802543504041187378905 45677101907628030890534179)
          ·
            refine ⟨68515652861442046335801269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45677101907628030890534179 68515652861442046335801269)
            ·
              refine ⟨6423342455760191843981369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68515652861442046335801269 6423342455760191843981369)
              ·
                refine ⟨4817506841820143882986027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423342455760191843981369 4817506841820143882986027)
                ·
                  refine ⟨7226260262730215824479041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817506841820143882986027 7226260262730215824479041)
                  ·
                    refine ⟨5419695197047661868359281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226260262730215824479041 5419695197047661868359281)
                    ·
                      refine ⟨4064771397785746401269461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419695197047661868359281 4064771397785746401269461)
                      ·
                        rfl

theorem cell23_7916114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_7916114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916114 prefixEnd_7916114 := by exact prefixLift 7916114
  have htrace : WordTrace (prefixWord ++ tailWord_7916114) baseStart_7916114 baseEnd_7916114 := by
    simpa [prefixWord, tailWord_7916114, baseEnd_7916114] using wordTrace_append hprefix tailTrace_7916114
  have hstable : (prefixWord ++ tailWord_7916114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916114).length < 2 ^ (prefixWord ++ tailWord_7916114).sum := by decide
  have hdescent : baseEnd_7916114 < baseStart_7916114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916124 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_7916124 : Nat := 118140960795 + 7916124 * 2 ^ 59
def prefixEnd_7916124 : Nat := 4983230072969 + 3 ^ 40 * 7916124 * 2
def baseEnd_7916124 : Nat := 1354925510864097120714805

theorem tailTrace_7916124 : CollatzResearch.WordTrace tailWord_7916124 prefixEnd_7916124 1354925510864097120714805 := by
  unfold tailWord_7916124
  simp only [CollatzResearch.WordTrace]
  refine ⟨144362380986621094594385713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192483174648828126125847617 144362380986621094594385713)
  ·
    refine ⟨108271785739965820945789285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144362380986621094594385713 108271785739965820945789285)
    ·
      refine ⟨20300959826243591427335491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108271785739965820945789285 20300959826243591427335491)
      ·
        refine ⟨30451439739365387141003237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20300959826243591427335491 30451439739365387141003237)
        ·
          refine ⟨5709644951131010088938107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30451439739365387141003237 5709644951131010088938107)
          ·
            refine ⟨8564467426696515133407161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709644951131010088938107 8564467426696515133407161)
            ·
              refine ⟨6423350570022386350055371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8564467426696515133407161 6423350570022386350055371)
              ·
                refine ⟨9635025855033579525083057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423350570022386350055371 9635025855033579525083057)
                ·
                  refine ⟨7226269391275184643812293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9635025855033579525083057 7226269391275184643812293)
                  ·
                    refine ⟨1354925510864097120714805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7226269391275184643812293 1354925510864097120714805)
                    ·
                      rfl

theorem cell23_7916124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_7916124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916124 prefixEnd_7916124 := by exact prefixLift 7916124
  have htrace : WordTrace (prefixWord ++ tailWord_7916124) baseStart_7916124 baseEnd_7916124 := by
    simpa [prefixWord, tailWord_7916124, baseEnd_7916124] using wordTrace_append hprefix tailTrace_7916124
  have hstable : (prefixWord ++ tailWord_7916124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916124).length < 2 ^ (prefixWord ++ tailWord_7916124).sum := by decide
  have hdescent : baseEnd_7916124 < baseStart_7916124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916140 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_7916140 : Nat := 118140960795 + 7916140 * 2 ^ 59
def prefixEnd_7916140 : Nat := 4983230072969 + 3 ^ 40 * 7916140 * 2
def baseEnd_7916140 : Nat := 4064784748282763299544341

theorem tailTrace_7916140 : CollatzResearch.WordTrace tailWord_7916140 prefixEnd_7916140 4064784748282763299544341 := by
  unfold tailWord_7916140
  simp only [CollatzResearch.WordTrace]
  refine ⟨144362672770592111960676937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192483563694122815947569249 144362672770592111960676937)
  ·
    refine ⟨108272004577944083970507703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144362672770592111960676937 108272004577944083970507703)
    ·
      refine ⟨162408006866916125955761555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108272004577944083970507703 162408006866916125955761555)
      ·
        refine ⟨243612010300374188933642333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162408006866916125955761555 243612010300374188933642333)
        ·
          refine ⟨91354503862640320850115875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243612010300374188933642333 91354503862640320850115875)
          ·
            refine ⟨137031755793960481275173813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91354503862640320850115875 137031755793960481275173813)
            ·
              refine ⟨12846727105683795119547545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137031755793960481275173813 12846727105683795119547545)
              ·
                refine ⟨9635045329262846339660659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12846727105683795119547545 9635045329262846339660659)
                ·
                  refine ⟨14452567993894269509490989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635045329262846339660659 14452567993894269509490989)
                  ·
                    refine ⟨5419712997710351066059121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14452567993894269509490989 5419712997710351066059121)
                    ·
                      refine ⟨4064784748282763299544341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419712997710351066059121 4064784748282763299544341)
                      ·
                        rfl

theorem cell23_7916140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_7916140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916140 prefixEnd_7916140 := by exact prefixLift 7916140
  have htrace : WordTrace (prefixWord ++ tailWord_7916140) baseStart_7916140 baseEnd_7916140 := by
    simpa [prefixWord, tailWord_7916140, baseEnd_7916140] using wordTrace_append hprefix tailTrace_7916140
  have hstable : (prefixWord ++ tailWord_7916140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916140).length < 2 ^ (prefixWord ++ tailWord_7916140).sum := by decide
  have hdescent : baseEnd_7916140 < baseStart_7916140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916153 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 4, 2]
def baseStart_7916153 : Nat := 118140960795 + 7916153 * 2 ^ 59
def prefixEnd_7916153 : Nat := 4983230072969 + 3 ^ 40 * 7916153 * 2
def baseEnd_7916153 : Nat := 4064791423531271748681781

theorem tailTrace_7916153 : CollatzResearch.WordTrace tailWord_7916153 prefixEnd_7916153 4064791423531271748681781 := by
  unfold tailWord_7916153
  simp only [CollatzResearch.WordTrace]
  refine ⟨288725819690137127141577113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192483879793424751427718075 288725819690137127141577113)
  ·
    refine ⟨216544364767602845356182835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288725819690137127141577113 216544364767602845356182835)
    ·
      refine ⟨324816547151404268034274253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216544364767602845356182835 324816547151404268034274253)
      ·
        refine ⟨121806205181776600512852845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324816547151404268034274253 121806205181776600512852845)
        ·
          refine ⟨45677326943166225192319817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121806205181776600512852845 45677326943166225192319817)
          ·
            refine ⟨34257995207374668894239863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45677326943166225192319817 34257995207374668894239863)
            ·
              refine ⟨51386992811062003341359795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34257995207374668894239863 51386992811062003341359795)
              ·
                refine ⟨77080489216593005012039693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51386992811062003341359795 77080489216593005012039693)
                ·
                  refine ⟨28905183456222376879514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77080489216593005012039693 28905183456222376879514885)
                  ·
                    refine ⟨5419721898041695664909041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28905183456222376879514885 5419721898041695664909041)
                    ·
                      refine ⟨4064791423531271748681781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419721898041695664909041 4064791423531271748681781)
                      ·
                        rfl

theorem cell23_7916153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_7916153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916153 prefixEnd_7916153 := by exact prefixLift 7916153
  have htrace : WordTrace (prefixWord ++ tailWord_7916153) baseStart_7916153 baseEnd_7916153 := by
    simpa [prefixWord, tailWord_7916153, baseEnd_7916153] using wordTrace_append hprefix tailTrace_7916153
  have hstable : (prefixWord ++ tailWord_7916153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916153).length < 2 ^ (prefixWord ++ tailWord_7916153).sum := by decide
  have hdescent : baseEnd_7916153 < baseStart_7916153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916156 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_7916156 : Nat := 118140960795 + 7916156 * 2 ^ 59
def prefixEnd_7916156 : Nat := 4983230072969 + 3 ^ 40 * 7916156 * 2
def baseEnd_7916156 : Nat := 4064792963973235236944267

theorem tailTrace_7916156 : CollatzResearch.WordTrace tailWord_7916156 prefixEnd_7916156 4064792963973235236944267 := by
  unfold tailWord_7916156
  simp only [CollatzResearch.WordTrace]
  refine ⟨144362964554563129326968161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192483952739417505769290881 144362964554563129326968161)
  ·
    refine ⟨108272223415922346995226121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144362964554563129326968161 108272223415922346995226121)
    ·
      refine ⟨81204167561941760246419591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108272223415922346995226121 81204167561941760246419591)
      ·
        refine ⟨121806251342912640369629387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81204167561941760246419591 121806251342912640369629387)
        ·
          refine ⟨182709377014368960554444081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121806251342912640369629387 182709377014368960554444081)
          ·
            refine ⟨137032032760776720415833061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182709377014368960554444081 137032032760776720415833061)
            ·
              refine ⟨25693506142645635077968699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137032032760776720415833061 25693506142645635077968699)
              ·
                refine ⟨38540259213968452616953049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25693506142645635077968699 38540259213968452616953049)
                ·
                  refine ⟨28905194410476339462714787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38540259213968452616953049 28905194410476339462714787)
                  ·
                    refine ⟨43357791615714509194072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28905194410476339462714787 43357791615714509194072181)
                    ·
                      refine ⟨4064792963973235236944267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43357791615714509194072181 4064792963973235236944267)
                      ·
                        rfl

theorem cell23_7916156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_7916156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916156 prefixEnd_7916156 := by exact prefixLift 7916156
  have htrace : WordTrace (prefixWord ++ tailWord_7916156) baseStart_7916156 baseEnd_7916156 := by
    simpa [prefixWord, tailWord_7916156, baseEnd_7916156] using wordTrace_append hprefix tailTrace_7916156
  have hstable : (prefixWord ++ tailWord_7916156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916156).length < 2 ^ (prefixWord ++ tailWord_7916156).sum := by decide
  have hdescent : baseEnd_7916156 < baseStart_7916156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916159 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 11]
def baseStart_7916159 : Nat := 118140960795 + 7916159 * 2 ^ 59
def prefixEnd_7916159 : Nat := 4983230072969 + 3 ^ 40 * 7916159 * 2
def baseEnd_7916159 : Nat := 451643833823910969467417

theorem tailTrace_7916159 : CollatzResearch.WordTrace tailWord_7916159 prefixEnd_7916159 451643833823910969467417 := by
  unfold tailWord_7916159
  simp only [CollatzResearch.WordTrace]
  refine ⟨288726038528115390166295531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192484025685410260110863687 288726038528115390166295531)
  ·
    refine ⟨433089057792173085249443297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288726038528115390166295531 433089057792173085249443297)
    ·
      refine ⟨324816793344129813937082473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433089057792173085249443297 324816793344129813937082473)
      ·
        refine ⟨243612595008097360452811855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324816793344129813937082473 243612595008097360452811855)
        ·
          refine ⟨365418892512146040679217783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243612595008097360452811855 365418892512146040679217783)
          ·
            refine ⟨548128338768219061018826675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365418892512146040679217783 548128338768219061018826675)
            ·
              refine ⟨822192508152328591528240013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548128338768219061018826675 822192508152328591528240013)
              ·
                refine ⟨308322190557123221823090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822192508152328591528240013 308322190557123221823090005)
                ·
                  refine ⟨451643833823910969467417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 308322190557123221823090005 451643833823910969467417)
                  ·
                    rfl

theorem cell23_7916159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 11].length) (baseStart_7916159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916159 prefixEnd_7916159 := by exact prefixLift 7916159
  have htrace : WordTrace (prefixWord ++ tailWord_7916159) baseStart_7916159 baseEnd_7916159 := by
    simpa [prefixWord, tailWord_7916159, baseEnd_7916159] using wordTrace_append hprefix tailTrace_7916159
  have hstable : (prefixWord ++ tailWord_7916159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916159).length < 2 ^ (prefixWord ++ tailWord_7916159).sum := by decide
  have hdescent : baseEnd_7916159 < baseStart_7916159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916193 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 7]
def baseStart_7916193 : Nat := 118140960795 + 7916193 * 2 ^ 59
def prefixEnd_7916193 : Nat := 4983230072969 + 3 ^ 40 * 7916193 * 2
def baseEnd_7916193 : Nat := 451645773639716843575733

theorem tailTrace_7916193 : CollatzResearch.WordTrace tailWord_7916193 prefixEnd_7916193 451645773639716843575733 := by
  unfold tailWord_7916193
  simp only [CollatzResearch.WordTrace]
  refine ⟨288727278609992213973033233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192484852406661475982022155 288727278609992213973033233)
  ·
    refine ⟨216545458957494160479774925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288727278609992213973033233 216545458957494160479774925)
    ·
      refine ⟨81204547109060310179915597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216545458957494160479774925 81204547109060310179915597)
      ·
        refine ⟨30451705165897616317468349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81204547109060310179915597 30451705165897616317468349)
        ·
          refine ⟨11419389437211606119050631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30451705165897616317468349 11419389437211606119050631)
          ·
            refine ⟨17129084155817409178575947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11419389437211606119050631 17129084155817409178575947)
            ·
              refine ⟨25693626233726113767863921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17129084155817409178575947 25693626233726113767863921)
              ·
                refine ⟨19270219675294585325897941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25693626233726113767863921 19270219675294585325897941)
                ·
                  refine ⟨451645773639716843575733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19270219675294585325897941 451645773639716843575733)
                  ·
                    rfl

theorem cell23_7916193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_7916193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916193 prefixEnd_7916193 := by exact prefixLift 7916193
  have htrace : WordTrace (prefixWord ++ tailWord_7916193) baseStart_7916193 baseEnd_7916193 := by
    simpa [prefixWord, tailWord_7916193, baseEnd_7916193] using wordTrace_append hprefix tailTrace_7916193
  have hstable : (prefixWord ++ tailWord_7916193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916193).length < 2 ^ (prefixWord ++ tailWord_7916193).sum := by decide
  have hdescent : baseEnd_7916193 < baseStart_7916193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916256 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_7916256 : Nat := 118140960795 + 7916256 * 2 ^ 59
def prefixEnd_7916256 : Nat := 4983230072969 + 3 ^ 40 * 7916256 * 2
def baseEnd_7916256 : Nat := 4064844312038684845693807

theorem tailTrace_7916256 : CollatzResearch.WordTrace tailWord_7916256 prefixEnd_7916256 4064844312038684845693807 := by
  unfold tailWord_7916256
  simp only [CollatzResearch.WordTrace]
  refine ⟨144364788204381987866288311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192486384272509317155051081 144364788204381987866288311)
  ·
    refine ⟨216547182306572981799432467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144364788204381987866288311 216547182306572981799432467)
    ·
      refine ⟨324820773459859472699148701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216547182306572981799432467 324820773459859472699148701)
      ·
        refine ⟨121807790047447302262180763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324820773459859472699148701 121807790047447302262180763)
        ·
          refine ⟨182711685071170953393271145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121807790047447302262180763 182711685071170953393271145)
          ·
            refine ⟨137033763803378215044953359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182711685071170953393271145 137033763803378215044953359)
            ·
              refine ⟨205550645705067322567430039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137033763803378215044953359 205550645705067322567430039)
              ·
                refine ⟨308325968557600983851145059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205550645705067322567430039 308325968557600983851145059)
                ·
                  refine ⟨462488952836401475776717589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308325968557600983851145059 462488952836401475776717589)
                  ·
                    refine ⟨21679169664206319177033637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 462488952836401475776717589 21679169664206319177033637)
                    ·
                      refine ⟨4064844312038684845693807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21679169664206319177033637 4064844312038684845693807)
                      ·
                        rfl

theorem cell23_7916256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_7916256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916256 prefixEnd_7916256 := by exact prefixLift 7916256
  have htrace : WordTrace (prefixWord ++ tailWord_7916256) baseStart_7916256 baseEnd_7916256 := by
    simpa [prefixWord, tailWord_7916256, baseEnd_7916256] using wordTrace_append hprefix tailTrace_7916256
  have hstable : (prefixWord ++ tailWord_7916256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916256).length < 2 ^ (prefixWord ++ tailWord_7916256).sum := by decide
  have hdescent : baseEnd_7916256 < baseStart_7916256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916313 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_7916313 : Nat := 118140960795 + 7916313 * 2 ^ 59
def prefixEnd_7916313 : Nat := 4983230072969 + 3 ^ 40 * 7916313 * 2
def baseEnd_7916313 : Nat := 1354957860145330374227015

theorem tailTrace_7916313 : CollatzResearch.WordTrace tailWord_7916313 prefixEnd_7916313 1354957860145330374227015 := by
  unfold tailWord_7916313
  simp only [CollatzResearch.WordTrace]
  refine ⟨288731655369557474467401593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192487770246371649644934395 288731655369557474467401593)
  ·
    refine ⟨216548741527168105850551195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288731655369557474467401593 216548741527168105850551195)
    ·
      refine ⟨324823112290752158775826793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216548741527168105850551195 324823112290752158775826793)
      ·
        refine ⟨243617334218064119081870095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324823112290752158775826793 243617334218064119081870095)
        ·
          refine ⟨365426001327096178622805143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243617334218064119081870095 365426001327096178622805143)
          ·
            refine ⟨548139001990644267934207715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365426001327096178622805143 548139001990644267934207715)
            ·
              refine ⟨822208502985966401901311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548139001990644267934207715 822208502985966401901311573)
              ·
                refine ⟨9635255894366793772280995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 822208502985966401901311573 9635255894366793772280995)
                ·
                  refine ⟨14452883841550190658421493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635255894366793772280995 14452883841550190658421493)
                  ·
                    refine ⟨1354957860145330374227015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14452883841550190658421493 1354957860145330374227015)
                    ·
                      rfl

theorem cell23_7916313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_7916313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916313 prefixEnd_7916313 := by exact prefixLift 7916313
  have htrace : WordTrace (prefixWord ++ tailWord_7916313) baseStart_7916313 baseEnd_7916313 := by
    simpa [prefixWord, tailWord_7916313, baseEnd_7916313] using wordTrace_append hprefix tailTrace_7916313
  have hstable : (prefixWord ++ tailWord_7916313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916313).length < 2 ^ (prefixWord ++ tailWord_7916313).sum := by decide
  have hdescent : baseEnd_7916313 < baseStart_7916313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916360 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_7916360 : Nat := 118140960795 + 7916360 * 2 ^ 59
def prefixEnd_7916360 : Nat := 4983230072969 + 3 ^ 40 * 7916360 * 2
def baseEnd_7916360 : Nat := 1354965904675584146264443

theorem tailTrace_7916360 : CollatzResearch.WordTrace tailWord_7916360 prefixEnd_7916360 1354965904675584146264443 := by
  unfold tailWord_7916360
  simp only [CollatzResearch.WordTrace]
  refine ⟨144366684800193600747181267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192488913066924800996241689 144366684800193600747181267)
  ·
    refine ⟨216550027200290401120771901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144366684800193600747181267 216550027200290401120771901)
    ·
      refine ⟨81206260200108900420289463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216550027200290401120771901 81206260200108900420289463)
      ·
        refine ⟨121809390300163350630434195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81206260200108900420289463 121809390300163350630434195)
        ·
          refine ⟨182714085450245025945651293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121809390300163350630434195 182714085450245025945651293)
          ·
            refine ⟨68517782043841884729619235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182714085450245025945651293 68517782043841884729619235)
            ·
              refine ⟨102776673065762827094428853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68517782043841884729619235 102776673065762827094428853)
              ·
                refine ⟨9635313099915265040102705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102776673065762827094428853 9635313099915265040102705)
                ·
                  refine ⟨7226484824936448780077029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9635313099915265040102705 7226484824936448780077029)
                  ·
                    refine ⟨1354965904675584146264443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7226484824936448780077029 1354965904675584146264443)
                    ·
                      rfl

theorem cell23_7916360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_7916360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916360 prefixEnd_7916360 := by exact prefixLift 7916360
  have htrace : WordTrace (prefixWord ++ tailWord_7916360) baseStart_7916360 baseEnd_7916360 := by
    simpa [prefixWord, tailWord_7916360, baseEnd_7916360] using wordTrace_append hprefix tailTrace_7916360
  have hstable : (prefixWord ++ tailWord_7916360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916360).length < 2 ^ (prefixWord ++ tailWord_7916360).sum := by decide
  have hdescent : baseEnd_7916360 < baseStart_7916360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916370 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_7916370 : Nat := 118140960795 + 7916370 * 2 ^ 59
def prefixEnd_7916370 : Nat := 4983230072969 + 3 ^ 40 * 7916370 * 2
def baseEnd_7916370 : Nat := 4064902848833297399668283

theorem tailTrace_7916370 : CollatzResearch.WordTrace tailWord_7916370 prefixEnd_7916370 4064902848833297399668283 := by
  unfold tailWord_7916370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72183433582587743300556641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192489156220233982134817709 72183433582587743300556641)
  ·
    refine ⟨54137575186940807475417481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72183433582587743300556641 54137575186940807475417481)
    ·
      refine ⟨40603181390205605606563111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54137575186940807475417481 40603181390205605606563111)
      ·
        refine ⟨60904772085308408409844667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603181390205605606563111 60904772085308408409844667)
        ·
          refine ⟨91357158127962612614767001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60904772085308408409844667 91357158127962612614767001)
          ·
            refine ⟨68517868595971959461075251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91357158127962612614767001 68517868595971959461075251)
            ·
              refine ⟨102776802893957939191612877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68517868595971959461075251 102776802893957939191612877)
              ·
                refine ⟨38541301085234227196854829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102776802893957939191612877 38541301085234227196854829)
                ·
                  refine ⟨14452987906962835198820561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38541301085234227196854829 14452987906962835198820561)
                  ·
                    refine ⟨10839740930222126399115421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14452987906962835198820561 10839740930222126399115421)
                    ·
                      refine ⟨4064902848833297399668283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839740930222126399115421 4064902848833297399668283)
                      ·
                        rfl

theorem cell23_7916370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_7916370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916370 prefixEnd_7916370 := by exact prefixLift 7916370
  have htrace : WordTrace (prefixWord ++ tailWord_7916370) baseStart_7916370 baseEnd_7916370 := by
    simpa [prefixWord, tailWord_7916370, baseEnd_7916370] using wordTrace_append hprefix tailTrace_7916370
  have hstable : (prefixWord ++ tailWord_7916370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916370).length < 2 ^ (prefixWord ++ tailWord_7916370).sum := by decide
  have hdescent : baseEnd_7916370 < baseStart_7916370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916387 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7916387 : Nat := 118140960795 + 7916387 * 2 ^ 59
def prefixEnd_7916387 : Nat := 4983230072969 + 3 ^ 40 * 7916387 * 2
def baseEnd_7916387 : Nat := 4064911578004423833155705

theorem tailTrace_7916387 : CollatzResearch.WordTrace tailWord_7916387 prefixEnd_7916387 4064911578004423833155705 := by
  unfold tailWord_7916387
  simp only [CollatzResearch.WordTrace]
  refine ⟨288734354371289385105595415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192489569580859590070396943 288734354371289385105595415)
  ·
    refine ⟨433101531556934077658393123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288734354371289385105595415 433101531556934077658393123)
    ·
      refine ⟨649652297335401116487589685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433101531556934077658393123 649652297335401116487589685)
      ·
        refine ⟨60904902875193854670711533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 649652297335401116487589685 60904902875193854670711533)
        ·
          refine ⟨22839338578197695501516825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60904902875193854670711533 22839338578197695501516825)
          ·
            refine ⟨17129503933648271626137619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22839338578197695501516825 17129503933648271626137619)
            ·
              refine ⟨25694255900472407439206429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17129503933648271626137619 25694255900472407439206429)
              ·
                refine ⟨9635345962677152789702411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25694255900472407439206429 9635345962677152789702411)
                ·
                  refine ⟨14453018944015729184553617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635345962677152789702411 14453018944015729184553617)
                  ·
                    refine ⟨10839764208011796888415213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14453018944015729184553617 10839764208011796888415213)
                    ·
                      refine ⟨4064911578004423833155705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839764208011796888415213 4064911578004423833155705)
                      ·
                        rfl

theorem cell23_7916387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7916387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916387 prefixEnd_7916387 := by exact prefixLift 7916387
  have htrace : WordTrace (prefixWord ++ tailWord_7916387) baseStart_7916387 baseEnd_7916387 := by
    simpa [prefixWord, tailWord_7916387, baseEnd_7916387] using wordTrace_append hprefix tailTrace_7916387
  have hstable : (prefixWord ++ tailWord_7916387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916387).length < 2 ^ (prefixWord ++ tailWord_7916387).sum := by decide
  have hdescent : baseEnd_7916387 < baseStart_7916387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916427 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 1, 3, 2]
def baseStart_7916427 : Nat := 118140960795 + 7916427 * 2 ^ 59
def prefixEnd_7916427 : Nat := 4983230072969 + 3 ^ 40 * 7916427 * 2
def baseEnd_7916427 : Nat := 4064932117230603676655521

theorem tailTrace_7916427 : CollatzResearch.WordTrace tailWord_7916427 prefixEnd_7916427 4064932117230603676655521 := by
  unfold tailWord_7916427
  simp only [CollatzResearch.WordTrace]
  refine ⟨288735813291144471937051535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192490542194096314624701023 288735813291144471937051535)
  ·
    refine ⟨433103719936716707905577303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288735813291144471937051535 433103719936716707905577303)
    ·
      refine ⟨649655579905075061858365955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433103719936716707905577303 649655579905075061858365955)
      ·
        refine ⟨974483369857612592787548933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649655579905075061858365955 974483369857612592787548933)
        ·
          refine ⟨182715631848302361147665425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 974483369857612592787548933 182715631848302361147665425)
          ·
            refine ⟨137036723886226770860749069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182715631848302361147665425 137036723886226770860749069)
            ·
              refine ⟨51388771457335039072780901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137036723886226770860749069 51388771457335039072780901)
              ·
                refine ⟨9635394648250319826146419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51388771457335039072780901 9635394648250319826146419)
                ·
                  refine ⟨14453091972375479739219629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635394648250319826146419 14453091972375479739219629)
                  ·
                    refine ⟨5419909489640804902207361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14453091972375479739219629 5419909489640804902207361)
                    ·
                      refine ⟨4064932117230603676655521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419909489640804902207361 4064932117230603676655521)
                      ·
                        rfl

theorem cell23_7916427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3, 2].length) (baseStart_7916427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916427 prefixEnd_7916427 := by exact prefixLift 7916427
  have htrace : WordTrace (prefixWord ++ tailWord_7916427) baseStart_7916427 baseEnd_7916427 := by
    simpa [prefixWord, tailWord_7916427, baseEnd_7916427] using wordTrace_append hprefix tailTrace_7916427
  have hstable : (prefixWord ++ tailWord_7916427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916427).length < 2 ^ (prefixWord ++ tailWord_7916427).sum := by decide
  have hdescent : baseEnd_7916427 < baseStart_7916427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916457 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 4, 2, 2]
def baseStart_7916457 : Nat := 118140960795 + 7916457 * 2 ^ 59
def prefixEnd_7916457 : Nat := 4983230072969 + 3 ^ 40 * 7916457 * 2
def baseEnd_7916457 : Nat := 4064947521650238559280383

theorem tailTrace_7916457 : CollatzResearch.WordTrace tailWord_7916457 prefixEnd_7916457 4064947521650238559280383 := by
  unfold tailWord_7916457
  simp only [CollatzResearch.WordTrace]
  refine ⟨288736907481035787060643625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192491271654023858040429083 288736907481035787060643625)
  ·
    refine ⟨216552680610776840295482719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288736907481035787060643625 216552680610776840295482719)
    ·
      refine ⟨324829020916165260443224079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216552680610776840295482719 324829020916165260443224079)
      ·
        refine ⟨487243531374247890664836119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324829020916165260443224079 487243531374247890664836119)
        ·
          refine ⟨730865297061371835997254179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487243531374247890664836119 730865297061371835997254179)
          ·
            refine ⟨1096297945592057753995881269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730865297061371835997254179 1096297945592057753995881269)
            ·
              refine ⟨102777932399255414437113869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1096297945592057753995881269 102777932399255414437113869)
              ·
                refine ⟨38541724649720780413917701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102777932399255414437113869 38541724649720780413917701)
                ·
                  refine ⟨7226573371822646327609569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38541724649720780413917701 7226573371822646327609569)
                  ·
                    refine ⟨5419930028866984745707177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226573371822646327609569 5419930028866984745707177)
                    ·
                      refine ⟨4064947521650238559280383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419930028866984745707177 4064947521650238559280383)
                      ·
                        rfl

theorem cell23_7916457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2, 2].length) (baseStart_7916457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916457 prefixEnd_7916457 := by exact prefixLift 7916457
  have htrace : WordTrace (prefixWord ++ tailWord_7916457) baseStart_7916457 baseEnd_7916457 := by
    simpa [prefixWord, tailWord_7916457, baseEnd_7916457] using wordTrace_append hprefix tailTrace_7916457
  have hstable : (prefixWord ++ tailWord_7916457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916457).length < 2 ^ (prefixWord ++ tailWord_7916457).sum := by decide
  have hdescent : baseEnd_7916457 < baseStart_7916457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916463 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 7]
def baseStart_7916463 : Nat := 118140960795 + 7916463 * 2 ^ 59
def prefixEnd_7916463 : Nat := 4983230072969 + 3 ^ 40 * 7916463 * 2
def baseEnd_7916463 : Nat := 451661178059351726200595

theorem tailTrace_7916463 : CollatzResearch.WordTrace tailWord_7916463 prefixEnd_7916463 451661178059351726200595 := by
  unfold tailWord_7916463
  simp only [CollatzResearch.WordTrace]
  refine ⟨288737126319014050085362043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192491417546009366723574695 288737126319014050085362043)
  ·
    refine ⟨433105689478521075128043065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288737126319014050085362043 433105689478521075128043065)
    ·
      refine ⟨324829267108890806346032299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433105689478521075128043065 324829267108890806346032299)
      ·
        refine ⟨487243900663336209519048449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324829267108890806346032299 487243900663336209519048449)
        ·
          refine ⟨365432925497502157139286337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487243900663336209519048449 365432925497502157139286337)
          ·
            refine ⟨274074694123126617854464753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365432925497502157139286337 274074694123126617854464753)
            ·
              refine ⟨205556020592344963390848565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274074694123126617854464753 205556020592344963390848565)
              ·
                refine ⟨19270876930532340317892053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205556020592344963390848565 19270876930532340317892053)
                ·
                  refine ⟨451661178059351726200595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19270876930532340317892053 451661178059351726200595)
                  ·
                    rfl

theorem cell23_7916463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 7].length) (baseStart_7916463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916463 prefixEnd_7916463 := by exact prefixLift 7916463
  have htrace : WordTrace (prefixWord ++ tailWord_7916463) baseStart_7916463 baseEnd_7916463 := by
    simpa [prefixWord, tailWord_7916463, baseEnd_7916463] using wordTrace_append hprefix tailTrace_7916463
  have hstable : (prefixWord ++ tailWord_7916463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916463).length < 2 ^ (prefixWord ++ tailWord_7916463).sum := by decide
  have hdescent : baseEnd_7916463 < baseStart_7916463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916468 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_7916468 : Nat := 118140960795 + 7916468 * 2 ^ 59
def prefixEnd_7916468 : Nat := 4983230072969 + 3 ^ 40 * 7916468 * 2
def baseEnd_7916468 : Nat := 4064953169937438016242833

theorem tailTrace_7916468 : CollatzResearch.WordTrace tailWord_7916468 prefixEnd_7916468 4064953169937438016242833 := by
  unfold tailWord_7916468
  simp only [CollatzResearch.WordTrace]
  refine ⟨144368654341997967969647029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192491539122663957292862705 144368654341997967969647029)
  ·
    refine ⟨13534561344562309497154409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144368654341997967969647029 13534561344562309497154409)
    ·
      refine ⟨10150921008421732122865807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13534561344562309497154409 10150921008421732122865807)
      ·
        refine ⟨15226381512632598184298711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10150921008421732122865807 15226381512632598184298711)
        ·
          refine ⟨22839572268948897276448067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15226381512632598184298711 22839572268948897276448067)
          ·
            refine ⟨34259358403423345914672101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22839572268948897276448067 34259358403423345914672101)
            ·
              refine ⟨6423629700641877359001019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34259358403423345914672101 6423629700641877359001019)
              ·
                refine ⟨9635444550962816038501529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423629700641877359001019 9635444550962816038501529)
                ·
                  refine ⟨7226583413222112028876147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9635444550962816038501529 7226583413222112028876147)
                  ·
                    refine ⟨10839875119833168043314221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7226583413222112028876147 10839875119833168043314221)
                    ·
                      refine ⟨4064953169937438016242833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839875119833168043314221 4064953169937438016242833)
                      ·
                        rfl

theorem cell23_7916468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_7916468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916468 prefixEnd_7916468 := by exact prefixLift 7916468
  have htrace : WordTrace (prefixWord ++ tailWord_7916468) baseStart_7916468 baseEnd_7916468 := by
    simpa [prefixWord, tailWord_7916468, baseEnd_7916468] using wordTrace_append hprefix tailTrace_7916468
  have hstable : (prefixWord ++ tailWord_7916468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916468).length < 2 ^ (prefixWord ++ tailWord_7916468).sum := by decide
  have hdescent : baseEnd_7916468 < baseStart_7916468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916474 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_7916474 : Nat := 118140960795 + 7916474 * 2 ^ 59
def prefixEnd_7916474 : Nat := 4983230072969 + 3 ^ 40 * 7916474 * 2
def baseEnd_7916474 : Nat := 4064956250821364992767805

theorem tailTrace_7916474 : CollatzResearch.WordTrace tailWord_7916474 prefixEnd_7916474 4064956250821364992767805 := by
  unfold tailWord_7916474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72184381880493549741003119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192491685014649465976008317 72184381880493549741003119)
  ·
    refine ⟨108276572820740324611504679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72184381880493549741003119 108276572820740324611504679)
    ·
      refine ⟨162414859231110486917257019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108276572820740324611504679 162414859231110486917257019)
      ·
        refine ⟨243622288846665730375885529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162414859231110486917257019 243622288846665730375885529)
        ·
          refine ⟨182716716634999297781914147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243622288846665730375885529 182716716634999297781914147)
          ·
            refine ⟨274075074952498946672871221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182716716634999297781914147 274075074952498946672871221)
            ·
              refine ⟨25694538276796776250581677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274075074952498946672871221 25694538276796776250581677)
              ·
                refine ⟨9635451853798791093968129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25694538276796776250581677 9635451853798791093968129)
                ·
                  refine ⟨7226588890349093320476097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9635451853798791093968129 7226588890349093320476097)
                  ·
                    refine ⟨5419941667761819990357073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226588890349093320476097 5419941667761819990357073)
                    ·
                      refine ⟨4064956250821364992767805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5419941667761819990357073 4064956250821364992767805)
                      ·
                        rfl

theorem cell23_7916474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_7916474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916474 prefixEnd_7916474 := by exact prefixLift 7916474
  have htrace : WordTrace (prefixWord ++ tailWord_7916474) baseStart_7916474 baseEnd_7916474 := by
    simpa [prefixWord, tailWord_7916474, baseEnd_7916474] using wordTrace_append hprefix tailTrace_7916474
  have hstable : (prefixWord ++ tailWord_7916474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916474).length < 2 ^ (prefixWord ++ tailWord_7916474).sum := by decide
  have hdescent : baseEnd_7916474 < baseStart_7916474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916490 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_7916490 : Nat := 118140960795 + 7916490 * 2 ^ 59
def prefixEnd_7916490 : Nat := 4983230072969 + 3 ^ 40 * 7916490 * 2
def baseEnd_7916490 : Nat := 4064964466511836930167731

theorem tailTrace_7916490 : CollatzResearch.WordTrace tailWord_7916490 prefixEnd_7916490 4064964466511836930167731 := by
  unfold tailWord_7916490
  simp only [CollatzResearch.WordTrace]
  refine ⟨72184527772479058424148731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192492074059944155797729949 72184527772479058424148731)
  ·
    refine ⟨108276791658718587636223097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72184527772479058424148731 108276791658718587636223097)
    ·
      refine ⟨81207593744038940727167323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108276791658718587636223097 81207593744038940727167323)
      ·
        refine ⟨121811390616058411090750985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81207593744038940727167323 121811390616058411090750985)
        ·
          refine ⟨91358542962043808318063239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121811390616058411090750985 91358542962043808318063239)
          ·
            refine ⟨137037814443065712477094859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91358542962043808318063239 137037814443065712477094859)
            ·
              refine ⟨205556721664598568715642289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137037814443065712477094859 205556721664598568715642289)
              ·
                refine ⟨154167541248448926536731717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205556721664598568715642289 154167541248448926536731717)
                ·
                  refine ⟨28906413984084173725637197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154167541248448926536731717 28906413984084173725637197)
                  ·
                    refine ⟨10839905244031565147113949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28906413984084173725637197 10839905244031565147113949)
                    ·
                      refine ⟨4064964466511836930167731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10839905244031565147113949 4064964466511836930167731)
                      ·
                        rfl

theorem cell23_7916490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_7916490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916490 prefixEnd_7916490 := by exact prefixLift 7916490
  have htrace : WordTrace (prefixWord ++ tailWord_7916490) baseStart_7916490 baseEnd_7916490 := by
    simpa [prefixWord, tailWord_7916490, baseEnd_7916490] using wordTrace_append hprefix tailTrace_7916490
  have hstable : (prefixWord ++ tailWord_7916490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916490).length < 2 ^ (prefixWord ++ tailWord_7916490).sum := by decide
  have hdescent : baseEnd_7916490 < baseStart_7916490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916520 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7916520 : Nat := 118140960795 + 7916520 * 2 ^ 59
def prefixEnd_7916520 : Nat := 4983230072969 + 3 ^ 40 * 7916520 * 2
def baseEnd_7916520 : Nat := 4064979870931471812792593

theorem tailTrace_7916520 : CollatzResearch.WordTrace tailWord_7916520 prefixEnd_7916520 4064979870931471812792593 := by
  unfold tailWord_7916520
  simp only [CollatzResearch.WordTrace]
  refine ⟨144369602639903774410093507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192492803519871699213458009 144369602639903774410093507)
  ·
    refine ⟨216554403959855661615140261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144369602639903774410093507 216554403959855661615140261)
    ·
      refine ⟨40603950742472936552838799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216554403959855661615140261 40603950742472936552838799)
      ·
        refine ⟨60905926113709404829258199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603950742472936552838799 60905926113709404829258199)
        ·
          refine ⟨91358889170564107243887299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60905926113709404829258199 91358889170564107243887299)
          ·
            refine ⟨137038333755846160865830949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91358889170564107243887299 137038333755846160865830949)
            ·
              refine ⟨25694687579221155162343303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137038333755846160865830949 25694687579221155162343303)
              ·
                refine ⟨38542031368831732743514955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25694687579221155162343303 38542031368831732743514955)
                ·
                  refine ⟨57813047053247599115272433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38542031368831732743514955 57813047053247599115272433)
                  ·
                    refine ⟨43359785289935699336454325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57813047053247599115272433 43359785289935699336454325)
                    ·
                      refine ⟨4064979870931471812792593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43359785289935699336454325 4064979870931471812792593)
                      ·
                        rfl

theorem cell23_7916520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7916520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916520 prefixEnd_7916520 := by exact prefixLift 7916520
  have htrace : WordTrace (prefixWord ++ tailWord_7916520) baseStart_7916520 baseEnd_7916520 := by
    simpa [prefixWord, tailWord_7916520, baseEnd_7916520] using wordTrace_append hprefix tailTrace_7916520
  have hstable : (prefixWord ++ tailWord_7916520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916520).length < 2 ^ (prefixWord ++ tailWord_7916520).sum := by decide
  have hdescent : baseEnd_7916520 < baseStart_7916520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916523 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 8]
def baseStart_7916523 : Nat := 118140960795 + 7916523 * 2 ^ 59
def prefixEnd_7916523 : Nat := 4983230072969 + 3 ^ 40 * 7916523 * 2
def baseEnd_7916523 : Nat := 1354993803791145100351693

theorem tailTrace_7916523 : CollatzResearch.WordTrace tailWord_7916523 prefixEnd_7916523 1354993803791145100351693 := by
  unfold tailWord_7916523
  simp only [CollatzResearch.WordTrace]
  refine ⟨288739314698796680332546223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192492876465864453555030815 288739314698796680332546223)
  ·
    refine ⟨433108972048195020498819335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288739314698796680332546223 433108972048195020498819335)
    ·
      refine ⟨649663458072292530748229003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433108972048195020498819335 649663458072292530748229003)
      ·
        refine ⟨974495187108438796122343505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649663458072292530748229003 974495187108438796122343505)
        ·
          refine ⟨730871390331329097091757629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974495187108438796122343505 730871390331329097091757629)
          ·
            refine ⟨274076771374248411409409111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730871390331329097091757629 274076771374248411409409111)
            ·
              refine ⟨411115157061372617114113667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274076771374248411409409111 411115157061372617114113667)
              ·
                refine ⟨616672735592058925671170501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411115157061372617114113667 616672735592058925671170501)
                ·
                  refine ⟨115626137923511048563344469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616672735592058925671170501 115626137923511048563344469)
                  ·
                    refine ⟨1354993803791145100351693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115626137923511048563344469 1354993803791145100351693)
                    ·
                      rfl

theorem cell23_7916523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_7916523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916523 prefixEnd_7916523 := by exact prefixLift 7916523
  have htrace : WordTrace (prefixWord ++ tailWord_7916523) baseStart_7916523 baseEnd_7916523 := by
    simpa [prefixWord, tailWord_7916523, baseEnd_7916523] using wordTrace_append hprefix tailTrace_7916523
  have hstable : (prefixWord ++ tailWord_7916523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916523).length < 2 ^ (prefixWord ++ tailWord_7916523).sum := by decide
  have hdescent : baseEnd_7916523 < baseStart_7916523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916570 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_7916570 : Nat := 118140960795 + 7916570 * 2 ^ 59
def prefixEnd_7916570 : Nat := 4983230072969 + 3 ^ 40 * 7916570 * 2
def baseEnd_7916570 : Nat := 451667282773799624129707

theorem tailTrace_7916570 : CollatzResearch.WordTrace tailWord_7916570 prefixEnd_7916570 451667282773799624129707 := by
  unfold tailWord_7916570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72185257232406601839876791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192494019286417604906338109 72185257232406601839876791)
  ·
    refine ⟨108277885848609902759815187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72185257232406601839876791 108277885848609902759815187)
    ·
      refine ⟨162416828772914854139722781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108277885848609902759815187 162416828772914854139722781)
      ·
        refine ⟨60906310789843070302396043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162416828772914854139722781 60906310789843070302396043)
        ·
          refine ⟨91359466184764605453594065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60906310789843070302396043 91359466184764605453594065)
          ·
            refine ⟨68519599638573454090195549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91359466184764605453594065 68519599638573454090195549)
            ·
              refine ⟨25694849864465045283823331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68519599638573454090195549 25694849864465045283823331)
              ·
                refine ⟨38542274796697567925734997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25694849864465045283823331 38542274796697567925734997)
                ·
                  refine ⟨451667282773799624129707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38542274796697567925734997 451667282773799624129707)
                  ·
                    rfl

theorem cell23_7916570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_7916570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916570 prefixEnd_7916570 := by exact prefixLift 7916570
  have htrace : WordTrace (prefixWord ++ tailWord_7916570) baseStart_7916570 baseEnd_7916570 := by
    simpa [prefixWord, tailWord_7916570, baseEnd_7916570] using wordTrace_append hprefix tailTrace_7916570
  have hstable : (prefixWord ++ tailWord_7916570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916570).length < 2 ^ (prefixWord ++ tailWord_7916570).sum := by decide
  have hdescent : baseEnd_7916570 < baseStart_7916570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916587 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 6]
def baseStart_7916587 : Nat := 118140960795 + 7916587 * 2 ^ 59
def prefixEnd_7916587 : Nat := 4983230072969 + 3 ^ 40 * 7916587 * 2
def baseEnd_7916587 : Nat := 451668252681702561183865

theorem tailTrace_7916587 : CollatzResearch.WordTrace tailWord_7916587 prefixEnd_7916587 451668252681702561183865 := by
  unfold tailWord_7916587
  simp only [CollatzResearch.WordTrace]
  refine ⟨288741648970564819262876015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192494432647043212841917343 288741648970564819262876015)
  ·
    refine ⟨433112473455847228894314023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288741648970564819262876015 433112473455847228894314023)
    ·
      refine ⟨649668710183770843341471035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433112473455847228894314023 649668710183770843341471035)
      ·
        refine ⟨974503065275656265012206553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649668710183770843341471035 974503065275656265012206553)
        ·
          refine ⟨730877298956742198759154915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974503065275656265012206553 730877298956742198759154915)
          ·
            refine ⟨1096315948435113298138732373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730877298956742198759154915 1096315948435113298138732373)
            ·
              refine ⟨6423726260361991981281635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1096315948435113298138732373 6423726260361991981281635)
              ·
                refine ⟨9635589390542987971922453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423726260361991981281635 9635589390542987971922453)
                ·
                  refine ⟨451668252681702561183865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9635589390542987971922453 451668252681702561183865)
                  ·
                    rfl

theorem cell23_7916587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 6].length) (baseStart_7916587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916587 prefixEnd_7916587 := by exact prefixLift 7916587
  have htrace : WordTrace (prefixWord ++ tailWord_7916587) baseStart_7916587 baseEnd_7916587 := by
    simpa [prefixWord, tailWord_7916587, baseEnd_7916587] using wordTrace_append hprefix tailTrace_7916587
  have hstable : (prefixWord ++ tailWord_7916587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916587).length < 2 ^ (prefixWord ++ tailWord_7916587).sum := by decide
  have hdescent : baseEnd_7916587 < baseStart_7916587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916638 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7916638 : Nat := 118140960795 + 7916638 * 2 ^ 59
def prefixEnd_7916638 : Nat := 4983230072969 + 3 ^ 40 * 7916638 * 2
def baseEnd_7916638 : Nat := 451671162405411372346339

theorem tailTrace_7916638 : CollatzResearch.WordTrace tailWord_7916638 prefixEnd_7916638 451671162405411372346339 := by
  unfold tailWord_7916638
  simp only [CollatzResearch.WordTrace]
  refine ⟨36092938636672506871622821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192495672728920036648655045 36092938636672506871622821)
  ·
    refine ⟨6767425994376095038429279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36092938636672506871622821 6767425994376095038429279)
    ·
      refine ⟨10151138991564142557643919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767425994376095038429279 10151138991564142557643919)
      ·
        refine ⟨15226708487346213836465879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151138991564142557643919 15226708487346213836465879)
        ·
          refine ⟨22840062731019320754698819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15226708487346213836465879 22840062731019320754698819)
          ·
            refine ⟨34260094096528981132048229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22840062731019320754698819 34260094096528981132048229)
            ·
              refine ⟨6423767643099183962259043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34260094096528981132048229 6423767643099183962259043)
              ·
                refine ⟨9635651464648775943388565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423767643099183962259043 9635651464648775943388565)
                ·
                  refine ⟨451671162405411372346339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9635651464648775943388565 451671162405411372346339)
                  ·
                    rfl

theorem cell23_7916638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7916638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916638 prefixEnd_7916638 := by exact prefixLift 7916638
  have htrace : WordTrace (prefixWord ++ tailWord_7916638) baseStart_7916638 baseEnd_7916638 := by
    simpa [prefixWord, tailWord_7916638, baseEnd_7916638] using wordTrace_append hprefix tailTrace_7916638
  have hstable : (prefixWord ++ tailWord_7916638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916638).length < 2 ^ (prefixWord ++ tailWord_7916638).sum := by decide
  have hdescent : baseEnd_7916638 < baseStart_7916638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916654 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7916654 : Nat := 118140960795 + 7916654 * 2 ^ 59
def prefixEnd_7916654 : Nat := 4983230072969 + 3 ^ 40 * 7916654 * 2
def baseEnd_7916654 : Nat := 4065048677339174288516977

theorem tailTrace_7916654 : CollatzResearch.WordTrace tailWord_7916654 prefixEnd_7916654 4065048677339174288516977 := by
  unfold tailWord_7916654
  simp only [CollatzResearch.WordTrace]
  refine ⟨36093011582665261213195627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192496061774214726470376677 36093011582665261213195627)
  ·
    refine ⟨54139517373997891819793441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36093011582665261213195627 54139517373997891819793441)
    ·
      refine ⟨40604638030498418864845081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54139517373997891819793441 40604638030498418864845081)
      ·
        refine ⟨30453478522873814148633811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40604638030498418864845081 30453478522873814148633811)
        ·
          refine ⟨45680217784310721222950717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453478522873814148633811 45680217784310721222950717)
          ·
            refine ⟨17130081669116520458606519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45680217784310721222950717 17130081669116520458606519)
            ·
              refine ⟨25695122503674780687909779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17130081669116520458606519 25695122503674780687909779)
              ·
                refine ⟨38542683755512171031864669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25695122503674780687909779 38542683755512171031864669)
                ·
                  refine ⟨14453506408317064136949251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38542683755512171031864669 14453506408317064136949251)
                  ·
                    refine ⟨21680259612475596205423877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14453506408317064136949251 21680259612475596205423877)
                    ·
                      refine ⟨4065048677339174288516977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21680259612475596205423877 4065048677339174288516977)
                      ·
                        rfl

theorem cell23_7916654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7916654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916654 prefixEnd_7916654 := by exact prefixLift 7916654
  have htrace : WordTrace (prefixWord ++ tailWord_7916654) baseStart_7916654 baseEnd_7916654 := by
    simpa [prefixWord, tailWord_7916654, baseEnd_7916654] using wordTrace_append hprefix tailTrace_7916654
  have hstable : (prefixWord ++ tailWord_7916654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916654).length < 2 ^ (prefixWord ++ tailWord_7916654).sum := by decide
  have hdescent : baseEnd_7916654 < baseStart_7916654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916677 : List Nat := [1, 3, 1, 1, 7, 10]
def baseStart_7916677 : Nat := 118140960795 + 7916677 * 2 ^ 59
def prefixEnd_7916677 : Nat := 4983230072969 + 3 ^ 40 * 7916677 * 2
def baseEnd_7916677 : Nat := 16728643981046204520697

theorem tailTrace_7916677 : CollatzResearch.WordTrace tailWord_7916677 prefixEnd_7916677 16728643981046204520697 := by
  unfold tailWord_7916677
  simp only [CollatzResearch.WordTrace]
  refine ⟨288744931540238764633652285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192496621026825843089101523 288744931540238764633652285)
  ·
    refine ⟨108279349327589536737619607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288744931540238764633652285 108279349327589536737619607)
    ·
      refine ⟨162419023991384305106429411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108279349327589536737619607 162419023991384305106429411)
      ·
        refine ⟨243628535987076457659644117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162419023991384305106429411 243628535987076457659644117)
        ·
          refine ⟨5710043812197104476397909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243628535987076457659644117 5710043812197104476397909)
          ·
            refine ⟨16728643981046204520697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5710043812197104476397909 16728643981046204520697)
            ·
              rfl

theorem cell23_7916677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 10].length) (baseStart_7916677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916677 prefixEnd_7916677 := by exact prefixLift 7916677
  have htrace : WordTrace (prefixWord ++ tailWord_7916677) baseStart_7916677 baseEnd_7916677 := by
    simpa [prefixWord, tailWord_7916677, baseEnd_7916677] using wordTrace_append hprefix tailTrace_7916677
  have hstable : (prefixWord ++ tailWord_7916677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916677).length < 2 ^ (prefixWord ++ tailWord_7916677).sum := by decide
  have hdescent : baseEnd_7916677 < baseStart_7916677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916704 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_7916704 : Nat := 118140960795 + 7916704 * 2 ^ 59
def prefixEnd_7916704 : Nat := 4983230072969 + 3 ^ 40 * 7916704 * 2
def baseEnd_7916704 : Nat := 4065074351371899092891747

theorem tailTrace_7916704 : CollatzResearch.WordTrace tailWord_7916704 prefixEnd_7916704 4065074351371899092891747 := by
  unfold tailWord_7916704
  simp only [CollatzResearch.WordTrace]
  refine ⟨144372958155570474122442583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192497277540760632163256777 144372958155570474122442583)
  ·
    refine ⟨216559437233355711183663875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144372958155570474122442583 216559437233355711183663875)
    ·
      refine ⟨324839155850033566775495813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216559437233355711183663875 324839155850033566775495813)
      ·
        refine ⟨60907341721881293770405465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324839155850033566775495813 60907341721881293770405465)
        ·
          refine ⟨45680506291410970327804099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60907341721881293770405465 45680506291410970327804099)
          ·
            refine ⟨68520759437116455491706149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45680506291410970327804099 68520759437116455491706149)
            ·
              refine ⟨12847642394459335404694903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68520759437116455491706149 12847642394459335404694903)
              ·
                refine ⟨19271463591689003107042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12847642394459335404694903 19271463591689003107042355)
                ·
                  refine ⟨28907195387533504660563533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19271463591689003107042355 28907195387533504660563533)
                  ·
                    refine ⟨10840198270325064247711325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28907195387533504660563533 10840198270325064247711325)
                    ·
                      refine ⟨4065074351371899092891747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840198270325064247711325 4065074351371899092891747)
                      ·
                        rfl

theorem cell23_7916704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_7916704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916704 prefixEnd_7916704 := by exact prefixLift 7916704
  have htrace : WordTrace (prefixWord ++ tailWord_7916704) baseStart_7916704 baseEnd_7916704 := by
    simpa [prefixWord, tailWord_7916704, baseEnd_7916704] using wordTrace_append hprefix tailTrace_7916704
  have hstable : (prefixWord ++ tailWord_7916704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916704).length < 2 ^ (prefixWord ++ tailWord_7916704).sum := by decide
  have hdescent : baseEnd_7916704 < baseStart_7916704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916744 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_7916744 : Nat := 118140960795 + 7916744 * 2 ^ 59
def prefixEnd_7916744 : Nat := 4983230072969 + 3 ^ 40 * 7916744 * 2
def baseEnd_7916744 : Nat := 4065094890598078936391563

theorem tailTrace_7916744 : CollatzResearch.WordTrace tailWord_7916744 prefixEnd_7916744 4065094890598078936391563 := by
  unfold tailWord_7916744
  simp only [CollatzResearch.WordTrace]
  refine ⟨144373687615498017538170643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192498250153997356717560857 144373687615498017538170643)
  ·
    refine ⟨216560531423247026307255965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144373687615498017538170643 216560531423247026307255965)
    ·
      refine ⟨81210199283717634865220987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216560531423247026307255965 81210199283717634865220987)
      ·
        refine ⟨121815298925576452297831481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81210199283717634865220987 121815298925576452297831481)
        ·
          refine ⟨91361474194182339223373611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121815298925576452297831481 91361474194182339223373611)
          ·
            refine ⟨137042211291273508835060417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91361474194182339223373611 137042211291273508835060417)
            ·
              refine ⟨102781658468455131626295313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137042211291273508835060417 102781658468455131626295313)
              ·
                refine ⟨77086243851341348719721485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102781658468455131626295313 77086243851341348719721485)
                ·
                  refine ⟨28907341444253005769895557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77086243851341348719721485 28907341444253005769895557)
                  ·
                    refine ⟨5420126520797438581855417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28907341444253005769895557 5420126520797438581855417)
                    ·
                      refine ⟨4065094890598078936391563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420126520797438581855417 4065094890598078936391563)
                      ·
                        rfl

theorem cell23_7916744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_7916744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916744 prefixEnd_7916744 := by exact prefixLift 7916744
  have htrace : WordTrace (prefixWord ++ tailWord_7916744) baseStart_7916744 baseEnd_7916744 := by
    simpa [prefixWord, tailWord_7916744, baseEnd_7916744] using wordTrace_append hprefix tailTrace_7916744
  have hstable : (prefixWord ++ tailWord_7916744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916744).length < 2 ^ (prefixWord ++ tailWord_7916744).sum := by decide
  have hdescent : baseEnd_7916744 < baseStart_7916744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916747 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3]
def baseStart_7916747 : Nat := 118140960795 + 7916747 * 2 ^ 59
def prefixEnd_7916747 : Nat := 4983230072969 + 3 ^ 40 * 7916747 * 2
def baseEnd_7916747 : Nat := 4065096431040042424654049

theorem tailTrace_7916747 : CollatzResearch.WordTrace tailWord_7916747 prefixEnd_7916747 4065096431040042424654049 := by
  unfold tailWord_7916747
  simp only [CollatzResearch.WordTrace]
  refine ⟨288747484649985166588700495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192498323099990111059133663 288747484649985166588700495)
  ·
    refine ⟨433121226974977749883050743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288747484649985166588700495 433121226974977749883050743)
    ·
      refine ⟨649681840462466624824576115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433121226974977749883050743 649681840462466624824576115)
      ·
        refine ⟨974522760693699937236864173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649681840462466624824576115 974522760693699937236864173)
        ·
          refine ⟨365446035260137476463824065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974522760693699937236864173 365446035260137476463824065)
          ·
            refine ⟨274084526445103107347868049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365446035260137476463824065 274084526445103107347868049)
            ·
              refine ⟨205563394833827330510901037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274084526445103107347868049 205563394833827330510901037)
              ·
                refine ⟨77086273062685248941587889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205563394833827330510901037 77086273062685248941587889)
                ·
                  refine ⟨57814704797013936706190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77086273062685248941587889 57814704797013936706190917)
                  ·
                    refine ⟨10840257149440113132410797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57814704797013936706190917 10840257149440113132410797)
                    ·
                      refine ⟨4065096431040042424654049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840257149440113132410797 4065096431040042424654049)
                      ·
                        rfl

theorem cell23_7916747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].length) (baseStart_7916747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916747 prefixEnd_7916747 := by exact prefixLift 7916747
  have htrace : WordTrace (prefixWord ++ tailWord_7916747) baseStart_7916747 baseEnd_7916747 := by
    simpa [prefixWord, tailWord_7916747, baseEnd_7916747] using wordTrace_append hprefix tailTrace_7916747
  have hstable : (prefixWord ++ tailWord_7916747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916747).length < 2 ^ (prefixWord ++ tailWord_7916747).sum := by decide
  have hdescent : baseEnd_7916747 < baseStart_7916747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916765 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7916765 : Nat := 118140960795 + 7916765 * 2 ^ 59
def prefixEnd_7916765 : Nat := 4983230072969 + 3 ^ 40 * 7916765 * 2
def baseEnd_7916765 : Nat := 4065105673691823354228967

theorem tailTrace_7916765 : CollatzResearch.WordTrace tailWord_7916765 prefixEnd_7916765 4065105673691823354228967 := by
  unfold tailWord_7916765
  simp only [CollatzResearch.WordTrace]
  refine ⟨288748141163919955662855749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192498760775946637108570499 288748141163919955662855749)
  ·
    refine ⟨54140276468234991686785453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288748141163919955662855749 54140276468234991686785453)
    ·
      refine ⟨20302603675588121882544545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54140276468234991686785453 20302603675588121882544545)
      ·
        refine ⟨15226952756691091411908409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20302603675588121882544545 15226952756691091411908409)
        ·
          refine ⟨11420214567518318558931307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15226952756691091411908409 11420214567518318558931307)
          ·
            refine ⟨17130321851277477838396961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420214567518318558931307 17130321851277477838396961)
            ·
              refine ⟨12847741388458108378797721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130321851277477838396961 12847741388458108378797721)
              ·
                refine ⟨9635806041343581284098291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12847741388458108378797721 9635806041343581284098291)
                ·
                  refine ⟨14453709062015371926147437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635806041343581284098291 14453709062015371926147437)
                  ·
                    refine ⟨5420140898255764472305289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14453709062015371926147437 5420140898255764472305289)
                    ·
                      refine ⟨4065105673691823354228967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420140898255764472305289 4065105673691823354228967)
                      ·
                        rfl

theorem cell23_7916765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7916765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916765 prefixEnd_7916765 := by exact prefixLift 7916765
  have htrace : WordTrace (prefixWord ++ tailWord_7916765) baseStart_7916765 baseEnd_7916765 := by
    simpa [prefixWord, tailWord_7916765, baseEnd_7916765] using wordTrace_append hprefix tailTrace_7916765
  have hstable : (prefixWord ++ tailWord_7916765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916765).length < 2 ^ (prefixWord ++ tailWord_7916765).sum := by decide
  have hdescent : baseEnd_7916765 < baseStart_7916765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916767 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 7]
def baseStart_7916767 : Nat := 118140960795 + 7916767 * 2 ^ 59
def prefixEnd_7916767 : Nat := 4983230072969 + 3 ^ 40 * 7916767 * 2
def baseEnd_7916767 : Nat := 451678522294792482933773

theorem tailTrace_7916767 : CollatzResearch.WordTrace tailWord_7916767 prefixEnd_7916767 451678522294792482933773 := by
  unfold tailWord_7916767
  simp only [CollatzResearch.WordTrace]
  refine ⟨288748214109912710004428555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192498809406608473336285703 288748214109912710004428555)
  ·
    refine ⟨433122321164869065006642833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288748214109912710004428555 433122321164869065006642833)
    ·
      refine ⟨324841740873651798754982125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433122321164869065006642833 324841740873651798754982125)
      ·
        refine ⟨121815652827619424533118297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324841740873651798754982125 121815652827619424533118297)
        ·
          refine ⟨91361739620714568399838723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121815652827619424533118297 91361739620714568399838723)
          ·
            refine ⟨137042609431071852599758085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91361739620714568399838723 137042609431071852599758085)
            ·
              refine ⟨25695489268325972362454641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137042609431071852599758085 25695489268325972362454641)
              ·
                refine ⟨19271616951244479271840981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25695489268325972362454641 19271616951244479271840981)
                ·
                  refine ⟨451678522294792482933773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19271616951244479271840981 451678522294792482933773)
                  ·
                    rfl

theorem cell23_7916767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 7].length) (baseStart_7916767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916767 prefixEnd_7916767 := by exact prefixLift 7916767
  have htrace : WordTrace (prefixWord ++ tailWord_7916767) baseStart_7916767 baseEnd_7916767 := by
    simpa [prefixWord, tailWord_7916767, baseEnd_7916767] using wordTrace_append hprefix tailTrace_7916767
  have hstable : (prefixWord ++ tailWord_7916767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916767).length < 2 ^ (prefixWord ++ tailWord_7916767).sum := by decide
  have hdescent : baseEnd_7916767 < baseStart_7916767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916831 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 2, 5]
def baseStart_7916831 : Nat := 118140960795 + 7916831 * 2 ^ 59
def prefixEnd_7916831 : Nat := 4983230072969 + 3 ^ 40 * 7916831 * 2
def baseEnd_7916831 : Nat := 1355046521138340032001221

theorem tailTrace_7916831 : CollatzResearch.WordTrace tailWord_7916831 prefixEnd_7916831 1355046521138340032001221 := by
  unfold tailWord_7916831
  simp only [CollatzResearch.WordTrace]
  refine ⟨288750548381680848934758347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192500365587787232623172231 288750548381680848934758347)
  ·
    refine ⟨433125822572521273402137521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288750548381680848934758347 433125822572521273402137521)
    ·
      refine ⟨324844366929390955051603141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433125822572521273402137521 324844366929390955051603141)
      ·
        refine ⟨60908318799260804072175589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324844366929390955051603141 60908318799260804072175589)
        ·
          refine ⟨11420309774861400763532923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60908318799260804072175589 11420309774861400763532923)
          ·
            refine ⟨17130464662292101145299385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420309774861400763532923 17130464662292101145299385)
            ·
              refine ⟨12847848496719075858974539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130464662292101145299385 12847848496719075858974539)
              ·
                refine ⟨19271772745078613788461809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12847848496719075858974539 19271772745078613788461809)
                ·
                  refine ⟨14453829558808960341346357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19271772745078613788461809 14453829558808960341346357)
                  ·
                    refine ⟨1355046521138340032001221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14453829558808960341346357 1355046521138340032001221)
                    ·
                      rfl

theorem cell23_7916831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_7916831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916831 prefixEnd_7916831 := by exact prefixLift 7916831
  have htrace : WordTrace (prefixWord ++ tailWord_7916831) baseStart_7916831 baseEnd_7916831 := by
    simpa [prefixWord, tailWord_7916831, baseEnd_7916831] using wordTrace_append hprefix tailTrace_7916831
  have hstable : (prefixWord ++ tailWord_7916831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916831).length < 2 ^ (prefixWord ++ tailWord_7916831).sum := by decide
  have hdescent : baseEnd_7916831 < baseStart_7916831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916847 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_7916847 : Nat := 118140960795 + 7916847 * 2 ^ 59
def prefixEnd_7916847 : Nat := 4983230072969 + 3 ^ 40 * 7916847 * 2
def baseEnd_7916847 : Nat := 4065147779105492033403589

theorem tailTrace_7916847 : CollatzResearch.WordTrace tailWord_7916847 prefixEnd_7916847 4065147779105492033403589 := by
  unfold tailWord_7916847
  simp only [CollatzResearch.WordTrace]
  refine ⟨288751131949622883667340795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192500754633081922444893863 288751131949622883667340795)
  ·
    refine ⟨433126697924434325501011193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288751131949622883667340795 433126697924434325501011193)
    ·
      refine ⟨324845023443325744125758395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433126697924434325501011193 324845023443325744125758395)
      ·
        refine ⟨487267535164988616188637593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324845023443325744125758395 487267535164988616188637593)
        ·
          refine ⟨365450651373741462141478195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487267535164988616188637593 365450651373741462141478195)
          ·
            refine ⟨548175977060612193212217293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365450651373741462141478195 548175977060612193212217293)
            ·
              refine ⟨205565991397729572454581485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548175977060612193212217293 205565991397729572454581485)
              ·
                refine ⟨77087246774148589670468057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205565991397729572454581485 77087246774148589670468057)
                ·
                  refine ⟨57815435080611442252851043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77087246774148589670468057 57815435080611442252851043)
                  ·
                    refine ⟨86723152620917163379276565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57815435080611442252851043 86723152620917163379276565)
                    ·
                      refine ⟨4065147779105492033403589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86723152620917163379276565 4065147779105492033403589)
                      ·
                        rfl

theorem cell23_7916847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_7916847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916847 prefixEnd_7916847 := by exact prefixLift 7916847
  have htrace : WordTrace (prefixWord ++ tailWord_7916847) baseStart_7916847 baseEnd_7916847 := by
    simpa [prefixWord, tailWord_7916847, baseEnd_7916847] using wordTrace_append hprefix tailTrace_7916847
  have hstable : (prefixWord ++ tailWord_7916847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916847).length < 2 ^ (prefixWord ++ tailWord_7916847).sum := by decide
  have hdescent : baseEnd_7916847 < baseStart_7916847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916868 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7916868 : Nat := 118140960795 + 7916868 * 2 ^ 59
def prefixEnd_7916868 : Nat := 4983230072969 + 3 ^ 40 * 7916868 * 2
def baseEnd_7916868 : Nat := 4065158562199236451240993

theorem tailTrace_7916868 : CollatzResearch.WordTrace tailWord_7916868 prefixEnd_7916868 4065158562199236451240993 := by
  unfold tailWord_7916868
  simp only [CollatzResearch.WordTrace]
  refine ⟨144375948941273402126927629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192501265255031202835903505 144375948941273402126927629)
  ·
    refine ⟨54140980852977525797597861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144375948941273402126927629 54140980852977525797597861)
    ·
      refine ⟨10151433909933286087049599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54140980852977525797597861 10151433909933286087049599)
      ·
        refine ⟨15227150864899929130574399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151433909933286087049599 15227150864899929130574399)
        ·
          refine ⟨22840726297349893695861599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227150864899929130574399 22840726297349893695861599)
          ·
            refine ⟨34261089446024840543792399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22840726297349893695861599 34261089446024840543792399)
            ·
              refine ⟨51391634169037260815688599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34261089446024840543792399 51391634169037260815688599)
              ·
                refine ⟨77087451253555891223532899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51391634169037260815688599 77087451253555891223532899)
                ·
                  refine ⟨115631176880333836835299349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77087451253555891223532899 115631176880333836835299349)
                  ·
                    refine ⟨5420211416265648601654657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115631176880333836835299349 5420211416265648601654657)
                    ·
                      refine ⟨4065158562199236451240993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420211416265648601654657 4065158562199236451240993)
                      ·
                        rfl

theorem cell23_7916868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7916868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916868 prefixEnd_7916868 := by exact prefixLift 7916868
  have htrace : WordTrace (prefixWord ++ tailWord_7916868) baseStart_7916868 baseEnd_7916868 := by
    simpa [prefixWord, tailWord_7916868, baseEnd_7916868] using wordTrace_append hprefix tailTrace_7916868
  have hstable : (prefixWord ++ tailWord_7916868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916868).length < 2 ^ (prefixWord ++ tailWord_7916868).sum := by decide
  have hdescent : baseEnd_7916868 < baseStart_7916868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916901 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_7916901 : Nat := 118140960795 + 7916901 * 2 ^ 59
def prefixEnd_7916901 : Nat := 4983230072969 + 3 ^ 40 * 7916901 * 2
def baseEnd_7916901 : Nat := 4065175507060834822128341

theorem tailTrace_7916901 : CollatzResearch.WordTrace tailWord_7916901 prefixEnd_7916901 4065175507060834822128341 := by
  unfold tailWord_7916901
  simp only [CollatzResearch.WordTrace]
  refine ⟨288753101491427250889806557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192502067660951500593204371 288753101491427250889806557)
  ·
    refine ⟨108282413059285219083677459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288753101491427250889806557 108282413059285219083677459)
    ·
      refine ⟨162423619588927828625516189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108282413059285219083677459 162423619588927828625516189)
      ·
        refine ⟨60908857345847935734568571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162423619588927828625516189 60908857345847935734568571)
        ·
          refine ⟨91363286018771903601852857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60908857345847935734568571 91363286018771903601852857)
          ·
            refine ⟨68522464514078927701389643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91363286018771903601852857 68522464514078927701389643)
            ·
              refine ⟨102783696771118391552084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68522464514078927701389643 102783696771118391552084465)
              ·
                refine ⟨77087772578338793664063349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102783696771118391552084465 77087772578338793664063349)
                ·
                  refine ⟨7226978679219261906005939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77087772578338793664063349 7226978679219261906005939)
                  ·
                    refine ⟨10840468018828892859008909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7226978679219261906005939 10840468018828892859008909)
                    ·
                      refine ⟨4065175507060834822128341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840468018828892859008909 4065175507060834822128341)
                      ·
                        rfl

theorem cell23_7916901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_7916901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916901 prefixEnd_7916901 := by exact prefixLift 7916901
  have htrace : WordTrace (prefixWord ++ tailWord_7916901) baseStart_7916901 baseEnd_7916901 := by
    simpa [prefixWord, tailWord_7916901, baseEnd_7916901] using wordTrace_append hprefix tailTrace_7916901
  have hstable : (prefixWord ++ tailWord_7916901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916901).length < 2 ^ (prefixWord ++ tailWord_7916901).sum := by decide
  have hdescent : baseEnd_7916901 < baseStart_7916901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916911 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 4, 3, 2]
def baseStart_7916911 : Nat := 118140960795 + 7916911 * 2 ^ 59
def prefixEnd_7916911 : Nat := 4983230072969 + 3 ^ 40 * 7916911 * 2
def baseEnd_7916911 : Nat := 4065180641867379783003295

theorem tailTrace_7916911 : CollatzResearch.WordTrace tailWord_7916911 prefixEnd_7916911 4065180641867379783003295 := by
  unfold tailWord_7916911
  simp only [CollatzResearch.WordTrace]
  refine ⟨288753466221391022597670587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192502310814260681731780391 288753466221391022597670587)
  ·
    refine ⟨433130199332086533896505881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288753466221391022597670587 433130199332086533896505881)
    ·
      refine ⟨324847649499064900422379411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433130199332086533896505881 324847649499064900422379411)
      ·
        refine ⟨487271474248597350633569117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324847649499064900422379411 487271474248597350633569117)
        ·
          refine ⟨182726802843224006487588419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487271474248597350633569117 182726802843224006487588419)
          ·
            refine ⟨274090204264836009731382629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182726802843224006487588419 274090204264836009731382629)
            ·
              refine ⟨51391913299656751824634243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274090204264836009731382629 51391913299656751824634243)
              ·
                refine ⟨77087869949485127736951365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51391913299656751824634243 77087869949485127736951365)
                ·
                  refine ⟨14453975615528461450678381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77087869949485127736951365 14453975615528461450678381)
                  ·
                    refine ⟨5420240855823173044004393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14453975615528461450678381 5420240855823173044004393)
                    ·
                      refine ⟨4065180641867379783003295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420240855823173044004393 4065180641867379783003295)
                      ·
                        rfl

theorem cell23_7916911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3, 2].length) (baseStart_7916911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916911 prefixEnd_7916911 := by exact prefixLift 7916911
  have htrace : WordTrace (prefixWord ++ tailWord_7916911) baseStart_7916911 baseEnd_7916911 := by
    simpa [prefixWord, tailWord_7916911, baseEnd_7916911] using wordTrace_append hprefix tailTrace_7916911
  have hstable : (prefixWord ++ tailWord_7916911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916911).length < 2 ^ (prefixWord ++ tailWord_7916911).sum := by decide
  have hdescent : baseEnd_7916911 < baseStart_7916911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916975 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 1, 2, 2]
def baseStart_7916975 : Nat := 118140960795 + 7916975 * 2 ^ 59
def prefixEnd_7916975 : Nat := 4983230072969 + 3 ^ 40 * 7916975 * 2
def baseEnd_7916975 : Nat := 4065213504629267532603001

theorem tailTrace_7916975 : CollatzResearch.WordTrace tailWord_7916975 prefixEnd_7916975 4065213504629267532603001 := by
  unfold tailWord_7916975
  simp only [CollatzResearch.WordTrace]
  refine ⟨288755800493159161528000379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192503866995439441018666919 288755800493159161528000379)
  ·
    refine ⟨433133700739738742292000569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288755800493159161528000379 433133700739738742292000569)
    ·
      refine ⟨324850275554804056719000427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433133700739738742292000569 324850275554804056719000427)
      ·
        refine ⟨487275413332206085078500641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324850275554804056719000427 487275413332206085078500641)
        ·
          refine ⟨365456559999154563808875481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487275413332206085078500641 365456559999154563808875481)
          ·
            refine ⟨274092419999365922856656611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365456559999154563808875481 274092419999365922856656611)
            ·
              refine ⟨411138629999048884284984917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274092419999365922856656611 411138629999048884284984917)
              ·
                refine ⟨4818030820301354112714667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 411138629999048884284984917 4818030820301354112714667)
                ·
                  refine ⟨7227046230452031169072001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818030820301354112714667 7227046230452031169072001)
                  ·
                    refine ⟨5420284672839023376804001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7227046230452031169072001 5420284672839023376804001)
                    ·
                      refine ⟨4065213504629267532603001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420284672839023376804001 4065213504629267532603001)
                      ·
                        rfl

theorem cell23_7916975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 2, 2].length) (baseStart_7916975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916975 prefixEnd_7916975 := by exact prefixLift 7916975
  have htrace : WordTrace (prefixWord ++ tailWord_7916975) baseStart_7916975 baseEnd_7916975 := by
    simpa [prefixWord, tailWord_7916975, baseEnd_7916975] using wordTrace_append hprefix tailTrace_7916975
  have hstable : (prefixWord ++ tailWord_7916975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916975).length < 2 ^ (prefixWord ++ tailWord_7916975).sum := by decide
  have hdescent : baseEnd_7916975 < baseStart_7916975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916981 : List Nat := [1, 3, 3, 2, 2, 2, 2, 8]
def baseStart_7916981 : Nat := 118140960795 + 7916981 * 2 ^ 59
def prefixEnd_7916981 : Nat := 4983230072969 + 3 ^ 40 * 7916981 * 2
def baseEnd_7916981 : Nat := 150563577241229426263999

theorem tailTrace_7916981 : CollatzResearch.WordTrace tailWord_7916981 prefixEnd_7916981 150563577241229426263999 := by
  unfold tailWord_7916981
  simp only [CollatzResearch.WordTrace]
  refine ⟨288756019331137424552718797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192504012887424949701812531 288756019331137424552718797)
  ·
    refine ⟨108283507249176534207269549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288756019331137424552718797 108283507249176534207269549)
    ·
      refine ⟨40606315218441200327726081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108283507249176534207269549 40606315218441200327726081)
      ·
        refine ⟨30454736413830900245794561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40606315218441200327726081 30454736413830900245794561)
        ·
          refine ⟨22841052310373175184345921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30454736413830900245794561 22841052310373175184345921)
          ·
            refine ⟨17130789232779881388259441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22841052310373175184345921 17130789232779881388259441)
            ·
              refine ⟨12848091924584911041194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130789232779881388259441 12848091924584911041194581)
              ·
                refine ⟨150563577241229426263999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12848091924584911041194581 150563577241229426263999)
                ·
                  rfl

theorem cell23_7916981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 8].length) (baseStart_7916981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7916981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7916981 prefixEnd_7916981 := by exact prefixLift 7916981
  have htrace : WordTrace (prefixWord ++ tailWord_7916981) baseStart_7916981 baseEnd_7916981 := by
    simpa [prefixWord, tailWord_7916981, baseEnd_7916981] using wordTrace_append hprefix tailTrace_7916981
  have hstable : (prefixWord ++ tailWord_7916981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916981).length < 2 ^ (prefixWord ++ tailWord_7916981).sum := by decide
  have hdescent : baseEnd_7916981 < baseStart_7916981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917012 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7917012 : Nat := 118140960795 + 7917012 * 2 ^ 59
def prefixEnd_7917012 : Nat := 4983230072969 + 3 ^ 40 * 7917012 * 2
def baseEnd_7917012 : Nat := 4065232503413483887840331

theorem tailTrace_7917012 : CollatzResearch.WordTrace tailWord_7917012 prefixEnd_7917012 4065232503413483887840331 := by
  unfold tailWord_7917012
  simp only [CollatzResearch.WordTrace]
  refine ⟨144378574997012558423548645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192504766662683411231398193 144378574997012558423548645)
  ·
    refine ⟨27070982811939854704415371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144378574997012558423548645 27070982811939854704415371)
    ·
      refine ⟨40606474217909782056623057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27070982811939854704415371 40606474217909782056623057)
      ·
        refine ⟨30454855663432336542467293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40606474217909782056623057 30454855663432336542467293)
        ·
          refine ⟨11420570873787126203425235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30454855663432336542467293 11420570873787126203425235)
          ·
            refine ⟨17130856310680689305137853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420570873787126203425235 17130856310680689305137853)
            ·
              refine ⟨6424071116505258489426695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17130856310680689305137853 6424071116505258489426695)
              ·
                refine ⟨9636106674757887734140043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424071116505258489426695 9636106674757887734140043)
                ·
                  refine ⟨14454160012136831601210065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636106674757887734140043 14454160012136831601210065)
                  ·
                    refine ⟨10840620009102623700907549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14454160012136831601210065 10840620009102623700907549)
                    ·
                      refine ⟨4065232503413483887840331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840620009102623700907549 4065232503413483887840331)
                      ·
                        rfl

theorem cell23_7917012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7917012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917012 prefixEnd_7917012 := by exact prefixLift 7917012
  have htrace : WordTrace (prefixWord ++ tailWord_7917012) baseStart_7917012 baseEnd_7917012 := by
    simpa [prefixWord, tailWord_7917012, baseEnd_7917012] using wordTrace_append hprefix tailTrace_7917012
  have hstable : (prefixWord ++ tailWord_7917012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917012).length < 2 ^ (prefixWord ++ tailWord_7917012).sum := by decide
  have hdescent : baseEnd_7917012 < baseStart_7917012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917025 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_7917025 : Nat := 118140960795 + 7917025 * 2 ^ 59
def prefixEnd_7917025 : Nat := 4983230072969 + 3 ^ 40 * 7917025 * 2
def baseEnd_7917025 : Nat := 4065239178661992336977771

theorem tailTrace_7917025 : CollatzResearch.WordTrace tailWord_7917025 prefixEnd_7917025 4065239178661992336977771 := by
  unfold tailWord_7917025
  simp only [CollatzResearch.WordTrace]
  refine ⟨288757624142978020067320529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192505082761985346711547019 288757624142978020067320529)
  ·
    refine ⟨216568218107233515050490397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288757624142978020067320529 216568218107233515050490397)
    ·
      refine ⟨81213081790212568143933899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216568218107233515050490397 81213081790212568143933899)
      ·
        refine ⟨121819622685318852215900849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81213081790212568143933899 121819622685318852215900849)
        ·
          refine ⟨91364717013989139161925637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121819622685318852215900849 91364717013989139161925637)
          ·
            refine ⟨17130884440122963592861057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91364717013989139161925637 17130884440122963592861057)
            ·
              refine ⟨12848163330092222694645793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130884440122963592861057 12848163330092222694645793)
              ·
                refine ⟨9636122497569167020984345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12848163330092222694645793 9636122497569167020984345)
                ·
                  refine ⟨7227091873176875265738259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9636122497569167020984345 7227091873176875265738259)
                  ·
                    refine ⟨10840637809765312898607389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227091873176875265738259 10840637809765312898607389)
                    ·
                      refine ⟨4065239178661992336977771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840637809765312898607389 4065239178661992336977771)
                      ·
                        rfl

theorem cell23_7917025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_7917025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917025 prefixEnd_7917025 := by exact prefixLift 7917025
  have htrace : WordTrace (prefixWord ++ tailWord_7917025) baseStart_7917025 baseEnd_7917025 := by
    simpa [prefixWord, tailWord_7917025, baseEnd_7917025] using wordTrace_append hprefix tailTrace_7917025
  have hstable : (prefixWord ++ tailWord_7917025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917025).length < 2 ^ (prefixWord ++ tailWord_7917025).sum := by decide
  have hdescent : baseEnd_7917025 < baseStart_7917025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917031 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7917031 : Nat := 118140960795 + 7917031 * 2 ^ 59
def prefixEnd_7917031 : Nat := 4983230072969 + 3 ^ 40 * 7917031 * 2
def baseEnd_7917031 : Nat := 4065242259545919313502743

theorem tailTrace_7917031 : CollatzResearch.WordTrace tailWord_7917031 prefixEnd_7917031 4065242259545919313502743 := by
  unfold tailWord_7917031
  simp only [CollatzResearch.WordTrace]
  refine ⟨288757842980956283092038947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192505228653970855394692631 288757842980956283092038947)
  ·
    refine ⟨433136764471434424638058421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288757842980956283092038947 433136764471434424638058421)
    ·
      refine ⟨40606571669196977309817977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433136764471434424638058421 40606571669196977309817977)
      ·
        refine ⟨30454928751897732982363483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40606571669196977309817977 30454928751897732982363483)
        ·
          refine ⟨45682393127846599473545225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30454928751897732982363483 45682393127846599473545225)
          ·
            refine ⟨34261794845884949605158919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45682393127846599473545225 34261794845884949605158919)
            ·
              refine ⟨51392692268827424407738379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34261794845884949605158919 51392692268827424407738379)
              ·
                refine ⟨77089038403241136611607569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51392692268827424407738379 77089038403241136611607569)
                ·
                  refine ⟨57816778802430852458705677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77089038403241136611607569 57816778802430852458705677)
                  ·
                    refine ⟨21681292050911569672014629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57816778802430852458705677 21681292050911569672014629)
                    ·
                      refine ⟨4065242259545919313502743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21681292050911569672014629 4065242259545919313502743)
                      ·
                        rfl

theorem cell23_7917031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7917031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917031 prefixEnd_7917031 := by exact prefixLift 7917031
  have htrace : WordTrace (prefixWord ++ tailWord_7917031) baseStart_7917031 baseEnd_7917031 := by
    simpa [prefixWord, tailWord_7917031, baseEnd_7917031] using wordTrace_append hprefix tailTrace_7917031
  have hstable : (prefixWord ++ tailWord_7917031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917031).length < 2 ^ (prefixWord ++ tailWord_7917031).sum := by decide
  have hdescent : baseEnd_7917031 < baseStart_7917031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917041 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_7917041 : Nat := 118140960795 + 7917041 * 2 ^ 59
def prefixEnd_7917041 : Nat := 4983230072969 + 3 ^ 40 * 7917041 * 2
def baseEnd_7917041 : Nat := 1355082464784154758125899

theorem tailTrace_7917041 : CollatzResearch.WordTrace tailWord_7917041 prefixEnd_7917041 1355082464784154758125899 := by
  unfold tailWord_7917041
  simp only [CollatzResearch.WordTrace]
  refine ⟨288758207710920054799902977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192505471807280036533268651 288758207710920054799902977)
  ·
    refine ⟨216568655783190041099927233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288758207710920054799902977 216568655783190041099927233)
    ·
      refine ⟨162426491837392530824945425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216568655783190041099927233 162426491837392530824945425)
      ·
        refine ⟨121819868878044398118709069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162426491837392530824945425 121819868878044398118709069)
        ·
          refine ⟨45682450829266649294515901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121819868878044398118709069 45682450829266649294515901)
          ·
            refine ⟨17130919060974993485443463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45682450829266649294515901 17130919060974993485443463)
            ·
              refine ⟨25696378591462490228165195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17130919060974993485443463 25696378591462490228165195)
              ·
                refine ⟨38544567887193735342247793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25696378591462490228165195 38544567887193735342247793)
                ·
                  refine ⟨28908425915395301506685845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38544567887193735342247793 28908425915395301506685845)
                  ·
                    refine ⟨1355082464784154758125899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28908425915395301506685845 1355082464784154758125899)
                    ·
                      rfl

theorem cell23_7917041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_7917041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917041 prefixEnd_7917041 := by exact prefixLift 7917041
  have htrace : WordTrace (prefixWord ++ tailWord_7917041) baseStart_7917041 baseEnd_7917041 := by
    simpa [prefixWord, tailWord_7917041, baseEnd_7917041] using wordTrace_append hprefix tailTrace_7917041
  have hstable : (prefixWord ++ tailWord_7917041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917041).length < 2 ^ (prefixWord ++ tailWord_7917041).sum := by decide
  have hdescent : baseEnd_7917041 < baseStart_7917041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917048 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_7917048 : Nat := 118140960795 + 7917048 * 2 ^ 59
def prefixEnd_7917048 : Nat := 4983230072969 + 3 ^ 40 * 7917048 * 2
def baseEnd_7917048 : Nat := 4065250988717045746990165

theorem tailTrace_7917048 : CollatzResearch.WordTrace tailWord_7917048 prefixEnd_7917048 4065250988717045746990165 := by
  unfold tailWord_7917048
  simp only [CollatzResearch.WordTrace]
  refine ⟨144379231510947347497703899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192505642014596463330271865 144379231510947347497703899)
  ·
    refine ⟨216568847266421021246555849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144379231510947347497703899 216568847266421021246555849)
    ·
      refine ⟨162426635449815765934916887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216568847266421021246555849 162426635449815765934916887)
      ·
        refine ⟨243639953174723648902375331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162426635449815765934916887 243639953174723648902375331)
        ·
          refine ⟨365459929762085473353562997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243639953174723648902375331 365459929762085473353562997)
          ·
            refine ⟨34261868415195513126896531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365459929762085473353562997 34261868415195513126896531)
            ·
              refine ⟨51392802622793269690344797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34261868415195513126896531 51392802622793269690344797)
              ·
                refine ⟨19272300983547476133879299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51392802622793269690344797 19272300983547476133879299)
                ·
                  refine ⟨28908451475321214200818949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19272300983547476133879299 28908451475321214200818949)
                  ·
                    refine ⟨5420334651622727662653553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28908451475321214200818949 5420334651622727662653553)
                    ·
                      refine ⟨4065250988717045746990165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420334651622727662653553 4065250988717045746990165)
                      ·
                        rfl

theorem cell23_7917048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_7917048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917048 prefixEnd_7917048 := by exact prefixLift 7917048
  have htrace : WordTrace (prefixWord ++ tailWord_7917048) baseStart_7917048 baseEnd_7917048 := by
    simpa [prefixWord, tailWord_7917048, baseEnd_7917048] using wordTrace_append hprefix tailTrace_7917048
  have hstable : (prefixWord ++ tailWord_7917048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917048).length < 2 ^ (prefixWord ++ tailWord_7917048).sum := by decide
  have hdescent : baseEnd_7917048 < baseStart_7917048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917076 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_7917076 : Nat := 118140960795 + 7917076 * 2 ^ 59
def prefixEnd_7917076 : Nat := 4983230072969 + 3 ^ 40 * 7917076 * 2
def baseEnd_7917076 : Nat := 4065265366175371637440037

theorem tailTrace_7917076 : CollatzResearch.WordTrace tailWord_7917076 prefixEnd_7917076 4065265366175371637440037 := by
  unfold tailWord_7917076
  simp only [CollatzResearch.WordTrace]
  refine ⟨144379742132896627888713541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192506322843862170518284721 144379742132896627888713541)
  ·
    refine ⟨27071201649918117729133789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144379742132896627888713541 27071201649918117729133789)
    ·
      refine ⟨10151700618719294148425171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27071201649918117729133789 10151700618719294148425171)
      ·
        refine ⟨15227550928078941222637757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151700618719294148425171 15227550928078941222637757)
        ·
          refine ⟨5710331598029602958489159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15227550928078941222637757 5710331598029602958489159)
          ·
            refine ⟨8565497397044404437733739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710331598029602958489159 8565497397044404437733739)
            ·
              refine ⟨12848246095566606656600609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565497397044404437733739 12848246095566606656600609)
              ·
                refine ⟨9636184571674954992450457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12848246095566606656600609 9636184571674954992450457)
                ·
                  refine ⟨7227138428756216244337843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9636184571674954992450457 7227138428756216244337843)
                  ·
                    refine ⟨10840707643134324366506765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227138428756216244337843 10840707643134324366506765)
                    ·
                      refine ⟨4065265366175371637440037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840707643134324366506765 4065265366175371637440037)
                      ·
                        rfl

theorem cell23_7917076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_7917076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917076 prefixEnd_7917076 := by exact prefixLift 7917076
  have htrace : WordTrace (prefixWord ++ tailWord_7917076) baseStart_7917076 baseEnd_7917076 := by
    simpa [prefixWord, tailWord_7917076, baseEnd_7917076] using wordTrace_append hprefix tailTrace_7917076
  have hstable : (prefixWord ++ tailWord_7917076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917076).length < 2 ^ (prefixWord ++ tailWord_7917076).sum := by decide
  have hdescent : baseEnd_7917076 < baseStart_7917076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917088 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 7]
def baseStart_7917088 : Nat := 118140960795 + 7917088 * 2 ^ 59
def prefixEnd_7917088 : Nat := 4983230072969 + 3 ^ 40 * 7917088 * 2
def baseEnd_7917088 : Nat := 451696836438136176721109

theorem tailTrace_7917088 : CollatzResearch.WordTrace tailWord_7917088 prefixEnd_7917088 451696836438136176721109 := by
  unfold tailWord_7917088
  simp only [CollatzResearch.WordTrace]
  refine ⟨144379960970874890913431959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192506614627833187884575945 144379960970874890913431959)
  ·
    refine ⟨216569941456312336370147939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144379960970874890913431959 216569941456312336370147939)
    ·
      refine ⟨324854912184468504555221909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216569941456312336370147939 324854912184468504555221909)
      ·
        refine ⟨15227574008646961151026027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324854912184468504555221909 15227574008646961151026027)
        ·
          refine ⟨22841361012970441726539041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227574008646961151026027 22841361012970441726539041)
          ·
            refine ⟨17131020759727831294904281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22841361012970441726539041 17131020759727831294904281)
            ·
              refine ⟨12848265569795873471178211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17131020759727831294904281 12848265569795873471178211)
              ·
                refine ⟨19272398354693810206767317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848265569795873471178211 19272398354693810206767317)
                ·
                  refine ⟨451696836438136176721109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19272398354693810206767317 451696836438136176721109)
                  ·
                    rfl

theorem cell23_7917088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_7917088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917088 prefixEnd_7917088 := by exact prefixLift 7917088
  have htrace : WordTrace (prefixWord ++ tailWord_7917088) baseStart_7917088 baseEnd_7917088 := by
    simpa [prefixWord, tailWord_7917088, baseEnd_7917088] using wordTrace_append hprefix tailTrace_7917088
  have hstable : (prefixWord ++ tailWord_7917088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917088).length < 2 ^ (prefixWord ++ tailWord_7917088).sum := by decide
  have hdescent : baseEnd_7917088 < baseStart_7917088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917098 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7917098 : Nat := 118140960795 + 7917098 * 2 ^ 59
def prefixEnd_7917098 : Nat := 4983230072969 + 3 ^ 40 * 7917098 * 2
def baseEnd_7917098 : Nat := 4065276662749770551364935

theorem tailTrace_7917098 : CollatzResearch.WordTrace tailWord_7917098 prefixEnd_7917098 4065276662749770551364935 := by
  unfold tailWord_7917098
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190071667928388383681987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192506857781142369023151965 72190071667928388383681987)
  ·
    refine ⟨108285107501892582575522981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72190071667928388383681987 108285107501892582575522981)
    ·
      refine ⟨20303457656604859232910559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108285107501892582575522981 20303457656604859232910559)
      ·
        refine ⟨30455186484907288849365839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20303457656604859232910559 30455186484907288849365839)
        ·
          refine ⟨45682779727360933274048759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30455186484907288849365839 45682779727360933274048759)
          ·
            refine ⟨68524169591041399911073139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45682779727360933274048759 68524169591041399911073139)
            ·
              refine ⟨102786254386562099866609709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68524169591041399911073139 102786254386562099866609709)
              ·
                refine ⟨38544845394960787449978641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102786254386562099866609709 38544845394960787449978641)
                ·
                  refine ⟨28908634046220590587483981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38544845394960787449978641 28908634046220590587483981)
                  ·
                    refine ⟨10840737767332721470306493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28908634046220590587483981 10840737767332721470306493)
                    ·
                      refine ⟨4065276662749770551364935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840737767332721470306493 4065276662749770551364935)
                      ·
                        rfl

theorem cell23_7917098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7917098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917098 prefixEnd_7917098 := by exact prefixLift 7917098
  have htrace : WordTrace (prefixWord ++ tailWord_7917098) baseStart_7917098 baseEnd_7917098 := by
    simpa [prefixWord, tailWord_7917098, baseEnd_7917098] using wordTrace_append hprefix tailTrace_7917098
  have hstable : (prefixWord ++ tailWord_7917098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917098).length < 2 ^ (prefixWord ++ tailWord_7917098).sum := by decide
  have hdescent : baseEnd_7917098 < baseStart_7917098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917138 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_7917138 : Nat := 118140960795 + 7917138 * 2 ^ 59
def prefixEnd_7917138 : Nat := 4983230072969 + 3 ^ 40 * 7917138 * 2
def baseEnd_7917138 : Nat := 4065297201975950394864751

theorem tailTrace_7917138 : CollatzResearch.WordTrace tailWord_7917138 prefixEnd_7917138 4065297201975950394864751 := by
  unfold tailWord_7917138
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190436397892160091546017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192507830394379093577456045 72190436397892160091546017)
  ·
    refine ⟨54142827298419120068659513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72190436397892160091546017 54142827298419120068659513)
    ·
      refine ⟨40607120473814340051494635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54142827298419120068659513 40607120473814340051494635)
      ·
        refine ⟨60910680710721510077241953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40607120473814340051494635 60910680710721510077241953)
        ·
          refine ⟨45683010533041132557931465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60910680710721510077241953 45683010533041132557931465)
          ·
            refine ⟨34262257899780849418448599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45683010533041132557931465 34262257899780849418448599)
            ·
              refine ⟨51393386849671274127672899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34262257899780849418448599 51393386849671274127672899)
              ·
                refine ⟨77090080274506911191509349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51393386849671274127672899 77090080274506911191509349)
                ·
                  refine ⟨14454390051470045848408003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77090080274506911191509349 14454390051470045848408003)
                  ·
                    refine ⟨21681585077205068772612005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14454390051470045848408003 21681585077205068772612005)
                    ·
                      refine ⟨4065297201975950394864751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21681585077205068772612005 4065297201975950394864751)
                      ·
                        rfl

theorem cell23_7917138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_7917138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917138 prefixEnd_7917138 := by exact prefixLift 7917138
  have htrace : WordTrace (prefixWord ++ tailWord_7917138) baseStart_7917138 baseEnd_7917138 := by
    simpa [prefixWord, tailWord_7917138, baseEnd_7917138] using wordTrace_append hprefix tailTrace_7917138
  have hstable : (prefixWord ++ tailWord_7917138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917138).length < 2 ^ (prefixWord ++ tailWord_7917138).sum := by decide
  have hdescent : baseEnd_7917138 < baseStart_7917138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917208 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_7917208 : Nat := 118140960795 + 7917208 * 2 ^ 59
def prefixEnd_7917208 : Nat := 4983230072969 + 3 ^ 40 * 7917208 * 2
def baseEnd_7917208 : Nat := 1355111048540588373663143

theorem tailTrace_7917208 : CollatzResearch.WordTrace tailWord_7917208 prefixEnd_7917208 1355111048540588373663143 := by
  unfold tailWord_7917208
  simp only [CollatzResearch.WordTrace]
  refine ⟨144382149350657521160616139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192509532467543361547488185 144382149350657521160616139)
  ·
    refine ⟨216573224025986281740924209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144382149350657521160616139 216573224025986281740924209)
    ·
      refine ⟨162429918019489711305693157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216573224025986281740924209 162429918019489711305693157)
      ·
        refine ⟨30455609628654320869817467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162429918019489711305693157 30455609628654320869817467)
        ·
          refine ⟨45683414442981481304726201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30455609628654320869817467 45683414442981481304726201)
          ·
            refine ⟨34262560832236110978544651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45683414442981481304726201 34262560832236110978544651)
            ·
              refine ⟨51393841248354166467816977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34262560832236110978544651 51393841248354166467816977)
              ·
                refine ⟨38545380936265624850862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51393841248354166467816977 38545380936265624850862733)
                ·
                  refine ⟨14454517851099609319073525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38545380936265624850862733 14454517851099609319073525)
                  ·
                    refine ⟨1355111048540588373663143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14454517851099609319073525 1355111048540588373663143)
                    ·
                      rfl

theorem cell23_7917208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_7917208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917208 prefixEnd_7917208 := by exact prefixLift 7917208
  have htrace : WordTrace (prefixWord ++ tailWord_7917208) baseStart_7917208 baseEnd_7917208 := by
    simpa [prefixWord, tailWord_7917208, baseEnd_7917208] using wordTrace_append hprefix tailTrace_7917208
  have hstable : (prefixWord ++ tailWord_7917208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917208).length < 2 ^ (prefixWord ++ tailWord_7917208).sum := by decide
  have hdescent : baseEnd_7917208 < baseStart_7917208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917239 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_7917239 : Nat := 118140960795 + 7917239 * 2 ^ 59
def prefixEnd_7917239 : Nat := 4983230072969 + 3 ^ 40 * 7917239 * 2
def baseEnd_7917239 : Nat := 4065349063522054499701787

theorem tailTrace_7917239 : CollatzResearch.WordTrace tailWord_7917239 prefixEnd_7917239 4065349063522054499701787 := by
  unfold tailWord_7917239
  simp only [CollatzResearch.WordTrace]
  refine ⟨288765429364202734615610771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192510286242801823077073847 288765429364202734615610771)
  ·
    refine ⟨433148144046304101923416157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288765429364202734615610771 433148144046304101923416157)
    ·
      refine ⟨162430554017364038221281059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433148144046304101923416157 162430554017364038221281059)
      ·
        refine ⟨243645831026046057331921589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162430554017364038221281059 243645831026046057331921589)
        ·
          refine ⟨22841796658691817874867649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243645831026046057331921589 22841796658691817874867649)
          ·
            refine ⟨17131347494018863406150737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22841796658691817874867649 17131347494018863406150737)
            ·
              refine ⟨12848510620514147554613053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17131347494018863406150737 12848510620514147554613053)
              ·
                refine ⟨4818191482692805332979895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12848510620514147554613053 4818191482692805332979895)
                ·
                  refine ⟨7227287224039207999469843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818191482692805332979895 7227287224039207999469843)
                  ·
                    refine ⟨10840930836058811999204765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227287224039207999469843 10840930836058811999204765)
                    ·
                      refine ⟨4065349063522054499701787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10840930836058811999204765 4065349063522054499701787)
                      ·
                        rfl

theorem cell23_7917239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_7917239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917239 prefixEnd_7917239 := by exact prefixLift 7917239
  have htrace : WordTrace (prefixWord ++ tailWord_7917239) baseStart_7917239 baseEnd_7917239 := by
    simpa [prefixWord, tailWord_7917239, baseEnd_7917239] using wordTrace_append hprefix tailTrace_7917239
  have hstable : (prefixWord ++ tailWord_7917239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917239).length < 2 ^ (prefixWord ++ tailWord_7917239).sum := by decide
  have hdescent : baseEnd_7917239 < baseStart_7917239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917242 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_7917242 : Nat := 118140960795 + 7917242 * 2 ^ 59
def prefixEnd_7917242 : Nat := 4983230072969 + 3 ^ 40 * 7917242 * 2
def baseEnd_7917242 : Nat := 1355116867988005995988091

theorem tailTrace_7917242 : CollatzResearch.WordTrace tailWord_7917242 prefixEnd_7917242 1355116867988005995988091 := by
  unfold tailWord_7917242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72191384695797966531992495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192510359188794577418646653 72191384695797966531992495)
  ·
    refine ⟨108287077043696949797988743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72191384695797966531992495 108287077043696949797988743)
    ·
      refine ⟨162430615565545424696983115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108287077043696949797988743 162430615565545424696983115)
      ·
        refine ⟨243645923348318137045474673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162430615565545424696983115 243645923348318137045474673)
        ·
          refine ⟨182734442511238602784106005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243645923348318137045474673 182734442511238602784106005)
          ·
            refine ⟨8565676992714309505504969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182734442511238602784106005 8565676992714309505504969)
            ·
              refine ⟨6424257744535732129128727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8565676992714309505504969 6424257744535732129128727)
              ·
                refine ⟨9636386616803598193693091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424257744535732129128727 9636386616803598193693091)
                ·
                  refine ⟨14454579925205397290539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636386616803598193693091 14454579925205397290539637)
                  ·
                    refine ⟨1355116867988005995988091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14454579925205397290539637 1355116867988005995988091)
                    ·
                      rfl

theorem cell23_7917242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_7917242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917242 prefixEnd_7917242 := by exact prefixLift 7917242
  have htrace : WordTrace (prefixWord ++ tailWord_7917242) baseStart_7917242 baseEnd_7917242 := by
    simpa [prefixWord, tailWord_7917242, baseEnd_7917242] using wordTrace_append hprefix tailTrace_7917242
  have hstable : (prefixWord ++ tailWord_7917242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917242).length < 2 ^ (prefixWord ++ tailWord_7917242).sum := by decide
  have hdescent : baseEnd_7917242 < baseStart_7917242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917245 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_7917245 : Nat := 118140960795 + 7917245 * 2 ^ 59
def prefixEnd_7917245 : Nat := 4983230072969 + 3 ^ 40 * 7917245 * 2
def baseEnd_7917245 : Nat := 4065352144405981476226759

theorem tailTrace_7917245 : CollatzResearch.WordTrace tailWord_7917245 prefixEnd_7917245 4065352144405981476226759 := by
  unfold tailWord_7917245
  simp only [CollatzResearch.WordTrace]
  refine ⟨288765648202180997640329189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192510432134787331760219459 288765648202180997640329189)
  ·
    refine ⟨54143559037908937057561723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288765648202180997640329189 54143559037908937057561723)
    ·
      refine ⟨81215338556863405586342585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54143559037908937057561723 81215338556863405586342585)
      ·
        refine ⟨60911503917647554189756939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81215338556863405586342585 60911503917647554189756939)
        ·
          refine ⟨91367255876471331284635409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60911503917647554189756939 91367255876471331284635409)
          ·
            refine ⟨68525441907353498463476557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91367255876471331284635409 68525441907353498463476557)
            ·
              refine ⟨25697040715257561923803709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68525441907353498463476557 25697040715257561923803709)
              ·
                refine ⟨9636390268221585721426391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25697040715257561923803709 9636390268221585721426391)
                ·
                  refine ⟨14454585402332378582139587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636390268221585721426391 14454585402332378582139587)
                  ·
                    refine ⟨21681878103498567873209381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14454585402332378582139587 21681878103498567873209381)
                    ·
                      refine ⟨4065352144405981476226759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21681878103498567873209381 4065352144405981476226759)
                      ·
                        rfl

theorem cell23_7917245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_7917245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917245 prefixEnd_7917245 := by exact prefixLift 7917245
  have htrace : WordTrace (prefixWord ++ tailWord_7917245) baseStart_7917245 baseEnd_7917245 := by
    simpa [prefixWord, tailWord_7917245, baseEnd_7917245] using wordTrace_append hprefix tailTrace_7917245
  have hstable : (prefixWord ++ tailWord_7917245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917245).length < 2 ^ (prefixWord ++ tailWord_7917245).sum := by decide
  have hdescent : baseEnd_7917245 < baseStart_7917245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917248 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_7917248 : Nat := 118140960795 + 7917248 * 2 ^ 59
def prefixEnd_7917248 : Nat := 4983230072969 + 3 ^ 40 * 7917248 * 2
def baseEnd_7917248 : Nat := 4065353684847944964489245

theorem tailTrace_7917248 : CollatzResearch.WordTrace tailWord_7917248 prefixEnd_7917248 4065353684847944964489245 := by
  unfold tailWord_7917248
  simp only [CollatzResearch.WordTrace]
  refine ⟨144382878810585064576344199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192510505080780086101792265 144382878810585064576344199)
  ·
    refine ⟨216574318215877596864516299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144382878810585064576344199 216574318215877596864516299)
    ·
      refine ⟨324861477323816395296774449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216574318215877596864516299 324861477323816395296774449)
      ·
        refine ⟨243646107992862296472580837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324861477323816395296774449 243646107992862296472580837)
        ·
          refine ⟨45683645248661680588608907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243646107992862296472580837 45683645248661680588608907)
          ·
            refine ⟨68525467872992520882913361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683645248661680588608907 68525467872992520882913361)
            ·
              refine ⟨51394100904744390662185021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68525467872992520882913361 51394100904744390662185021)
              ·
                refine ⟨19272787839279146498319383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51394100904744390662185021 19272787839279146498319383)
                ·
                  refine ⟨28909181758918719747479075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19272787839279146498319383 28909181758918719747479075)
                  ·
                    refine ⟨43363772638378079621218613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28909181758918719747479075 43363772638378079621218613)
                    ·
                      refine ⟨4065353684847944964489245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43363772638378079621218613 4065353684847944964489245)
                      ·
                        rfl

theorem cell23_7917248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_7917248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917248 prefixEnd_7917248 := by exact prefixLift 7917248
  have htrace : WordTrace (prefixWord ++ tailWord_7917248) baseStart_7917248 baseEnd_7917248 := by
    simpa [prefixWord, tailWord_7917248, baseEnd_7917248] using wordTrace_append hprefix tailTrace_7917248
  have hstable : (prefixWord ++ tailWord_7917248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917248).length < 2 ^ (prefixWord ++ tailWord_7917248).sum := by decide
  have hdescent : baseEnd_7917248 < baseStart_7917248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917272 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_7917272 : Nat := 118140960795 + 7917272 * 2 ^ 59
def prefixEnd_7917272 : Nat := 4983230072969 + 3 ^ 40 * 7917272 * 2
def baseEnd_7917272 : Nat := 1355122002794550956863045

theorem tailTrace_7917272 : CollatzResearch.WordTrace tailWord_7917272 prefixEnd_7917272 1355122002794550956863045 := by
  unfold tailWord_7917272
  simp only [CollatzResearch.WordTrace]
  refine ⟨144383316486541590625781035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192511088648722120834374713 144383316486541590625781035)
  ·
    refine ⟨216574974729812385938671553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144383316486541590625781035 216574974729812385938671553)
    ·
      refine ⟨162431231047359289454003665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216574974729812385938671553 162431231047359289454003665)
      ·
        refine ⟨121823423285519467090502749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162431231047359289454003665 121823423285519467090502749)
        ·
          refine ⟨45683783732069800158938531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121823423285519467090502749 45683783732069800158938531)
          ·
            refine ⟨68525675598104700238407797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683783732069800158938531 68525675598104700238407797)
            ·
              refine ⟨6424282087322315647350731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68525675598104700238407797 6424282087322315647350731)
              ·
                refine ⟨9636423130983473471026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424282087322315647350731 9636423130983473471026097)
                ·
                  refine ⟨7227317348237605103269573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9636423130983473471026097 7227317348237605103269573)
                  ·
                    refine ⟨1355122002794550956863045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7227317348237605103269573 1355122002794550956863045)
                    ·
                      rfl

theorem cell23_7917272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_7917272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917272 prefixEnd_7917272 := by exact prefixLift 7917272
  have htrace : WordTrace (prefixWord ++ tailWord_7917272) baseStart_7917272 baseEnd_7917272 := by
    simpa [prefixWord, tailWord_7917272, baseEnd_7917272] using wordTrace_append hprefix tailTrace_7917272
  have hstable : (prefixWord ++ tailWord_7917272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917272).length < 2 ^ (prefixWord ++ tailWord_7917272).sum := by decide
  have hdescent : baseEnd_7917272 < baseStart_7917272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917295 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_7917295 : Nat := 118140960795 + 7917295 * 2 ^ 59
def prefixEnd_7917295 : Nat := 4983230072969 + 3 ^ 40 * 7917295 * 2
def baseEnd_7917295 : Nat := 4065377818438706280601529

theorem tailTrace_7917295 : CollatzResearch.WordTrace tailWord_7917295 prefixEnd_7917295 4065377818438706280601529 := by
  unfold tailWord_7917295
  simp only [CollatzResearch.WordTrace]
  refine ⟨288767471851999856179649339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192511647901333237453099559 288767471851999856179649339)
  ·
    refine ⟨433151207777999784269474009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288767471851999856179649339 433151207777999784269474009)
    ·
      refine ⟨324863405833499838202105507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433151207777999784269474009 324863405833499838202105507)
      ·
        refine ⟨487295108750249757303158261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324863405833499838202105507 487295108750249757303158261)
        ·
          refine ⟨45683916445335914747171087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487295108750249757303158261 45683916445335914747171087)
          ·
            refine ⟨68525874668003872120756631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683916445335914747171087 68525874668003872120756631)
            ·
              refine ⟨102788812002005808181134947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68525874668003872120756631 102788812002005808181134947)
              ·
                refine ⟨154183218003008712271702421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102788812002005808181134947 154183218003008712271702421)
                ·
                  refine ⟨7227338343891033387736051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154183218003008712271702421 7227338343891033387736051)
                  ·
                    refine ⟨10841007515836550081604077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227338343891033387736051 10841007515836550081604077)
                    ·
                      refine ⟨4065377818438706280601529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841007515836550081604077 4065377818438706280601529)
                      ·
                        rfl

theorem cell23_7917295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_7917295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917295 prefixEnd_7917295 := by exact prefixLift 7917295
  have htrace : WordTrace (prefixWord ++ tailWord_7917295) baseStart_7917295 baseEnd_7917295 := by
    simpa [prefixWord, tailWord_7917295, baseEnd_7917295] using wordTrace_append hprefix tailTrace_7917295
  have hstable : (prefixWord ++ tailWord_7917295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917295).length < 2 ^ (prefixWord ++ tailWord_7917295).sum := by decide
  have hdescent : baseEnd_7917295 < baseStart_7917295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917305 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 7, 3, 2]
def baseStart_7917305 : Nat := 118140960795 + 7917305 * 2 ^ 59
def prefixEnd_7917305 : Nat := 4983230072969 + 3 ^ 40 * 7917305 * 2
def baseEnd_7917305 : Nat := 4065382953245251241476483

theorem tailTrace_7917305 : CollatzResearch.WordTrace tailWord_7917305 prefixEnd_7917305 4065382953245251241476483 := by
  unfold tailWord_7917305
  simp only [CollatzResearch.WordTrace]
  refine ⟨288767836581963627887513369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192511891054642418591675579 288767836581963627887513369)
  ·
    refine ⟨216575877436472720915635027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288767836581963627887513369 216575877436472720915635027)
    ·
      refine ⟨324863816154709081373452541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216575877436472720915635027 324863816154709081373452541)
      ·
        refine ⟨121823931058015905515044703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324863816154709081373452541 121823931058015905515044703)
        ·
          refine ⟨182735896587023858272567055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121823931058015905515044703 182735896587023858272567055)
          ·
            refine ⟨274103844880535787408850583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182735896587023858272567055 274103844880535787408850583)
            ·
              refine ⟨411155767320803681113275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274103844880535787408850583 411155767320803681113275875)
              ·
                refine ⟨616733650981205521669913813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411155767320803681113275875 616733650981205521669913813)
                ·
                  refine ⟨14454694944872004414138605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 616733650981205521669913813 14454694944872004414138605)
                  ·
                    refine ⟨5420510604327001655301977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14454694944872004414138605 5420510604327001655301977)
                    ·
                      refine ⟨4065382953245251241476483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420510604327001655301977 4065382953245251241476483)
                      ·
                        rfl

theorem cell23_7917305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_7917305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917305 prefixEnd_7917305 := by exact prefixLift 7917305
  have htrace : WordTrace (prefixWord ++ tailWord_7917305) baseStart_7917305 baseEnd_7917305 := by
    simpa [prefixWord, tailWord_7917305, baseEnd_7917305] using wordTrace_append hprefix tailTrace_7917305
  have hstable : (prefixWord ++ tailWord_7917305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917305).length < 2 ^ (prefixWord ++ tailWord_7917305).sum := by decide
  have hdescent : baseEnd_7917305 < baseStart_7917305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917308 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_7917308 : Nat := 118140960795 + 7917308 * 2 ^ 59
def prefixEnd_7917308 : Nat := 4983230072969 + 3 ^ 40 * 7917308 * 2
def baseEnd_7917308 : Nat := 4065384493687214729738969

theorem tailTrace_7917308 : CollatzResearch.WordTrace tailWord_7917308 prefixEnd_7917308 4065384493687214729738969 := by
  unfold tailWord_7917308
  simp only [CollatzResearch.WordTrace]
  refine ⟨144383973000476379699936289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192511964000635172933248385 144383973000476379699936289)
  ·
    refine ⟨108287979750357284774952217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144383973000476379699936289 108287979750357284774952217)
    ·
      refine ⟨81215984812767963581214163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108287979750357284774952217 81215984812767963581214163)
      ·
        refine ⟨121823977219151945371821245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81215984812767963581214163 121823977219151945371821245)
        ·
          refine ⟨45683991457181979514432967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121823977219151945371821245 45683991457181979514432967)
          ·
            refine ⟨68525987185772969271649451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683991457181979514432967 68525987185772969271649451)
            ·
              refine ⟨102788980778659453907474177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68525987185772969271649451 102788980778659453907474177)
              ·
                refine ⟨77091735583994590430605633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102788980778659453907474177 77091735583994590430605633)
                ·
                  refine ⟨57818801687995942822954225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77091735583994590430605633 57818801687995942822954225)
                  ·
                    refine ⟨43364101265996957117215669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57818801687995942822954225 43364101265996957117215669)
                    ·
                      refine ⟨4065384493687214729738969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43364101265996957117215669 4065384493687214729738969)
                      ·
                        rfl

theorem cell23_7917308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_7917308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917308 prefixEnd_7917308 := by exact prefixLift 7917308
  have htrace : WordTrace (prefixWord ++ tailWord_7917308) baseStart_7917308 baseEnd_7917308 := by
    simpa [prefixWord, tailWord_7917308, baseEnd_7917308] using wordTrace_append hprefix tailTrace_7917308
  have hstable : (prefixWord ++ tailWord_7917308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917308).length < 2 ^ (prefixWord ++ tailWord_7917308).sum := by decide
  have hdescent : baseEnd_7917308 < baseStart_7917308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917352 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7917352 : Nat := 118140960795 + 7917352 * 2 ^ 59
def prefixEnd_7917352 : Nat := 4983230072969 + 3 ^ 40 * 7917352 * 2
def baseEnd_7917352 : Nat := 4065407086836012557588767

theorem tailTrace_7917352 : CollatzResearch.WordTrace tailWord_7917352 prefixEnd_7917352 4065407086836012557588767 := by
  unfold tailWord_7917352
  simp only [CollatzResearch.WordTrace]
  refine ⟨144384775406396677457237155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192513033875195569942982873 144384775406396677457237155)
  ·
    refine ⟨216577163109595016185855733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144384775406396677457237155 216577163109595016185855733)
    ·
      refine ⟨20304109041524532767423975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216577163109595016185855733 20304109041524532767423975)
      ·
        refine ⟨30456163562286799151135963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20304109041524532767423975 30456163562286799151135963)
        ·
          refine ⟨45684245343430198726703945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30456163562286799151135963 45684245343430198726703945)
          ·
            refine ⟨34263184007572649045027959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45684245343430198726703945 34263184007572649045027959)
            ·
              refine ⟨51394776011358973567541939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34263184007572649045027959 51394776011358973567541939)
              ·
                refine ⟨77092164017038460351312909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51394776011358973567541939 77092164017038460351312909)
                ·
                  refine ⟨28909561506389422631742341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77092164017038460351312909 28909561506389422631742341)
                  ·
                    refine ⟨5420542782448016743451689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28909561506389422631742341 5420542782448016743451689)
                    ·
                      refine ⟨4065407086836012557588767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420542782448016743451689 4065407086836012557588767)
                      ·
                        rfl

theorem cell23_7917352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7917352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917352 prefixEnd_7917352 := by exact prefixLift 7917352
  have htrace : WordTrace (prefixWord ++ tailWord_7917352) baseStart_7917352 baseEnd_7917352 := by
    simpa [prefixWord, tailWord_7917352, baseEnd_7917352] using wordTrace_append hprefix tailTrace_7917352
  have hstable : (prefixWord ++ tailWord_7917352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917352).length < 2 ^ (prefixWord ++ tailWord_7917352).sum := by decide
  have hdescent : baseEnd_7917352 < baseStart_7917352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917385 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_7917385 : Nat := 118140960795 + 7917385 * 2 ^ 59
def prefixEnd_7917385 : Nat := 4983230072969 + 3 ^ 40 * 7917385 * 2
def baseEnd_7917385 : Nat := 4065424031697610928476115

theorem tailTrace_7917385 : CollatzResearch.WordTrace tailWord_7917385 prefixEnd_7917385 4065424031697610928476115 := by
  unfold tailWord_7917385
  simp only [CollatzResearch.WordTrace]
  refine ⟨288770754421673801550425609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192513836281115867700283739 288770754421673801550425609)
  ·
    refine ⟨216578065816255351162819207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288770754421673801550425609 216578065816255351162819207)
    ·
      refine ⟨324867098724383026744228811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216578065816255351162819207 324867098724383026744228811)
      ·
        refine ⟨487300648086574540116343217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324867098724383026744228811 487300648086574540116343217)
        ·
          refine ⟨365475486064930905087257413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487300648086574540116343217 365475486064930905087257413)
          ·
            refine ⟨68526653637174544703860765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365475486064930905087257413 68526653637174544703860765)
            ·
              refine ⟨25697495113940454263947787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68526653637174544703860765 25697495113940454263947787)
              ·
                refine ⟨38546242670910681395921681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25697495113940454263947787 38546242670910681395921681)
                ·
                  refine ⟨28909682003183011046941261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38546242670910681395921681 28909682003183011046941261)
                  ·
                    refine ⟨10841130751193629142602973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28909682003183011046941261 10841130751193629142602973)
                    ·
                      refine ⟨4065424031697610928476115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841130751193629142602973 4065424031697610928476115)
                      ·
                        rfl

theorem cell23_7917385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_7917385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917385 prefixEnd_7917385 := by exact prefixLift 7917385
  have htrace : WordTrace (prefixWord ++ tailWord_7917385) baseStart_7917385 baseEnd_7917385 := by
    simpa [prefixWord, tailWord_7917385, baseEnd_7917385] using wordTrace_append hprefix tailTrace_7917385
  have hstable : (prefixWord ++ tailWord_7917385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917385).length < 2 ^ (prefixWord ++ tailWord_7917385).sum := by decide
  have hdescent : baseEnd_7917385 < baseStart_7917385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917425 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_7917425 : Nat := 118140960795 + 7917425 * 2 ^ 59
def prefixEnd_7917425 : Nat := 4983230072969 + 3 ^ 40 * 7917425 * 2
def baseEnd_7917425 : Nat := 4065444570923790771975931

theorem tailTrace_7917425 : CollatzResearch.WordTrace tailWord_7917425 prefixEnd_7917425 4065444570923790771975931 := by
  unfold tailWord_7917425
  simp only [CollatzResearch.WordTrace]
  refine ⟨288772213341528888381881729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192514808894352592254587819 288772213341528888381881729)
  ·
    refine ⟨216579160006146666286411297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288772213341528888381881729 216579160006146666286411297)
    ·
      refine ⟨162434370004609999714808473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216579160006146666286411297 162434370004609999714808473)
      ·
        refine ⟨121825777503457499786106355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162434370004609999714808473 121825777503457499786106355)
        ·
          refine ⟨182738666255186249679159533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121825777503457499786106355 182738666255186249679159533)
          ·
            refine ⟨68526999845694843629684825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182738666255186249679159533 68526999845694843629684825)
            ·
              refine ⟨51395249884271132722263619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68526999845694843629684825 51395249884271132722263619)
              ·
                refine ⟨77092874826406699083395429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51395249884271132722263619 77092874826406699083395429)
                ·
                  refine ⟨14454914029951256078136643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77092874826406699083395429 14454914029951256078136643)
                  ·
                    refine ⟨21682371044926884117204965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14454914029951256078136643 21682371044926884117204965)
                    ·
                      refine ⟨4065444570923790771975931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21682371044926884117204965 4065444570923790771975931)
                      ·
                        rfl

theorem cell23_7917425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_7917425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917425 prefixEnd_7917425 := by exact prefixLift 7917425
  have htrace : WordTrace (prefixWord ++ tailWord_7917425) baseStart_7917425 baseEnd_7917425 := by
    simpa [prefixWord, tailWord_7917425, baseEnd_7917425] using wordTrace_append hprefix tailTrace_7917425
  have hstable : (prefixWord ++ tailWord_7917425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917425).length < 2 ^ (prefixWord ++ tailWord_7917425).sum := by decide
  have hdescent : baseEnd_7917425 < baseStart_7917425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917445 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_7917445 : Nat := 118140960795 + 7917445 * 2 ^ 59
def prefixEnd_7917445 : Nat := 4983230072969 + 3 ^ 40 * 7917445 * 2
def baseEnd_7917445 : Nat := 4065454840536880693725839

theorem tailTrace_7917445 : CollatzResearch.WordTrace tailWord_7917445 prefixEnd_7917445 4065454840536880693725839 := by
  unfold tailWord_7917445
  simp only [CollatzResearch.WordTrace]
  refine ⟨288772942801456431797609789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192515295200970954531739859 288772942801456431797609789)
  ·
    refine ⟨108289853550546161924103671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288772942801456431797609789 108289853550546161924103671)
    ·
      refine ⟨162434780325819242886155507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108289853550546161924103671 162434780325819242886155507)
      ·
        refine ⟨243652170488728864329233261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162434780325819242886155507 243652170488728864329233261)
        ·
          refine ⟨91369563933273324123462473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243652170488728864329233261 91369563933273324123462473)
          ·
            refine ⟨68527172949954993092596855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91369563933273324123462473 68527172949954993092596855)
            ·
              refine ⟨102790759424932489638895283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68527172949954993092596855 102790759424932489638895283)
              ·
                refine ⟨154186139137398734458342925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102790759424932489638895283 154186139137398734458342925)
                ·
                  refine ⟨57819802176524525421878597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154186139137398734458342925 57819802176524525421878597)
                  ·
                    refine ⟨10841212908098348516602237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57819802176524525421878597 10841212908098348516602237)
                    ·
                      refine ⟨4065454840536880693725839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841212908098348516602237 4065454840536880693725839)
                      ·
                        rfl

theorem cell23_7917445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_7917445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917445 prefixEnd_7917445 := by exact prefixLift 7917445
  have htrace : WordTrace (prefixWord ++ tailWord_7917445) baseStart_7917445 baseEnd_7917445 := by
    simpa [prefixWord, tailWord_7917445, baseEnd_7917445] using wordTrace_append hprefix tailTrace_7917445
  have hstable : (prefixWord ++ tailWord_7917445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917445).length < 2 ^ (prefixWord ++ tailWord_7917445).sum := by decide
  have hdescent : baseEnd_7917445 < baseStart_7917445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917479 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_7917479 : Nat := 118140960795 + 7917479 * 2 ^ 59
def prefixEnd_7917479 : Nat := 4983230072969 + 3 ^ 40 * 7917479 * 2
def baseEnd_7917479 : Nat := 4065472298879133560700683

theorem tailTrace_7917479 : CollatzResearch.WordTrace tailWord_7917479 prefixEnd_7917479 4065472298879133560700683 := by
  unfold tailWord_7917479
  simp only [CollatzResearch.WordTrace]
  refine ⟨288774182883333255604347491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192516121922222170402898327 288774182883333255604347491)
  ·
    refine ⟨433161274324999883406521237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288774182883333255604347491 433161274324999883406521237)
    ·
      refine ⟨20304434733984369534680683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 433161274324999883406521237 20304434733984369534680683)
      ·
        refine ⟨30456652100976554302021025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20304434733984369534680683 30456652100976554302021025)
        ·
          refine ⟨22842489075732415726515769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30456652100976554302021025 22842489075732415726515769)
          ·
            refine ⟨17131866806799311794886827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22842489075732415726515769 17131866806799311794886827)
            ·
              refine ⟨25697800210198967692330241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131866806799311794886827 25697800210198967692330241)
              ·
                refine ⟨19273350157649225769247681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25697800210198967692330241 19273350157649225769247681)
                ·
                  refine ⟨14455012618236919326935761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19273350157649225769247681 14455012618236919326935761)
                  ·
                    refine ⟨10841259463677689495201821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14455012618236919326935761 10841259463677689495201821)
                    ·
                      refine ⟨4065472298879133560700683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841259463677689495201821 4065472298879133560700683)
                      ·
                        rfl

theorem cell23_7917479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_7917479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917479 prefixEnd_7917479 := by exact prefixLift 7917479
  have htrace : WordTrace (prefixWord ++ tailWord_7917479) baseStart_7917479 baseEnd_7917479 := by
    simpa [prefixWord, tailWord_7917479, baseEnd_7917479] using wordTrace_append hprefix tailTrace_7917479
  have hstable : (prefixWord ++ tailWord_7917479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917479).length < 2 ^ (prefixWord ++ tailWord_7917479).sum := by decide
  have hdescent : baseEnd_7917479 < baseStart_7917479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917495 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 3, 5]
def baseStart_7917495 : Nat := 118140960795 + 7917495 * 2 ^ 59
def prefixEnd_7917495 : Nat := 4983230072969 + 3 ^ 40 * 7917495 * 2
def baseEnd_7917495 : Nat := 1355160171523201832700203

theorem tailTrace_7917495 : CollatzResearch.WordTrace tailWord_7917495 prefixEnd_7917495 1355160171523201832700203 := by
  unfold tailWord_7917495
  simp only [CollatzResearch.WordTrace]
  refine ⟨288774766451275290336929939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192516510967516860224619959 288774766451275290336929939)
  ·
    refine ⟨433162149676912935505394909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288774766451275290336929939 433162149676912935505394909)
    ·
      refine ⟨162435806128842350814523091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433162149676912935505394909 162435806128842350814523091)
      ·
        refine ⟨243653709193263526221784637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162435806128842350814523091 243653709193263526221784637)
        ·
          refine ⟨91370140947473822333169239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243653709193263526221784637 91370140947473822333169239)
          ·
            refine ⟨137055211421210733499753859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91370140947473822333169239 137055211421210733499753859)
            ·
              refine ⟨205582817131816100249630789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137055211421210733499753859 205582817131816100249630789)
              ·
                refine ⟨38546778212215518796805773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205582817131816100249630789 38546778212215518796805773)
                ·
                  refine ⟨14455041829580819548802165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38546778212215518796805773 14455041829580819548802165)
                  ·
                    refine ⟨1355160171523201832700203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14455041829580819548802165 1355160171523201832700203)
                    ·
                      rfl

theorem cell23_7917495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_7917495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917495 prefixEnd_7917495 := by exact prefixLift 7917495
  have htrace : WordTrace (prefixWord ++ tailWord_7917495) baseStart_7917495 baseEnd_7917495 := by
    simpa [prefixWord, tailWord_7917495, baseEnd_7917495] using wordTrace_append hprefix tailTrace_7917495
  have hstable : (prefixWord ++ tailWord_7917495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917495).length < 2 ^ (prefixWord ++ tailWord_7917495).sum := by decide
  have hdescent : baseEnd_7917495 < baseStart_7917495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917512 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_7917512 : Nat := 118140960795 + 7917512 * 2 ^ 59
def prefixEnd_7917512 : Nat := 4983230072969 + 3 ^ 40 * 7917512 * 2
def baseEnd_7917512 : Nat := 1355163081246910643862677

theorem tailTrace_7917512 : CollatzResearch.WordTrace tailWord_7917512 prefixEnd_7917512 1355163081246910643862677 := by
  unfold tailWord_7917512
  simp only [CollatzResearch.WordTrace]
  refine ⟨144387693246106851120149395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192516924328142468160199193 144387693246106851120149395)
  ·
    refine ⟨216581539869160276680224093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144387693246106851120149395 216581539869160276680224093)
    ·
      refine ⟨81218077450935103755084035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216581539869160276680224093 81218077450935103755084035)
      ·
        refine ⟨121827116176402655632626053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81218077450935103755084035 121827116176402655632626053)
        ·
          refine ⟨22842584283075497931117385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121827116176402655632626053 22842584283075497931117385)
          ·
            refine ⟨17131938212306623448338039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22842584283075497931117385 17131938212306623448338039)
            ·
              refine ⟨25697907318459935172507059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131938212306623448338039 25697907318459935172507059)
              ·
                refine ⟨38546860977689902758760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25697907318459935172507059 38546860977689902758760589)
                ·
                  refine ⟨14455072866633713534535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38546860977689902758760589 14455072866633713534535221)
                  ·
                    refine ⟨1355163081246910643862677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14455072866633713534535221 1355163081246910643862677)
                    ·
                      rfl

theorem cell23_7917512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_7917512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917512 prefixEnd_7917512 := by exact prefixLift 7917512
  have htrace : WordTrace (prefixWord ++ tailWord_7917512) baseStart_7917512 baseEnd_7917512 := by
    simpa [prefixWord, tailWord_7917512, baseEnd_7917512] using wordTrace_append hprefix tailTrace_7917512
  have hstable : (prefixWord ++ tailWord_7917512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917512).length < 2 ^ (prefixWord ++ tailWord_7917512).sum := by decide
  have hdescent : baseEnd_7917512 < baseStart_7917512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917519 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 2, 3, 2]
def baseStart_7917519 : Nat := 118140960795 + 7917519 * 2 ^ 59
def prefixEnd_7917519 : Nat := 4983230072969 + 3 ^ 40 * 7917519 * 2
def baseEnd_7917519 : Nat := 4065492838105313404200499

theorem tailTrace_7917519 : CollatzResearch.WordTrace tailWord_7917519 prefixEnd_7917519 4065492838105313404200499 := by
  unfold tailWord_7917519
  simp only [CollatzResearch.WordTrace]
  refine ⟨288775641803188342435803611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192517094535458894957202407 288775641803188342435803611)
  ·
    refine ⟨433163462704782513653705417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288775641803188342435803611 433163462704782513653705417)
    ·
      refine ⟨324872597028586885240279063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433163462704782513653705417 324872597028586885240279063)
      ·
        refine ⟨487308895542880327860418595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324872597028586885240279063 487308895542880327860418595)
        ·
          refine ⟨730963343314320491790627893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487308895542880327860418595 730963343314320491790627893)
          ·
            refine ⟨68527813435717546105371365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 730963343314320491790627893 68527813435717546105371365)
            ·
              refine ⟨12848965019197039894757131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68527813435717546105371365 12848965019197039894757131)
              ·
                refine ⟨19273447528795559842135697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848965019197039894757131 19273447528795559842135697)
                ·
                  refine ⟨14455085646596669881601773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19273447528795559842135697 14455085646596669881601773)
                  ·
                    refine ⟨5420657117473751205600665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14455085646596669881601773 5420657117473751205600665)
                    ·
                      refine ⟨4065492838105313404200499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420657117473751205600665 4065492838105313404200499)
                      ·
                        rfl

theorem cell23_7917519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3, 2].length) (baseStart_7917519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917519 prefixEnd_7917519 := by exact prefixLift 7917519
  have htrace : WordTrace (prefixWord ++ tailWord_7917519) baseStart_7917519 baseEnd_7917519 := by
    simpa [prefixWord, tailWord_7917519, baseEnd_7917519] using wordTrace_append hprefix tailTrace_7917519
  have hstable : (prefixWord ++ tailWord_7917519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917519).length < 2 ^ (prefixWord ++ tailWord_7917519).sum := by decide
  have hdescent : baseEnd_7917519 < baseStart_7917519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917543 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7917543 : Nat := 118140960795 + 7917543 * 2 ^ 59
def prefixEnd_7917543 : Nat := 4983230072969 + 3 ^ 40 * 7917543 * 2
def baseEnd_7917543 : Nat := 4065505161641021310300389

theorem tailTrace_7917543 : CollatzResearch.WordTrace tailWord_7917543 prefixEnd_7917543 4065505161641021310300389 := by
  unfold tailWord_7917543
  simp only [CollatzResearch.WordTrace]
  refine ⟨288776517155101394534677283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192517678103400929689784855 288776517155101394534677283)
  ·
    refine ⟨433164775732652091802015925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288776517155101394534677283 433164775732652091802015925)
    ·
      refine ⟨40609197724936133606438993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 433164775732652091802015925 40609197724936133606438993)
      ·
        refine ⟨30456898293702100204829245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40609197724936133606438993 30456898293702100204829245)
        ·
          refine ⟨11421336860138287576810967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30456898293702100204829245 11421336860138287576810967)
          ·
            refine ⟨17132005290207431365216451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421336860138287576810967 17132005290207431365216451)
            ·
              refine ⟨25698007935311147047824677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132005290207431365216451 25698007935311147047824677)
              ·
                refine ⟨4818376487870840071467127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25698007935311147047824677 4818376487870840071467127)
                ·
                  refine ⟨7227564731806260107200691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818376487870840071467127 7227564731806260107200691)
                  ·
                    refine ⟨10841347097709390160801037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227564731806260107200691 10841347097709390160801037)
                    ·
                      refine ⟨4065505161641021310300389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841347097709390160801037 4065505161641021310300389)
                      ·
                        rfl

theorem cell23_7917543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7917543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917543 prefixEnd_7917543 := by exact prefixLift 7917543
  have htrace : WordTrace (prefixWord ++ tailWord_7917543) baseStart_7917543 baseEnd_7917543 := by
    simpa [prefixWord, tailWord_7917543, baseEnd_7917543] using wordTrace_append hprefix tailTrace_7917543
  have hstable : (prefixWord ++ tailWord_7917543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917543).length < 2 ^ (prefixWord ++ tailWord_7917543).sum := by decide
  have hdescent : baseEnd_7917543 < baseStart_7917543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917552 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_7917552 : Nat := 118140960795 + 7917552 * 2 ^ 59
def prefixEnd_7917552 : Nat := 4983230072969 + 3 ^ 40 * 7917552 * 2
def baseEnd_7917552 : Nat := 4065509782966911775087847

theorem tailTrace_7917552 : CollatzResearch.WordTrace tailWord_7917552 prefixEnd_7917552 4065509782966911775087847 := by
  unfold tailWord_7917552
  simp only [CollatzResearch.WordTrace]
  refine ⟨144388422706034394535877455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192517896941379192714503273 144388422706034394535877455)
  ·
    refine ⟨216582634059051591803816183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144388422706034394535877455 216582634059051591803816183)
    ·
      refine ⟨324873951088577387705724275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216582634059051591803816183 324873951088577387705724275)
      ·
        refine ⟨487310926632866081558586413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324873951088577387705724275 487310926632866081558586413)
        ·
          refine ⟨182741597487324780584469905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 487310926632866081558586413 182741597487324780584469905)
          ·
            refine ⟨137056198115493585438352429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182741597487324780584469905 137056198115493585438352429)
            ·
              refine ⟨51396074293310094539382161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137056198115493585438352429 51396074293310094539382161)
              ·
                refine ⟨38547055719982570904536621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51396074293310094539382161 38547055719982570904536621)
                ·
                  refine ⟨14455145894993464089201233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38547055719982570904536621 14455145894993464089201233)
                  ·
                    refine ⟨10841359421245098066900925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14455145894993464089201233 10841359421245098066900925)
                    ·
                      refine ⟨4065509782966911775087847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841359421245098066900925 4065509782966911775087847)
                      ·
                        rfl

theorem cell23_7917552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_7917552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917552 prefixEnd_7917552 := by exact prefixLift 7917552
  have htrace : WordTrace (prefixWord ++ tailWord_7917552) baseStart_7917552 baseEnd_7917552 := by
    simpa [prefixWord, tailWord_7917552, baseEnd_7917552] using wordTrace_append hprefix tailTrace_7917552
  have hstable : (prefixWord ++ tailWord_7917552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917552).length < 2 ^ (prefixWord ++ tailWord_7917552).sum := by decide
  have hdescent : baseEnd_7917552 < baseStart_7917552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917569 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_7917569 : Nat := 118140960795 + 7917569 * 2 ^ 59
def prefixEnd_7917569 : Nat := 4983230072969 + 3 ^ 40 * 7917569 * 2
def baseEnd_7917569 : Nat := 4065518512138038208575269

theorem tailTrace_7917569 : CollatzResearch.WordTrace tailWord_7917569 prefixEnd_7917569 4065518512138038208575269 := by
  unfold tailWord_7917569
  simp only [CollatzResearch.WordTrace]
  refine ⟨288777465453007200975123761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192518310302004800650082507 288777465453007200975123761)
  ·
    refine ⟨216583099089755400731342821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288777465453007200975123761 216583099089755400731342821)
    ·
      refine ⟨40609331079329137637126779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216583099089755400731342821 40609331079329137637126779)
      ·
        refine ⟨60913996618993706455690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40609331079329137637126779 60913996618993706455690169)
        ·
          refine ⟨45685497464245279841767627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60913996618993706455690169 45685497464245279841767627)
          ·
            refine ⟨68528246196367919762651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45685497464245279841767627 68528246196367919762651441)
            ·
              refine ⟨51396184647275939821988581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68528246196367919762651441 51396184647275939821988581)
              ·
                refine ⟨9636784621364238716622859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51396184647275939821988581 9636784621364238716622859)
                ·
                  refine ⟨14455176932046358074934289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636784621364238716622859 14455176932046358074934289)
                  ·
                    refine ⟨10841382699034768556200717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14455176932046358074934289 10841382699034768556200717)
                    ·
                      refine ⟨4065518512138038208575269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841382699034768556200717 4065518512138038208575269)
                      ·
                        rfl

theorem cell23_7917569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_7917569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917569 prefixEnd_7917569 := by exact prefixLift 7917569
  have htrace : WordTrace (prefixWord ++ tailWord_7917569) baseStart_7917569 baseEnd_7917569 := by
    simpa [prefixWord, tailWord_7917569, baseEnd_7917569] using wordTrace_append hprefix tailTrace_7917569
  have hstable : (prefixWord ++ tailWord_7917569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917569).length < 2 ^ (prefixWord ++ tailWord_7917569).sum := by decide
  have hdescent : baseEnd_7917569 < baseStart_7917569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917595 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_7917595 : Nat := 118140960795 + 7917595 * 2 ^ 59
def prefixEnd_7917595 : Nat := 4983230072969 + 3 ^ 40 * 7917595 * 2
def baseEnd_7917595 : Nat := 4065531862635055106850149

theorem tailTrace_7917595 : CollatzResearch.WordTrace tailWord_7917595 prefixEnd_7917595 4065531862635055106850149 := by
  unfold tailWord_7917595
  simp only [CollatzResearch.WordTrace]
  refine ⟨288778413750913007415570239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192518942500608671610380159 288778413750913007415570239)
  ·
    refine ⟨433167620626369511123355359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288778413750913007415570239 433167620626369511123355359)
    ·
      refine ⟨649751430939554266685033039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433167620626369511123355359 649751430939554266685033039)
      ·
        refine ⟨974627146409331400027549559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649751430939554266685033039 974627146409331400027549559)
        ·
          refine ⟨1461940719613997100041324339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974627146409331400027549559 1461940719613997100041324339)
          ·
            refine ⟨2192911079420995650061986509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461940719613997100041324339 2192911079420995650061986509)
            ·
              refine ⟨822341654782873368773244941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192911079420995650061986509 822341654782873368773244941)
              ·
                refine ⟨308378120543577513289966853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822341654782873368773244941 308378120543577513289966853)
                ·
                  refine ⟨57820897601920783741868785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308378120543577513289966853 57820897601920783741868785)
                  ·
                    refine ⟨43365673201440587806401589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57820897601920783741868785 43365673201440587806401589)
                    ·
                      refine ⟨4065531862635055106850149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43365673201440587806401589 4065531862635055106850149)
                      ·
                        rfl

theorem cell23_7917595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_7917595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917595 prefixEnd_7917595 := by exact prefixLift 7917595
  have htrace : WordTrace (prefixWord ++ tailWord_7917595) baseStart_7917595 baseEnd_7917595 := by
    simpa [prefixWord, tailWord_7917595, baseEnd_7917595] using wordTrace_append hprefix tailTrace_7917595
  have hstable : (prefixWord ++ tailWord_7917595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917595).length < 2 ^ (prefixWord ++ tailWord_7917595).sum := by decide
  have hdescent : baseEnd_7917595 < baseStart_7917595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917599 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_7917599 : Nat := 118140960795 + 7917599 * 2 ^ 59
def prefixEnd_7917599 : Nat := 4983230072969 + 3 ^ 40 * 7917599 * 2
def baseEnd_7917599 : Nat := 4065533916557673091200131

theorem tailTrace_7917599 : CollatzResearch.WordTrace tailWord_7917599 prefixEnd_7917599 4065533916557673091200131 := by
  unfold tailWord_7917599
  simp only [CollatzResearch.WordTrace]
  refine ⟨288778559642898516098715851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192519039761932344065810567 288778559642898516098715851)
  ·
    refine ⟨433167839464347774148073777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288778559642898516098715851 433167839464347774148073777)
    ·
      refine ⟨324875879598260830611055333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433167839464347774148073777 324875879598260830611055333)
      ·
        refine ⟨60914227424673905739572875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324875879598260830611055333 60914227424673905739572875)
        ·
          refine ⟨91371341137010858609359313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60914227424673905739572875 91371341137010858609359313)
          ·
            refine ⟨68528505852758143957019485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91371341137010858609359313 68528505852758143957019485)
            ·
              refine ⟨25698189694784303983882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68528505852758143957019485 25698189694784303983882307)
              ·
                refine ⟨38547284542176455975823461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25698189694784303983882307 38547284542176455975823461)
                ·
                  refine ⟨7227615851658085495466899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38547284542176455975823461 7227615851658085495466899)
                  ·
                    refine ⟨10841423777487128243200349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227615851658085495466899 10841423777487128243200349)
                    ·
                      refine ⟨4065533916557673091200131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841423777487128243200349 4065533916557673091200131)
                      ·
                        rfl

theorem cell23_7917599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_7917599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917599 prefixEnd_7917599 := by exact prefixLift 7917599
  have htrace : WordTrace (prefixWord ++ tailWord_7917599) baseStart_7917599 baseEnd_7917599 := by
    simpa [prefixWord, tailWord_7917599, baseEnd_7917599] using wordTrace_append hprefix tailTrace_7917599
  have hstable : (prefixWord ++ tailWord_7917599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917599).length < 2 ^ (prefixWord ++ tailWord_7917599).sum := by decide
  have hdescent : baseEnd_7917599 < baseStart_7917599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917615 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 8]
def baseStart_7917615 : Nat := 118140960795 + 7917615 * 2 ^ 59
def prefixEnd_7917615 : Nat := 4983230072969 + 3 ^ 40 * 7917615 * 2
def baseEnd_7917615 : Nat := 1355180710749381676200019

theorem tailTrace_7917615 : CollatzResearch.WordTrace tailWord_7917615 prefixEnd_7917615 1355180710749381676200019 := by
  unfold tailWord_7917615
  simp only [CollatzResearch.WordTrace]
  refine ⟨288779143210840550831298299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192519428807227033887532199 288779143210840550831298299)
  ·
    refine ⟨433168714816260826246947449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288779143210840550831298299 433168714816260826246947449)
    ·
      refine ⟨324876536112195619685210587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433168714816260826246947449 324876536112195619685210587)
      ·
        refine ⟨487314804168293429527815881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324876536112195619685210587 487314804168293429527815881)
        ·
          refine ⟨365486103126220072145861911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487314804168293429527815881 365486103126220072145861911)
          ·
            refine ⟨548229154689330108218792867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365486103126220072145861911 548229154689330108218792867)
            ·
              refine ⟨822343732033995162328189301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548229154689330108218792867 822343732033995162328189301)
              ·
                refine ⟨77094724878187046468267747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 822343732033995162328189301 77094724878187046468267747)
                ·
                  refine ⟨115642087317280569702401621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77094724878187046468267747 115642087317280569702401621)
                  ·
                    refine ⟨1355180710749381676200019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115642087317280569702401621 1355180710749381676200019)
                    ·
                      rfl

theorem cell23_7917615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_7917615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917615 prefixEnd_7917615 := by exact prefixLift 7917615
  have htrace : WordTrace (prefixWord ++ tailWord_7917615) baseStart_7917615 baseEnd_7917615 := by
    simpa [prefixWord, tailWord_7917615, baseEnd_7917615] using wordTrace_append hprefix tailTrace_7917615
  have hstable : (prefixWord ++ tailWord_7917615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917615).length < 2 ^ (prefixWord ++ tailWord_7917615).sum := by decide
  have hdescent : baseEnd_7917615 < baseStart_7917615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917639 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_7917639 : Nat := 118140960795 + 7917639 * 2 ^ 59
def prefixEnd_7917639 : Nat := 4983230072969 + 3 ^ 40 * 7917639 * 2
def baseEnd_7917639 : Nat := 4065554455783852934699947

theorem tailTrace_7917639 : CollatzResearch.WordTrace tailWord_7917639 prefixEnd_7917639 4065554455783852934699947 := by
  unfold tailWord_7917639
  simp only [CollatzResearch.WordTrace]
  refine ⟨288780018562753602930171971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192520012375169068620114647 288780018562753602930171971)
  ·
    refine ⟨433170027844130404395257957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288780018562753602930171971 433170027844130404395257957)
    ·
      refine ⟨81219380220774450824110867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433170027844130404395257957 81219380220774450824110867)
      ·
        refine ⟨121829070331161676236166301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81219380220774450824110867 121829070331161676236166301)
        ·
          refine ⟨45685901374185628588562363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121829070331161676236166301 45685901374185628588562363)
          ·
            refine ⟨68528852061278442882843545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45685901374185628588562363 68528852061278442882843545)
            ·
              refine ⟨51396639045958832162132659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68528852061278442882843545 51396639045958832162132659)
              ·
                refine ⟨77094958568938248243198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51396639045958832162132659 77094958568938248243198989)
                ·
                  refine ⟨28910609463351843091199621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77094958568938248243198989 28910609463351843091199621)
                  ·
                    refine ⟨5420739274378470579599929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28910609463351843091199621 5420739274378470579599929)
                    ·
                      refine ⟨4065554455783852934699947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420739274378470579599929 4065554455783852934699947)
                      ·
                        rfl

theorem cell23_7917639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_7917639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917639 prefixEnd_7917639 := by exact prefixLift 7917639
  have htrace : WordTrace (prefixWord ++ tailWord_7917639) baseStart_7917639 baseEnd_7917639 := by
    simpa [prefixWord, tailWord_7917639, baseEnd_7917639] using wordTrace_append hprefix tailTrace_7917639
  have hstable : (prefixWord ++ tailWord_7917639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917639).length < 2 ^ (prefixWord ++ tailWord_7917639).sum := by decide
  have hdescent : baseEnd_7917639 < baseStart_7917639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_7917642 : Nat := 118140960795 + 7917642 * 2 ^ 59
def prefixEnd_7917642 : Nat := 4983230072969 + 3 ^ 40 * 7917642 * 2
def baseEnd_7917642 : Nat := 4065555996225816422962433

theorem tailTrace_7917642 : CollatzResearch.WordTrace tailWord_7917642 prefixEnd_7917642 4065555996225816422962433 := by
  unfold tailWord_7917642
  simp only [CollatzResearch.WordTrace]
  refine ⟨72195031995435683610632795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192520085321161822961687453 72195031995435683610632795)
  ·
    refine ⟨108292547993153525415949193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72195031995435683610632795 108292547993153525415949193)
    ·
      refine ⟨81219410994865144061961895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108292547993153525415949193 81219410994865144061961895)
      ·
        refine ⟨121829116492297716092942843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81219410994865144061961895 121829116492297716092942843)
        ·
          refine ⟨182743674738446574139414265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121829116492297716092942843 182743674738446574139414265)
          ·
            refine ⟨137057756053834930604560699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182743674738446574139414265 137057756053834930604560699)
            ·
              refine ⟨205586634080752395906841049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137057756053834930604560699 205586634080752395906841049)
              ·
                refine ⟨154189975560564296930130787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205586634080752395906841049 154189975560564296930130787)
                ·
                  refine ⟨231284963340846445395196181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154189975560564296930130787 231284963340846445395196181)
                  ·
                    refine ⟨10841482656602177127899821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231284963340846445395196181 10841482656602177127899821)
                    ·
                      refine ⟨4065555996225816422962433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841482656602177127899821 4065555996225816422962433)
                      ·
                        rfl

theorem cell23_7917642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_7917642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917642 prefixEnd_7917642 := by exact prefixLift 7917642
  have htrace : WordTrace (prefixWord ++ tailWord_7917642) baseStart_7917642 baseEnd_7917642 := by
    simpa [prefixWord, tailWord_7917642, baseEnd_7917642] using wordTrace_append hprefix tailTrace_7917642
  have hstable : (prefixWord ++ tailWord_7917642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917642).length < 2 ^ (prefixWord ++ tailWord_7917642).sum := by decide
  have hdescent : baseEnd_7917642 < baseStart_7917642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917656 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2]
def baseStart_7917656 : Nat := 118140960795 + 7917656 * 2 ^ 59
def prefixEnd_7917656 : Nat := 4983230072969 + 3 ^ 40 * 7917656 * 2
def baseEnd_7917656 : Nat := 4065563184954979368187369

theorem tailTrace_7917656 : CollatzResearch.WordTrace tailWord_7917656 prefixEnd_7917656 4065563184954979368187369 := by
  unfold tailWord_7917656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144390319301846007416770411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192520425735794676555693881 144390319301846007416770411)
  ·
    refine ⟨216585478952769011125155617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144390319301846007416770411 216585478952769011125155617)
    ·
      refine ⟨162439109214576758343866713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216585478952769011125155617 162439109214576758343866713)
      ·
        refine ⟨121829331910932568757900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162439109214576758343866713 121829331910932568757900035)
        ·
          refine ⟨182743997866398853136850053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121829331910932568757900035 182743997866398853136850053)
          ·
            refine ⟨34264499599949784963159385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182743997866398853136850053 34264499599949784963159385)
            ·
              refine ⟨25698374699962338722369539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34264499599949784963159385 25698374699962338722369539)
              ·
                refine ⟨38547562049943508083554309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25698374699962338722369539 38547562049943508083554309)
                ·
                  refine ⟨7227667884364407765666433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38547562049943508083554309 7227667884364407765666433)
                  ·
                    refine ⟨5420750913273305824249825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7227667884364407765666433 5420750913273305824249825)
                    ·
                      refine ⟨4065563184954979368187369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420750913273305824249825 4065563184954979368187369)
                      ·
                        rfl

theorem cell23_7917656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_7917656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917656 prefixEnd_7917656 := by exact prefixLift 7917656
  have htrace : WordTrace (prefixWord ++ tailWord_7917656) baseStart_7917656 baseEnd_7917656 := by
    simpa [prefixWord, tailWord_7917656, baseEnd_7917656] using wordTrace_append hprefix tailTrace_7917656
  have hstable : (prefixWord ++ tailWord_7917656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917656).length < 2 ^ (prefixWord ++ tailWord_7917656).sum := by decide
  have hdescent : baseEnd_7917656 < baseStart_7917656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917752 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 8]
def baseStart_7917752 : Nat := 118140960795 + 7917752 * 2 ^ 59
def prefixEnd_7917752 : Nat := 4983230072969 + 3 ^ 40 * 7917752 * 2
def baseEnd_7917752 : Nat := 451734719899756776954103

theorem tailTrace_7917752 : CollatzResearch.WordTrace tailWord_7917752 prefixEnd_7917752 451734719899756776954103 := by
  unfold tailWord_7917752
  simp only [CollatzResearch.WordTrace]
  refine ⟨144392070005672111614517755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192522760007562815486023673 144392070005672111614517755)
  ·
    refine ⟨216588105008508167421776633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144392070005672111614517755 216588105008508167421776633)
    ·
      refine ⟨162441078756381125566332475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216588105008508167421776633 162441078756381125566332475)
      ·
        refine ⟨243661618134571688349498713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162441078756381125566332475 243661618134571688349498713)
        ·
          refine ⟨182746213600928766262124035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243661618134571688349498713 182746213600928766262124035)
          ·
            refine ⟨274119320401393149393186053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182746213600928766262124035 274119320401393149393186053)
            ·
              refine ⟨51397372575261215511222385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274119320401393149393186053 51397372575261215511222385)
              ·
                refine ⟨38548029431445911633416789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51397372575261215511222385 38548029431445911633416789)
                ·
                  refine ⟨451734719899756776954103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38548029431445911633416789 451734719899756776954103)
                  ·
                    rfl

theorem cell23_7917752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_7917752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917752 prefixEnd_7917752 := by exact prefixLift 7917752
  have htrace : WordTrace (prefixWord ++ tailWord_7917752) baseStart_7917752 baseEnd_7917752 := by
    simpa [prefixWord, tailWord_7917752, baseEnd_7917752] using wordTrace_append hprefix tailTrace_7917752
  have hstable : (prefixWord ++ tailWord_7917752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917752).length < 2 ^ (prefixWord ++ tailWord_7917752).sum := by decide
  have hdescent : baseEnd_7917752 < baseStart_7917752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917850 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_7917850 : Nat := 118140960795 + 7917850 * 2 ^ 59
def prefixEnd_7917850 : Nat := 4983230072969 + 3 ^ 40 * 7917850 * 2
def baseEnd_7917850 : Nat := 1355220933400650536387159

theorem tailTrace_7917850 : CollatzResearch.WordTrace tailWord_7917850 prefixEnd_7917850 1355220933400650536387159 := by
  unfold tailWord_7917850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72196928591247296491525751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192525142909992790644068669 72196928591247296491525751)
  ·
    refine ⟨108295392886870944737288627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72196928591247296491525751 108295392886870944737288627)
    ·
      refine ⟨162443089330306417105932941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108295392886870944737288627 162443089330306417105932941)
      ·
        refine ⟨60916158498864906414724853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162443089330306417105932941 60916158498864906414724853)
        ·
          refine ⟨5710889859268584976380455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60916158498864906414724853 5710889859268584976380455)
          ·
            refine ⟨8566334788902877464570683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710889859268584976380455 8566334788902877464570683)
            ·
              refine ⟨12849502183354316196856025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566334788902877464570683 12849502183354316196856025)
              ·
                refine ⟨9637126637515737147642019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12849502183354316196856025 9637126637515737147642019)
                ·
                  refine ⟨14455689956273605721463029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637126637515737147642019 14455689956273605721463029)
                  ·
                    refine ⟨1355220933400650536387159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14455689956273605721463029 1355220933400650536387159)
                    ·
                      rfl

theorem cell23_7917850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_7917850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917850 prefixEnd_7917850 := by exact prefixLift 7917850
  have htrace : WordTrace (prefixWord ++ tailWord_7917850) baseStart_7917850 baseEnd_7917850 := by
    simpa [prefixWord, tailWord_7917850, baseEnd_7917850] using wordTrace_append hprefix tailTrace_7917850
  have hstable : (prefixWord ++ tailWord_7917850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917850).length < 2 ^ (prefixWord ++ tailWord_7917850).sum := by decide
  have hdescent : baseEnd_7917850 < baseStart_7917850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917853 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7917853 : Nat := 118140960795 + 7917853 * 2 ^ 59
def prefixEnd_7917853 : Nat := 4983230072969 + 3 ^ 40 * 7917853 * 2
def baseEnd_7917853 : Nat := 4065664340643915097423963

theorem tailTrace_7917853 : CollatzResearch.WordTrace tailWord_7917853 prefixEnd_7917853 4065664340643915097423963 := by
  unfold tailWord_7917853
  simp only [CollatzResearch.WordTrace]
  refine ⟨288787823783978317478462213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192525215855985544985641475 288787823783978317478462213)
  ·
    refine ⟨54147716959495934527211665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288787823783978317478462213 54147716959495934527211665)
    ·
      refine ⟨40610787719621950895408749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54147716959495934527211665 40610787719621950895408749)
      ·
        refine ⟨15229045394858231585778281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40610787719621950895408749 15229045394858231585778281)
        ·
          refine ⟨11421784046143673689333711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15229045394858231585778281 11421784046143673689333711)
          ·
            refine ⟨17132676069215510534000567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421784046143673689333711 17132676069215510534000567)
            ·
              refine ⟨25699014103823265801000851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132676069215510534000567 25699014103823265801000851)
              ·
                refine ⟨38548521155734898701501277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25699014103823265801000851 38548521155734898701501277)
                ·
                  refine ⟨14455695433400587013062979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38548521155734898701501277 14455695433400587013062979)
                  ·
                    refine ⟨21683543150100880519594469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14455695433400587013062979 21683543150100880519594469)
                    ·
                      refine ⟨4065664340643915097423963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21683543150100880519594469 4065664340643915097423963)
                      ·
                        rfl

theorem cell23_7917853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7917853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917853 prefixEnd_7917853 := by exact prefixLift 7917853
  have htrace : WordTrace (prefixWord ++ tailWord_7917853) baseStart_7917853 baseEnd_7917853 := by
    simpa [prefixWord, tailWord_7917853, baseEnd_7917853] using wordTrace_append hprefix tailTrace_7917853
  have hstable : (prefixWord ++ tailWord_7917853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917853).length < 2 ^ (prefixWord ++ tailWord_7917853).sum := by decide
  have hdescent : baseEnd_7917853 < baseStart_7917853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917873 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_7917873 : Nat := 118140960795 + 7917873 * 2 ^ 59
def prefixEnd_7917873 : Nat := 4983230072969 + 3 ^ 40 * 7917873 * 2
def baseEnd_7917873 : Nat := 4065674610257005019173871

theorem tailTrace_7917873 : CollatzResearch.WordTrace tailWord_7917873 prefixEnd_7917873 4065674610257005019173871 := by
  unfold tailWord_7917873
  simp only [CollatzResearch.WordTrace]
  refine ⟨288788553243905860894190273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192525702162603907262793515 288788553243905860894190273)
  ·
    refine ⟨216591414932929395670642705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288788553243905860894190273 216591414932929395670642705)
    ·
      refine ⟨162443561199697046752982029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216591414932929395670642705 162443561199697046752982029)
      ·
        refine ⟨60916335449886392532368261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162443561199697046752982029 60916335449886392532368261)
        ·
          refine ⟨11421812896853698599819049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60916335449886392532368261 11421812896853698599819049)
          ·
            refine ⟨8566359672640273949864287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11421812896853698599819049 8566359672640273949864287)
            ·
              refine ⟨12849539508960410924796431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566359672640273949864287 12849539508960410924796431)
              ·
                refine ⟨19274309263440616387194647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849539508960410924796431 19274309263440616387194647)
                ·
                  refine ⟨28911463895160924580791971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19274309263440616387194647 28911463895160924580791971)
                  ·
                    refine ⟨43367195842741386871187957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28911463895160924580791971 43367195842741386871187957)
                    ·
                      refine ⟨4065674610257005019173871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43367195842741386871187957 4065674610257005019173871)
                      ·
                        rfl

theorem cell23_7917873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_7917873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917873 prefixEnd_7917873 := by exact prefixLift 7917873
  have htrace : WordTrace (prefixWord ++ tailWord_7917873) baseStart_7917873 baseEnd_7917873 := by
    simpa [prefixWord, tailWord_7917873, baseEnd_7917873] using wordTrace_append hprefix tailTrace_7917873
  have hstable : (prefixWord ++ tailWord_7917873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917873).length < 2 ^ (prefixWord ++ tailWord_7917873).sum := by decide
  have hdescent : baseEnd_7917873 < baseStart_7917873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917913 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 1, 3, 2]
def baseStart_7917913 : Nat := 118140960795 + 7917913 * 2 ^ 59
def prefixEnd_7917913 : Nat := 4983230072969 + 3 ^ 40 * 7917913 * 2
def baseEnd_7917913 : Nat := 4065695149483184862673687

theorem tailTrace_7917913 : CollatzResearch.WordTrace tailWord_7917913 prefixEnd_7917913 4065695149483184862673687 := by
  unfold tailWord_7917913
  simp only [CollatzResearch.WordTrace]
  refine ⟨288790012163760947725646393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192526674775840631817097595 288790012163760947725646393)
  ·
    refine ⟨216592509122820710794234795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288790012163760947725646393 216592509122820710794234795)
    ·
      refine ⟨324888763684231066191352193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216592509122820710794234795 324888763684231066191352193)
      ·
        refine ⟨243666572763173299643514145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324888763684231066191352193 243666572763173299643514145)
        ·
          refine ⟨182749929572379974732635609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243666572763173299643514145 182749929572379974732635609)
          ·
            refine ⟨137062447179284981049476707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182749929572379974732635609 137062447179284981049476707)
            ·
              refine ⟨205593670768927471574215061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137062447179284981049476707 205593670768927471574215061)
              ·
                refine ⟨9637203317293475230041331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205593670768927471574215061 9637203317293475230041331)
                ·
                  refine ⟨14455804975940212845061997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637203317293475230041331 14455804975940212845061997)
                  ·
                    refine ⟨5420926865977579816898249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14455804975940212845061997 5420926865977579816898249)
                    ·
                      refine ⟨4065695149483184862673687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5420926865977579816898249 4065695149483184862673687)
                      ·
                        rfl

theorem cell23_7917913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_7917913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917913 prefixEnd_7917913 := by exact prefixLift 7917913
  have htrace : WordTrace (prefixWord ++ tailWord_7917913) baseStart_7917913 baseEnd_7917913 := by
    simpa [prefixWord, tailWord_7917913, baseEnd_7917913] using wordTrace_append hprefix tailTrace_7917913
  have hstable : (prefixWord ++ tailWord_7917913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917913).length < 2 ^ (prefixWord ++ tailWord_7917913).sum := by decide
  have hdescent : baseEnd_7917913 < baseStart_7917913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917918 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7917918 : Nat := 118140960795 + 7917918 * 2 ^ 59
def prefixEnd_7917918 : Nat := 4983230072969 + 3 ^ 40 * 7917918 * 2
def baseEnd_7917918 : Nat := 1355232572295485781037055

theorem tailTrace_7917918 : CollatzResearch.WordTrace tailWord_7917918 prefixEnd_7917918 1355232572295485781037055 := by
  unfold tailWord_7917918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098774316092854197447301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192526796352495222386385605 36098774316092854197447301)
  ·
    refine ⟨6768520184267410162021369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36098774316092854197447301 6768520184267410162021369)
    ·
      refine ⟨5076390138200557621516027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6768520184267410162021369 5076390138200557621516027)
      ·
        refine ⟨7614585207300836432274041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076390138200557621516027 7614585207300836432274041)
        ·
          refine ⟨5710938905475627324205531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614585207300836432274041 5710938905475627324205531)
          ·
            refine ⟨8566408358213440986308297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710938905475627324205531 8566408358213440986308297)
            ·
              refine ⟨6424806268660080739731223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8566408358213440986308297 6424806268660080739731223)
              ·
                refine ⟨9637209402990121109596835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6424806268660080739731223 9637209402990121109596835)
                ·
                  refine ⟨14455814104485181664395253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637209402990121109596835 14455814104485181664395253)
                  ·
                    refine ⟨1355232572295485781037055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14455814104485181664395253 1355232572295485781037055)
                    ·
                      rfl

theorem cell23_7917918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7917918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917918 prefixEnd_7917918 := by exact prefixLift 7917918
  have htrace : WordTrace (prefixWord ++ tailWord_7917918) baseStart_7917918 baseEnd_7917918 := by
    simpa [prefixWord, tailWord_7917918, baseEnd_7917918] using wordTrace_append hprefix tailTrace_7917918
  have hstable : (prefixWord ++ tailWord_7917918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917918).length < 2 ^ (prefixWord ++ tailWord_7917918).sum := by decide
  have hdescent : baseEnd_7917918 < baseStart_7917918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917929 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_7917929 : Nat := 118140960795 + 7917929 * 2 ^ 59
def prefixEnd_7917929 : Nat := 4983230072969 + 3 ^ 40 * 7917929 * 2
def baseEnd_7917929 : Nat := 4065703365173656800073613

theorem tailTrace_7917929 : CollatzResearch.WordTrace tailWord_7917929 prefixEnd_7917929 4065703365173656800073613 := by
  unfold tailWord_7917929
  simp only [CollatzResearch.WordTrace]
  refine ⟨288790595731702982458228841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192527063821135321638819227 288790595731702982458228841)
  ·
    refine ⟨216592946798777236843671631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288790595731702982458228841 216592946798777236843671631)
    ·
      refine ⟨324889420198165855265507447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216592946798777236843671631 324889420198165855265507447)
      ·
        refine ⟨487334130297248782898261171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324889420198165855265507447 487334130297248782898261171)
        ·
          refine ⟨731001195445873174347391757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487334130297248782898261171 731001195445873174347391757)
          ·
            refine ⟨274125448292202440380271909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 731001195445873174347391757 274125448292202440380271909)
            ·
              refine ⟨51398521554787957571300983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274125448292202440380271909 51398521554787957571300983)
              ·
                refine ⟨77097782332181936356951475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51398521554787957571300983 77097782332181936356951475)
                ·
                  refine ⟨115646673498272904535427213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77097782332181936356951475 115646673498272904535427213)
                  ·
                    refine ⟨43367502561852339200785205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115646673498272904535427213 43367502561852339200785205)
                    ·
                      refine ⟨4065703365173656800073613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43367502561852339200785205 4065703365173656800073613)
                      ·
                        rfl

theorem cell23_7917929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_7917929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917929 prefixEnd_7917929 := by exact prefixLift 7917929
  have htrace : WordTrace (prefixWord ++ tailWord_7917929) baseStart_7917929 baseEnd_7917929 := by
    simpa [prefixWord, tailWord_7917929, baseEnd_7917929] using wordTrace_append hprefix tailTrace_7917929
  have hstable : (prefixWord ++ tailWord_7917929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917929).length < 2 ^ (prefixWord ++ tailWord_7917929).sum := by decide
  have hdescent : baseEnd_7917929 < baseStart_7917929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917939 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_7917939 : Nat := 118140960795 + 7917939 * 2 ^ 59
def prefixEnd_7917939 : Nat := 4983230072969 + 3 ^ 40 * 7917939 * 2
def baseEnd_7917939 : Nat := 4065708499980201760948567

theorem tailTrace_7917939 : CollatzResearch.WordTrace tailWord_7917939 prefixEnd_7917939 4065708499980201760948567 := by
  unfold tailWord_7917939
  simp only [CollatzResearch.WordTrace]
  refine ⟨288790960461666754166092871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192527306974444502777395247 288790960461666754166092871)
  ·
    refine ⟨433186440692500131249139307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288790960461666754166092871 433186440692500131249139307)
    ·
      refine ⟨649779661038750196873708961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433186440692500131249139307 649779661038750196873708961)
      ·
        refine ⟨487334745779062647655281721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649779661038750196873708961 487334745779062647655281721)
        ·
          refine ⟨365501059334296985741461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487334745779062647655281721 365501059334296985741461291)
          ·
            refine ⟨548251589001445478612191937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365501059334296985741461291 548251589001445478612191937)
            ·
              refine ⟨411188691751084108959143953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548251589001445478612191937 411188691751084108959143953)
              ·
                refine ⟨308391518813313081719357965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411188691751084108959143953 308391518813313081719357965)
                ·
                  refine ⟨115646819554992405644759237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308391518813313081719357965 115646819554992405644759237)
                  ·
                    refine ⟨21683778666561076058392357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115646819554992405644759237 21683778666561076058392357)
                    ·
                      refine ⟨4065708499980201760948567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21683778666561076058392357 4065708499980201760948567)
                      ·
                        rfl

theorem cell23_7917939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_7917939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917939 prefixEnd_7917939 := by exact prefixLift 7917939
  have htrace : WordTrace (prefixWord ++ tailWord_7917939) baseStart_7917939 baseEnd_7917939 := by
    simpa [prefixWord, tailWord_7917939, baseEnd_7917939] using wordTrace_append hprefix tailTrace_7917939
  have hstable : (prefixWord ++ tailWord_7917939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917939).length < 2 ^ (prefixWord ++ tailWord_7917939).sum := by decide
  have hdescent : baseEnd_7917939 < baseStart_7917939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917954 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7917954 : Nat := 118140960795 + 7917954 * 2 ^ 59
def prefixEnd_7917954 : Nat := 4983230072969 + 3 ^ 40 * 7917954 * 2
def baseEnd_7917954 : Nat := 4065716202190019202260999

theorem tailTrace_7917954 : CollatzResearch.WordTrace tailWord_7917954 prefixEnd_7917954 4065716202190019202260999 := by
  unfold tailWord_7917954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72197876889153102931972229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192527671704408274485259277 72197876889153102931972229)
  ·
    refine ⟨13537101916716206799744793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72197876889153102931972229 13537101916716206799744793)
    ·
      refine ⟨10152826437537155099808595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13537101916716206799744793 10152826437537155099808595)
      ·
        refine ⟨15229239656305732649712893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152826437537155099808595 15229239656305732649712893)
        ·
          refine ⟨5710964871114649743642335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15229239656305732649712893 5710964871114649743642335)
          ·
            refine ⟨8566447306671974615463503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710964871114649743642335 8566447306671974615463503)
            ·
              refine ⟨12849670960007961923195255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566447306671974615463503 12849670960007961923195255)
              ·
                refine ⟨19274506440011942884792883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849670960007961923195255 19274506440011942884792883)
                ·
                  refine ⟨28911759660017914327189325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19274506440011942884792883 28911759660017914327189325)
                  ·
                    refine ⟨10841909872506717872695997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28911759660017914327189325 10841909872506717872695997)
                    ·
                      refine ⟨4065716202190019202260999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10841909872506717872695997 4065716202190019202260999)
                      ·
                        rfl

theorem cell23_7917954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7917954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917954 prefixEnd_7917954 := by exact prefixLift 7917954
  have htrace : WordTrace (prefixWord ++ tailWord_7917954) baseStart_7917954 baseEnd_7917954 := by
    simpa [prefixWord, tailWord_7917954, baseEnd_7917954] using wordTrace_append hprefix tailTrace_7917954
  have hstable : (prefixWord ++ tailWord_7917954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917954).length < 2 ^ (prefixWord ++ tailWord_7917954).sum := by decide
  have hdescent : baseEnd_7917954 < baseStart_7917954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917956 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7917956 : Nat := 118140960795 + 7917956 * 2 ^ 59
def prefixEnd_7917956 : Nat := 4983230072969 + 3 ^ 40 * 7917956 * 2
def baseEnd_7917956 : Nat := 4065717229151328194435989

theorem tailTrace_7917956 : CollatzResearch.WordTrace tailWord_7917956 prefixEnd_7917956 4065717229151328194435989 := by
  unfold tailWord_7917956
  simp only [CollatzResearch.WordTrace]
  refine ⟨144395790251302583034730861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192527720335070110712974481 144395790251302583034730861)
  ·
    refine ⟨54148421344238468638024073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144395790251302583034730861 54148421344238468638024073)
    ·
      refine ⟨40611316008178851478518055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54148421344238468638024073 40611316008178851478518055)
      ·
        refine ⟨60916974012268277217777083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40611316008178851478518055 60916974012268277217777083)
        ·
          refine ⟨91375461018402415826665625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60916974012268277217777083 91375461018402415826665625)
          ·
            refine ⟨68531595763801811869999219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91375461018402415826665625 68531595763801811869999219)
            ·
              refine ⟨102797393645702717804998829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68531595763801811869999219 102797393645702717804998829)
              ·
                refine ⟨38549022617138519176874561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102797393645702717804998829 38549022617138519176874561)
                ·
                  refine ⟨28911766962853889382655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38549022617138519176874561 28911766962853889382655921)
                  ·
                    refine ⟨21683825222140417036991941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28911766962853889382655921 21683825222140417036991941)
                    ·
                      refine ⟨4065717229151328194435989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21683825222140417036991941 4065717229151328194435989)
                      ·
                        rfl

theorem cell23_7917956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7917956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917956 prefixEnd_7917956 := by exact prefixLift 7917956
  have htrace : WordTrace (prefixWord ++ tailWord_7917956) baseStart_7917956 baseEnd_7917956 := by
    simpa [prefixWord, tailWord_7917956, baseEnd_7917956] using wordTrace_append hprefix tailTrace_7917956
  have hstable : (prefixWord ++ tailWord_7917956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917956).length < 2 ^ (prefixWord ++ tailWord_7917956).sum := by decide
  have hdescent : baseEnd_7917956 < baseStart_7917956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7917999 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_7917999 : Nat := 118140960795 + 7917999 * 2 ^ 59
def prefixEnd_7917999 : Nat := 4983230072969 + 3 ^ 40 * 7917999 * 2
def baseEnd_7917999 : Nat := 4065739308819471526198291

theorem tailTrace_7917999 : CollatzResearch.WordTrace tailWord_7917999 prefixEnd_7917999 4065739308819471526198291 := by
  unfold tailWord_7917999
  simp only [CollatzResearch.WordTrace]
  refine ⟨288793148841449384413277051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192528765894299589608851367 288793148841449384413277051)
  ·
    refine ⟨433189723262174076619915577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288793148841449384413277051 433189723262174076619915577)
    ·
      refine ⟨324892292446630557464936683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433189723262174076619915577 324892292446630557464936683)
      ·
        refine ⟨487338438669945836197405025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324892292446630557464936683 487338438669945836197405025)
        ·
          refine ⟨365503829002459377148053769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487338438669945836197405025 365503829002459377148053769)
          ·
            refine ⟨274127871751844532861040327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365503829002459377148053769 274127871751844532861040327)
            ·
              refine ⟨411191807627766799291560491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274127871751844532861040327 411191807627766799291560491)
              ·
                refine ⟨616787711441650198937340737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411191807627766799291560491 616787711441650198937340737)
                ·
                  refine ⟨462590783581237649203005553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616787711441650198937340737 462590783581237649203005553)
                  ·
                    refine ⟨346943087685928236902254165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462590783581237649203005553 346943087685928236902254165)
                    ·
                      refine ⟨4065739308819471526198291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346943087685928236902254165 4065739308819471526198291)
                      ·
                        rfl

theorem cell23_7917999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_7917999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7917999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7917999 prefixEnd_7917999 := by exact prefixLift 7917999
  have htrace : WordTrace (prefixWord ++ tailWord_7917999) baseStart_7917999 baseEnd_7917999 := by
    simpa [prefixWord, tailWord_7917999, baseEnd_7917999] using wordTrace_append hprefix tailTrace_7917999
  have hstable : (prefixWord ++ tailWord_7917999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7917999).length < 2 ^ (prefixWord ++ tailWord_7917999).sum := by decide
  have hdescent : baseEnd_7917999 < baseStart_7917999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7917999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918016 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_7918016 : Nat := 118140960795 + 7918016 * 2 ^ 59
def prefixEnd_7918016 : Nat := 4983230072969 + 3 ^ 40 * 7918016 * 2
def baseEnd_7918016 : Nat := 4065748037990597959685713

theorem tailTrace_7918016 : CollatzResearch.WordTrace tailWord_7918016 prefixEnd_7918016 4065748037990597959685713 := by
  unfold tailWord_7918016
  simp only [CollatzResearch.WordTrace]
  refine ⟨144396884441193898158322951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192529179254925197544430601 144396884441193898158322951)
  ·
    refine ⟨216595326661790847237484427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144396884441193898158322951 216595326661790847237484427)
    ·
      refine ⟨324892989992686270856226641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216595326661790847237484427 324892989992686270856226641)
      ·
        refine ⟨243669742494514703142169981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324892989992686270856226641 243669742494514703142169981)
        ·
          refine ⟨91376153435443013678313743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243669742494514703142169981 91376153435443013678313743)
          ·
            refine ⟨137064230153164520517470615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91376153435443013678313743 137064230153164520517470615)
            ·
              refine ⟨205596345229746780776205923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137064230153164520517470615 205596345229746780776205923)
              ·
                refine ⟨308394517844620171164308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205596345229746780776205923 308394517844620171164308885)
                ·
                  refine ⟨14455993023966570523326979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 308394517844620171164308885 14455993023966570523326979)
                  ·
                    refine ⟨21683989535949855784990469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14455993023966570523326979 21683989535949855784990469)
                    ·
                      refine ⟨4065748037990597959685713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21683989535949855784990469 4065748037990597959685713)
                      ·
                        rfl

theorem cell23_7918016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_7918016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918016 prefixEnd_7918016 := by exact prefixLift 7918016
  have htrace : WordTrace (prefixWord ++ tailWord_7918016) baseStart_7918016 baseEnd_7918016 := by
    simpa [prefixWord, tailWord_7918016, baseEnd_7918016] using wordTrace_append hprefix tailTrace_7918016
  have hstable : (prefixWord ++ tailWord_7918016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918016).length < 2 ^ (prefixWord ++ tailWord_7918016).sum := by decide
  have hdescent : baseEnd_7918016 < baseStart_7918016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918060 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_7918060 : Nat := 118140960795 + 7918060 * 2 ^ 59
def prefixEnd_7918060 : Nat := 4983230072969 + 3 ^ 40 * 7918060 * 2
def baseEnd_7918060 : Nat := 1355256877046465262511837

theorem tailTrace_7918060 : CollatzResearch.WordTrace tailWord_7918060 prefixEnd_7918060 1355256877046465262511837 := by
  unfold tailWord_7918060
  simp only [CollatzResearch.WordTrace]
  refine ⟨144397686847114195915623817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192530249129485594554165089 144397686847114195915623817)
  ·
    refine ⟨108298265135335646936717863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144397686847114195915623817 108298265135335646936717863)
    ·
      refine ⟨162447397703003470405076795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108298265135335646936717863 162447397703003470405076795)
      ·
        refine ⟨243671096554505205607615193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162447397703003470405076795 243671096554505205607615193)
        ·
          refine ⟨182753322415878904205711395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243671096554505205607615193 182753322415878904205711395)
          ·
            refine ⟨274129983623818356308567093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182753322415878904205711395 274129983623818356308567093)
            ·
              refine ⟨25699685964732970903928165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274129983623818356308567093 25699685964732970903928165)
              ·
                refine ⟨4818691118387432044486531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25699685964732970903928165 4818691118387432044486531)
                ·
                  refine ⟨7228036677581148066729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818691118387432044486531 7228036677581148066729797)
                  ·
                    refine ⟨1355256877046465262511837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228036677581148066729797 1355256877046465262511837)
                    ·
                      rfl

theorem cell23_7918060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_7918060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918060 prefixEnd_7918060 := by exact prefixLift 7918060
  have htrace : WordTrace (prefixWord ++ tailWord_7918060) baseStart_7918060 baseEnd_7918060 := by
    simpa [prefixWord, tailWord_7918060, baseEnd_7918060] using wordTrace_append hprefix tailTrace_7918060
  have hstable : (prefixWord ++ tailWord_7918060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918060).length < 2 ^ (prefixWord ++ tailWord_7918060).sum := by decide
  have hdescent : baseEnd_7918060 < baseStart_7918060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918087 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7918087 : Nat := 118140960795 + 7918087 * 2 ^ 59
def prefixEnd_7918087 : Nat := 4983230072969 + 3 ^ 40 * 7918087 * 2
def baseEnd_7918087 : Nat := 4065784495117067181897887

theorem tailTrace_7918087 : CollatzResearch.WordTrace tailWord_7918087 prefixEnd_7918087 4065784495117067181897887 := by
  unfold tailWord_7918087
  simp only [CollatzResearch.WordTrace]
  refine ⟨288796358465130575442480515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192530905643420383628320343 288796358465130575442480515)
  ·
    refine ⟨433194537697695863163720773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288796358465130575442480515 433194537697695863163720773)
    ·
      refine ⟨81223975818317974343197645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 433194537697695863163720773 81223975818317974343197645)
      ·
        refine ⟨30458990931869240378699117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81223975818317974343197645 30458990931869240378699117)
        ·
          refine ⟨11422121599450965142012169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30458990931869240378699117 11422121599450965142012169)
          ·
            refine ⟨8566591199588223856509127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11422121599450965142012169 8566591199588223856509127)
            ·
              refine ⟨12849886799382335784763691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566591199588223856509127 12849886799382335784763691)
              ·
                refine ⟨19274830199073503677145537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849886799382335784763691 19274830199073503677145537)
                ·
                  refine ⟨14456122649305127757859153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19274830199073503677145537 14456122649305127757859153)
                  ·
                    refine ⟨10842091986978845818394365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14456122649305127757859153 10842091986978845818394365)
                    ·
                      refine ⟨4065784495117067181897887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842091986978845818394365 4065784495117067181897887)
                      ·
                        rfl

theorem cell23_7918087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7918087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918087 prefixEnd_7918087 := by exact prefixLift 7918087
  have htrace : WordTrace (prefixWord ++ tailWord_7918087) baseStart_7918087 baseEnd_7918087 := by
    simpa [prefixWord, tailWord_7918087, baseEnd_7918087] using wordTrace_append hprefix tailTrace_7918087
  have hstable : (prefixWord ++ tailWord_7918087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918087).length < 2 ^ (prefixWord ++ tailWord_7918087).sum := by decide
  have hdescent : baseEnd_7918087 < baseStart_7918087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918117 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_7918117 : Nat := 118140960795 + 7918117 * 2 ^ 59
def prefixEnd_7918117 : Nat := 4983230072969 + 3 ^ 40 * 7918117 * 2
def baseEnd_7918117 : Nat := 4065799899536702064522749

theorem tailTrace_7918117 : CollatzResearch.WordTrace tailWord_7918117 prefixEnd_7918117 4065799899536702064522749 := by
  unfold tailWord_7918117
  simp only [CollatzResearch.WordTrace]
  refine ⟨288797452655021890566072605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192531635103347927044048403 288797452655021890566072605)
  ·
    refine ⟨108299044745633208962277227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288797452655021890566072605 108299044745633208962277227)
    ·
      refine ⟨162448567118449813443415841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108299044745633208962277227 162448567118449813443415841)
      ·
        refine ⟨121836425338837360082561881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162448567118449813443415841 121836425338837360082561881)
        ·
          refine ⟨91377319004128020061921411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121836425338837360082561881 91377319004128020061921411)
          ·
            refine ⟨137065978506192030092882117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91377319004128020061921411 137065978506192030092882117)
            ·
              refine ⟨25699870969911005642415397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137065978506192030092882117 25699870969911005642415397)
              ·
                refine ⟨4818725806858313557952887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25699870969911005642415397 4818725806858313557952887)
                ·
                  refine ⟨7228088710287470336929331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818725806858313557952887 7228088710287470336929331)
                  ·
                    refine ⟨10842133065431205505393997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7228088710287470336929331 10842133065431205505393997)
                    ·
                      refine ⟨4065799899536702064522749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842133065431205505393997 4065799899536702064522749)
                      ·
                        rfl

theorem cell23_7918117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_7918117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918117 prefixEnd_7918117 := by exact prefixLift 7918117
  have htrace : WordTrace (prefixWord ++ tailWord_7918117) baseStart_7918117 baseEnd_7918117 := by
    simpa [prefixWord, tailWord_7918117, baseEnd_7918117] using wordTrace_append hprefix tailTrace_7918117
  have hstable : (prefixWord ++ tailWord_7918117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918117).length < 2 ^ (prefixWord ++ tailWord_7918117).sum := by decide
  have hdescent : baseEnd_7918117 < baseStart_7918117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918140 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_7918140 : Nat := 118140960795 + 7918140 * 2 ^ 59
def prefixEnd_7918140 : Nat := 4983230072969 + 3 ^ 40 * 7918140 * 2
def baseEnd_7918140 : Nat := 4065811709591755474535143

theorem tailTrace_7918140 : CollatzResearch.WordTrace tailWord_7918140 prefixEnd_7918140 4065811709591755474535143 := by
  unfold tailWord_7918140
  simp only [CollatzResearch.WordTrace]
  refine ⟨144399145766969282747079937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192532194355959043662773249 144399145766969282747079937)
  ·
    refine ⟨108299359325226962060309953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144399145766969282747079937 108299359325226962060309953)
    ·
      refine ⟨81224519493920221545232465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108299359325226962060309953 81224519493920221545232465)
      ·
        refine ⟨60918389620440166158924349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81224519493920221545232465 60918389620440166158924349)
        ·
          refine ⟨22844396107665062309596631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60918389620440166158924349 22844396107665062309596631)
          ·
            refine ⟨34266594161497593464394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22844396107665062309596631 34266594161497593464394947)
            ·
              refine ⟨51399891242246390196592421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34266594161497593464394947 51399891242246390196592421)
              ·
                refine ⟨9637479607921198161861079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51399891242246390196592421 9637479607921198161861079)
                ·
                  refine ⟨14456219411881797242791619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637479607921198161861079 14456219411881797242791619)
                  ·
                    refine ⟨21684329117822695864187429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14456219411881797242791619 21684329117822695864187429)
                    ·
                      refine ⟨4065811709591755474535143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21684329117822695864187429 4065811709591755474535143)
                      ·
                        rfl

theorem cell23_7918140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_7918140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918140 prefixEnd_7918140 := by exact prefixLift 7918140
  have htrace : WordTrace (prefixWord ++ tailWord_7918140) baseStart_7918140 baseEnd_7918140 := by
    simpa [prefixWord, tailWord_7918140, baseEnd_7918140] using wordTrace_append hprefix tailTrace_7918140
  have hstable : (prefixWord ++ tailWord_7918140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918140).length < 2 ^ (prefixWord ++ tailWord_7918140).sum := by decide
  have hdescent : baseEnd_7918140 < baseStart_7918140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918157 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_7918157 : Nat := 118140960795 + 7918157 * 2 ^ 59
def prefixEnd_7918157 : Nat := 4983230072969 + 3 ^ 40 * 7918157 * 2
def baseEnd_7918157 : Nat := 4065820438762881908022565

theorem tailTrace_7918157 : CollatzResearch.WordTrace tailWord_7918157 prefixEnd_7918157 4065820438762881908022565 := by
  unfold tailWord_7918157
  simp only [CollatzResearch.WordTrace]
  refine ⟨288798911574876977397528725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192532607716584651598352483 288798911574876977397528725)
  ·
    refine ⟨13537448980072358315509159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288798911574876977397528725 13537448980072358315509159)
    ·
      refine ⟨20306173470108537473263739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13537448980072358315509159 20306173470108537473263739)
      ·
        refine ⟨30459260205162806209895609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20306173470108537473263739 30459260205162806209895609)
        ·
          refine ⟨22844445153872104657421707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30459260205162806209895609 22844445153872104657421707)
          ·
            refine ⟨34266667730808156986132561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22844445153872104657421707 34266667730808156986132561)
            ·
              refine ⟨25700000798106117739599421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34266667730808156986132561 25700000798106117739599421)
              ·
                refine ⟨9637500299289794152349783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25700000798106117739599421 9637500299289794152349783)
                ·
                  refine ⟨14456250448934691228524675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637500299289794152349783 14456250448934691228524675)
                  ·
                    refine ⟨21684375673402036842787013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14456250448934691228524675 21684375673402036842787013)
                    ·
                      refine ⟨4065820438762881908022565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21684375673402036842787013 4065820438762881908022565)
                      ·
                        rfl

theorem cell23_7918157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_7918157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918157 prefixEnd_7918157 := by exact prefixLift 7918157
  have htrace : WordTrace (prefixWord ++ tailWord_7918157) baseStart_7918157 baseEnd_7918157 := by
    simpa [prefixWord, tailWord_7918157, baseEnd_7918157] using wordTrace_append hprefix tailTrace_7918157
  have hstable : (prefixWord ++ tailWord_7918157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918157).length < 2 ^ (prefixWord ++ tailWord_7918157).sum := by decide
  have hdescent : baseEnd_7918157 < baseStart_7918157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918194 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_7918194 : Nat := 118140960795 + 7918194 * 2 ^ 59
def prefixEnd_7918194 : Nat := 4983230072969 + 3 ^ 40 * 7918194 * 2
def baseEnd_7918194 : Nat := 4065839437547098263259895

theorem tailTrace_7918194 : CollatzResearch.WordTrace tailWord_7918194 prefixEnd_7918194 4065839437547098263259895 := by
  unfold tailWord_7918194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72200065268935733179156409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192533507383828621811083757 72200065268935733179156409)
  ·
    refine ⟨54150048951701799884367307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72200065268935733179156409 54150048951701799884367307)
    ·
      refine ⟨81225073427552699826550961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54150048951701799884367307 81225073427552699826550961)
      ·
        refine ⟨60918805070664524869913221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81225073427552699826550961 60918805070664524869913221)
        ·
          refine ⟨11422275950749598413108729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60918805070664524869913221 11422275950749598413108729)
          ·
            refine ⟨8566706963062198809831547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11422275950749598413108729 8566706963062198809831547)
            ·
              refine ⟨12850060444593298214747321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566706963062198809831547 12850060444593298214747321)
              ·
                refine ⟨9637545333444973661060491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12850060444593298214747321 9637545333444973661060491)
                ·
                  refine ⟨14456318000167460491590737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9637545333444973661060491 14456318000167460491590737)
                  ·
                    refine ⟨10842238500125595368693053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14456318000167460491590737 10842238500125595368693053)
                    ·
                      refine ⟨4065839437547098263259895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10842238500125595368693053 4065839437547098263259895)
                      ·
                        rfl

theorem cell23_7918194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_7918194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918194 prefixEnd_7918194 := by exact prefixLift 7918194
  have htrace : WordTrace (prefixWord ++ tailWord_7918194) baseStart_7918194 baseEnd_7918194 := by
    simpa [prefixWord, tailWord_7918194, baseEnd_7918194] using wordTrace_append hprefix tailTrace_7918194
  have hstable : (prefixWord ++ tailWord_7918194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918194).length < 2 ^ (prefixWord ++ tailWord_7918194).sum := by decide
  have hdescent : baseEnd_7918194 < baseStart_7918194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7918200 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2]
def baseStart_7918200 : Nat := 118140960795 + 7918200 * 2 ^ 59
def prefixEnd_7918200 : Nat := 4983230072969 + 3 ^ 40 * 7918200 * 2
def baseEnd_7918200 : Nat := 4065842518431025239784867

theorem tailTrace_7918200 : CollatzResearch.WordTrace tailWord_7918200 prefixEnd_7918200 4065842518431025239784867 := by
  unfold tailWord_7918200
  simp only [CollatzResearch.WordTrace]
  refine ⟨144400239956860597870672027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192533653275814130494229369 144400239956860597870672027)
  ·
    refine ⟨216600359935290896806008041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144400239956860597870672027 216600359935290896806008041)
    ·
      refine ⟨162450269951468172604506031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216600359935290896806008041 162450269951468172604506031)
      ·
        refine ⟨243675404927202258906759047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162450269951468172604506031 243675404927202258906759047)
        ·
          refine ⟨365513107390803388360138571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243675404927202258906759047 365513107390803388360138571)
          ·
            refine ⟨548269661086205082540207857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365513107390803388360138571 548269661086205082540207857)
            ·
              refine ⟨411202245814653811905155893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548269661086205082540207857 411202245814653811905155893)
              ·
                refine ⟨38550210545123794866108365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411202245814653811905155893 38550210545123794866108365)
                ·
                  refine ⟨14456328954421423074790637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38550210545123794866108365 14456328954421423074790637)
                  ·
                    refine ⟨5421123357908033653046489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14456328954421423074790637 5421123357908033653046489)
                    ·
                      refine ⟨4065842518431025239784867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5421123357908033653046489 4065842518431025239784867)
                      ·
                        rfl

theorem cell23_7918200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_7918200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7918200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7918200 prefixEnd_7918200 := by exact prefixLift 7918200
  have htrace : WordTrace (prefixWord ++ tailWord_7918200) baseStart_7918200 baseEnd_7918200 := by
    simpa [prefixWord, tailWord_7918200, baseEnd_7918200] using wordTrace_append hprefix tailTrace_7918200
  have hstable : (prefixWord ++ tailWord_7918200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7918200).length < 2 ^ (prefixWord ++ tailWord_7918200).sum := by decide
  have hdescent : baseEnd_7918200 < baseStart_7918200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7918200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
