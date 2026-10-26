import V185TrunkScan23Chunk0443

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2624813 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2624813 : Nat := 118140960795 + 2624813 * 2 ^ 59
def prefixEnd_2624813 : Nat := 4983230072969 + 3 ^ 40 * 2624813 * 2
def baseEnd_2624813 : Nat := 449263565723314713588737

theorem tailTrace_2624813 : CollatzResearch.WordTrace tailWord_2624813 prefixEnd_2624813 449263565723314713588737 := by
  unfold tailWord_2624813
  simp only [CollatzResearch.WordTrace]
  refine ⟨95734795039758258215927093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63823196693172172143951395 95734795039758258215927093)
  ·
    refine ⟨8975137034977336707743165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95734795039758258215927093 8975137034977336707743165)
    ·
      refine ⟨3365676388116501265403687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8975137034977336707743165 3365676388116501265403687)
      ·
        refine ⟨5048514582174751898105531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365676388116501265403687 5048514582174751898105531)
        ·
          refine ⟨7572771873262127847158297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048514582174751898105531 7572771873262127847158297)
          ·
            refine ⟨5679578904946595885368723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7572771873262127847158297 5679578904946595885368723)
            ·
              refine ⟨8519368357419893828053085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679578904946595885368723 8519368357419893828053085)
              ·
                refine ⟨3194763134032460185519907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519368357419893828053085 3194763134032460185519907)
                ·
                  refine ⟨4792144701048690278279861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194763134032460185519907 4792144701048690278279861)
                  ·
                    refine ⟨449263565723314713588737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4792144701048690278279861 449263565723314713588737)
                    ·
                      rfl

theorem cell23_2624813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2624813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624813 prefixEnd_2624813 := by exact prefixLift 2624813
  have htrace : WordTrace (prefixWord ++ tailWord_2624813) baseStart_2624813 baseEnd_2624813 := by
    simpa [prefixWord, tailWord_2624813, baseEnd_2624813] using wordTrace_append hprefix tailTrace_2624813
  have hstable : (prefixWord ++ tailWord_2624813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624813).length < 2 ^ (prefixWord ++ tailWord_2624813).sum := by decide
  have hdescent : baseEnd_2624813 < baseStart_2624813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624816 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2]
def baseStart_2624816 : Nat := 118140960795 + 2624816 * 2 ^ 59
def prefixEnd_2624816 : Nat := 4983230072969 + 3 ^ 40 * 2624816 * 2
def baseEnd_2624816 : Nat := 1347792237611907629028697

theorem tailTrace_2624816 : CollatzResearch.WordTrace tailWord_2624816 prefixEnd_2624816 1347792237611907629028697 := by
  unfold tailWord_2624816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867452229373694864143151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63823269639164926485524201 47867452229373694864143151)
  ·
    refine ⟨71801178344060542296214727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47867452229373694864143151 71801178344060542296214727)
    ·
      refine ⟨107701767516090813444322091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71801178344060542296214727 107701767516090813444322091)
      ·
        refine ⟨161552651274136220166483137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107701767516090813444322091 161552651274136220166483137)
        ·
          refine ⟨121164488455602165124862353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161552651274136220166483137 121164488455602165124862353)
          ·
            refine ⟨90873366341701623843646765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121164488455602165124862353 90873366341701623843646765)
            ·
              refine ⟨34077512378138108941367537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90873366341701623843646765 34077512378138108941367537)
              ·
                refine ⟨25558134283603581706025653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34077512378138108941367537 25558134283603581706025653)
                ·
                  refine ⟨2396075089087835784939905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25558134283603581706025653 2396075089087835784939905)
                  ·
                    refine ⟨1797056316815876838704929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396075089087835784939905 1797056316815876838704929)
                    ·
                      refine ⟨1347792237611907629028697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797056316815876838704929 1347792237611907629028697)
                      ·
                        rfl

theorem cell23_2624816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2].length) (baseStart_2624816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624816 prefixEnd_2624816 := by exact prefixLift 2624816
  have htrace : WordTrace (prefixWord ++ tailWord_2624816) baseStart_2624816 baseEnd_2624816 := by
    simpa [prefixWord, tailWord_2624816, baseEnd_2624816] using wordTrace_append hprefix tailTrace_2624816
  have hstable : (prefixWord ++ tailWord_2624816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624816).length < 2 ^ (prefixWord ++ tailWord_2624816).sum := by decide
  have hdescent : baseEnd_2624816 < baseStart_2624816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624836 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2624836 : Nat := 118140960795 + 2624836 * 2 ^ 59
def prefixEnd_2624836 : Nat := 4983230072969 + 3 ^ 40 * 2624836 * 2
def baseEnd_2624836 : Nat := 1347802507224997550778605

theorem tailTrace_2624836 : CollatzResearch.WordTrace tailWord_2624836 prefixEnd_2624836 1347802507224997550778605 := by
  unfold tailWord_2624836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867816959337466572007181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63823755945783288762676241 47867816959337466572007181)
  ·
    refine ⟨17950431359751549964502693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47867816959337466572007181 17950431359751549964502693)
    ·
      refine ⟨3365705879953415618344255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17950431359751549964502693 3365705879953415618344255)
      ·
        refine ⟨5048558819930123427516383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365705879953415618344255 5048558819930123427516383)
        ·
          refine ⟨7572838229895185141274575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048558819930123427516383 7572838229895185141274575)
          ·
            refine ⟨11359257344842777711911863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572838229895185141274575 11359257344842777711911863)
            ·
              refine ⟨17038886017264166567867795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359257344842777711911863 17038886017264166567867795)
              ·
                refine ⟨25558329025896249851801693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17038886017264166567867795 25558329025896249851801693)
                ·
                  refine ⟨9584373384711093694425635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25558329025896249851801693 9584373384711093694425635)
                  ·
                    refine ⟨14376560077066640541638453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9584373384711093694425635 14376560077066640541638453)
                    ·
                      refine ⟨1347802507224997550778605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14376560077066640541638453 1347802507224997550778605)
                      ·
                        rfl

theorem cell23_2624836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2624836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624836 prefixEnd_2624836 := by exact prefixLift 2624836
  have htrace : WordTrace (prefixWord ++ tailWord_2624836) baseStart_2624836 baseEnd_2624836 := by
    simpa [prefixWord, tailWord_2624836, baseEnd_2624836] using wordTrace_append hprefix tailTrace_2624836
  have hstable : (prefixWord ++ tailWord_2624836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624836).length < 2 ^ (prefixWord ++ tailWord_2624836).sum := by decide
  have hdescent : baseEnd_2624836 < baseStart_2624836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624853 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2624853 : Nat := 118140960795 + 2624853 * 2 ^ 59
def prefixEnd_2624853 : Nat := 4983230072969 + 3 ^ 40 * 2624853 * 2
def baseEnd_2624853 : Nat := 1347811236396123984266027

theorem tailTrace_2624853 : CollatzResearch.WordTrace tailWord_2624853 prefixEnd_2624853 1347811236396123984266027 := by
  unfold tailWord_2624853
  simp only [CollatzResearch.WordTrace]
  refine ⟨95736253959613345047383213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63824169306408896698255475 95736253959613345047383213)
  ·
    refine ⟨35901095234855004392768705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95736253959613345047383213 35901095234855004392768705)
    ·
      refine ⟨26925821426141253294576529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35901095234855004392768705 26925821426141253294576529)
      ·
        refine ⟨20194366069605939970932397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26925821426141253294576529 20194366069605939970932397)
        ·
          refine ⟨7572887276102227489099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20194366069605939970932397 7572887276102227489099649)
          ·
            refine ⟨5679665457076670616824737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7572887276102227489099649 5679665457076670616824737)
            ·
              refine ⟨4259749092807502962618553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679665457076670616824737 4259749092807502962618553)
              ·
                refine ⟨3194811819605627221963915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259749092807502962618553 3194811819605627221963915)
                ·
                  refine ⟨4792217729408440832945873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194811819605627221963915 4792217729408440832945873)
                  ·
                    refine ⟨3594163297056330624709405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792217729408440832945873 3594163297056330624709405)
                    ·
                      refine ⟨1347811236396123984266027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594163297056330624709405 1347811236396123984266027)
                      ·
                        rfl

theorem cell23_2624853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2624853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624853 prefixEnd_2624853 := by exact prefixLift 2624853
  have htrace : WordTrace (prefixWord ++ tailWord_2624853) baseStart_2624853 baseEnd_2624853 := by
    simpa [prefixWord, tailWord_2624853, baseEnd_2624853] using wordTrace_append hprefix tailTrace_2624853
  have hstable : (prefixWord ++ tailWord_2624853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624853).length < 2 ^ (prefixWord ++ tailWord_2624853).sum := by decide
  have hdescent : baseEnd_2624853 < baseStart_2624853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624861 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2624861 : Nat := 118140960795 + 2624861 * 2 ^ 59
def prefixEnd_2624861 : Nat := 4983230072969 + 3 ^ 40 * 2624861 * 2
def baseEnd_2624861 : Nat := 1347815344241359952965991

theorem tailTrace_2624861 : CollatzResearch.WordTrace tailWord_2624861 prefixEnd_2624861 1347815344241359952965991 := by
  unfold tailWord_2624861
  simp only [CollatzResearch.WordTrace]
  refine ⟨95736545743584362413674437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63824363829056241609116291 95736545743584362413674437)
  ·
    refine ⟨17950602326922067952563957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95736545743584362413674437 17950602326922067952563957)
    ·
      refine ⟨1682868968148943870552871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17950602326922067952563957 1682868968148943870552871)
      ·
        refine ⟨2524303452223415805829307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682868968148943870552871 2524303452223415805829307)
        ·
          refine ⟨3786455178335123708743961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524303452223415805829307 3786455178335123708743961)
          ·
            refine ⟨2839841383751342781557971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786455178335123708743961 2839841383751342781557971)
            ·
              refine ⟨4259762075627014172336957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839841383751342781557971 4259762075627014172336957)
              ·
                refine ⟨1597410778360130314626359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259762075627014172336957 1597410778360130314626359)
                ·
                  refine ⟨2396116167540195471939539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597410778360130314626359 2396116167540195471939539)
                  ·
                    refine ⟨3594174251310293207909309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396116167540195471939539 3594174251310293207909309)
                    ·
                      refine ⟨1347815344241359952965991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594174251310293207909309 1347815344241359952965991)
                      ·
                        rfl

theorem cell23_2624861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2624861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624861 prefixEnd_2624861 := by exact prefixLift 2624861
  have htrace : WordTrace (prefixWord ++ tailWord_2624861) baseStart_2624861 baseEnd_2624861 := by
    simpa [prefixWord, tailWord_2624861, baseEnd_2624861] using wordTrace_append hprefix tailTrace_2624861
  have hstable : (prefixWord ++ tailWord_2624861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624861).length < 2 ^ (prefixWord ++ tailWord_2624861).sum := by decide
  have hdescent : baseEnd_2624861 < baseStart_2624861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624866 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2624866 : Nat := 118140960795 + 2624866 * 2 ^ 59
def prefixEnd_2624866 : Nat := 4983230072969 + 3 ^ 40 * 2624866 * 2
def baseEnd_2624866 : Nat := 1347817911644632433403467

theorem tailTrace_2624866 : CollatzResearch.WordTrace tailWord_2624866 prefixEnd_2624866 1347817911644632433403467 := by
  unfold tailWord_2624866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23934182027141562066901613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63824485405710832178404301 23934182027141562066901613)
  ·
    refine ⟨8975318260178085775088105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23934182027141562066901613 8975318260178085775088105)
    ·
      refine ⟨6731488695133564331316079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8975318260178085775088105 6731488695133564331316079)
      ·
        refine ⟨10097233042700346496974119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731488695133564331316079 10097233042700346496974119)
        ·
          refine ⟨15145849564050519745461179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10097233042700346496974119 15145849564050519745461179)
          ·
            refine ⟨22718774346075779618191769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15145849564050519745461179 22718774346075779618191769)
            ·
              refine ⟨17039080759556834713643827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22718774346075779618191769 17039080759556834713643827)
              ·
                refine ⟨25558621139335252070465741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17039080759556834713643827 25558621139335252070465741)
                ·
                  refine ⟨9584482927250719526424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25558621139335252070465741 9584482927250719526424653)
                  ·
                    refine ⟨3594181097719019822409245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9584482927250719526424653 3594181097719019822409245)
                    ·
                      refine ⟨1347817911644632433403467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594181097719019822409245 1347817911644632433403467)
                      ·
                        rfl

theorem cell23_2624866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2624866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624866 prefixEnd_2624866 := by exact prefixLift 2624866
  have htrace : WordTrace (prefixWord ++ tailWord_2624866) baseStart_2624866 baseEnd_2624866 := by
    simpa [prefixWord, tailWord_2624866, baseEnd_2624866] using wordTrace_append hprefix tailTrace_2624866
  have hstable : (prefixWord ++ tailWord_2624866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624866).length < 2 ^ (prefixWord ++ tailWord_2624866).sum := by decide
  have hdescent : baseEnd_2624866 < baseStart_2624866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624867 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2624867 : Nat := 118140960795 + 2624867 * 2 ^ 59
def prefixEnd_2624867 : Nat := 4983230072969 + 3 ^ 40 * 2624867 * 2
def baseEnd_2624867 : Nat := 1347818425125286929490963

theorem tailTrace_2624867 : CollatzResearch.WordTrace tailWord_2624867 prefixEnd_2624867 1347818425125286929490963 := by
  unfold tailWord_2624867
  simp only [CollatzResearch.WordTrace]
  refine ⟨95736764581562625438392855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63824509721041750292261903 95736764581562625438392855)
  ·
    refine ⟨143605146872343938157589283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95736764581562625438392855 143605146872343938157589283)
    ·
      refine ⟨215407720308515907236383925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143605146872343938157589283 215407720308515907236383925)
      ·
        refine ⟨20194473778923366303410993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215407720308515907236383925 20194473778923366303410993)
        ·
          refine ⟨15145855334192524727558245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20194473778923366303410993 15145855334192524727558245)
          ·
            refine ⟨2839847875161098386417171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15145855334192524727558245 2839847875161098386417171)
            ·
              refine ⟨4259771812741647579625757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839847875161098386417171 4259771812741647579625757)
              ·
                refine ⟨1597414429778117842359659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259771812741647579625757 1597414429778117842359659)
                ·
                  refine ⟨2396121644667176763539489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597414429778117842359659 2396121644667176763539489)
                  ·
                    refine ⟨1797091233500382572654617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396121644667176763539489 1797091233500382572654617)
                    ·
                      refine ⟨1347818425125286929490963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797091233500382572654617 1347818425125286929490963)
                      ·
                        rfl

theorem cell23_2624867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2624867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624867 prefixEnd_2624867 := by exact prefixLift 2624867
  have htrace : WordTrace (prefixWord ++ tailWord_2624867) baseStart_2624867 baseEnd_2624867 := by
    simpa [prefixWord, tailWord_2624867, baseEnd_2624867] using wordTrace_append hprefix tailTrace_2624867
  have hstable : (prefixWord ++ tailWord_2624867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624867).length < 2 ^ (prefixWord ++ tailWord_2624867).sum := by decide
  have hdescent : baseEnd_2624867 < baseStart_2624867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624894 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2624894 : Nat := 118140960795 + 2624894 * 2 ^ 59
def prefixEnd_2624894 : Nat := 4983230072969 + 3 ^ 40 * 2624894 * 2
def baseEnd_2624894 : Nat := 449277429700986107951113

theorem tailTrace_2624894 : CollatzResearch.WordTrace tailWord_2624894 prefixEnd_2624894 449277429700986107951113 := by
  unfold tailWord_2624894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967218669058101131203217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63825166234976539366417157 11967218669058101131203217)
  ·
    refine ⟨8975414001793575848402413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11967218669058101131203217 8975414001793575848402413)
    ·
      refine ⟨3365780250672590943150905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8975414001793575848402413 3365780250672590943150905)
      ·
        refine ⟨2524335188004443207363179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365780250672590943150905 2524335188004443207363179)
        ·
          refine ⟨3786502782006664811044769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524335188004443207363179 3786502782006664811044769)
          ·
            refine ⟨2839877086504998608283577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786502782006664811044769 2839877086504998608283577)
            ·
              refine ⟨2129907814878748956212683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839877086504998608283577 2129907814878748956212683)
              ·
                refine ⟨3194861722318123434319025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129907814878748956212683 3194861722318123434319025)
                ·
                  refine ⟨2396146291738592575739269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194861722318123434319025 2396146291738592575739269)
                  ·
                    refine ⟨449277429700986107951113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396146291738592575739269 449277429700986107951113)
                    ·
                      rfl

theorem cell23_2624894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2624894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624894 prefixEnd_2624894 := by exact prefixLift 2624894
  have htrace : WordTrace (prefixWord ++ tailWord_2624894) baseStart_2624894 baseEnd_2624894 := by
    simpa [prefixWord, tailWord_2624894, baseEnd_2624894] using wordTrace_append hprefix tailTrace_2624894
  have hstable : (prefixWord ++ tailWord_2624894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624894).length < 2 ^ (prefixWord ++ tailWord_2624894).sum := by decide
  have hdescent : baseEnd_2624894 < baseStart_2624894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624900 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2624900 : Nat := 118140960795 + 2624900 * 2 ^ 59
def prefixEnd_2624900 : Nat := 4983230072969 + 3 ^ 40 * 2624900 * 2
def baseEnd_2624900 : Nat := 1347835369986885300378311

theorem tailTrace_2624900 : CollatzResearch.WordTrace tailWord_2624900 prefixEnd_2624900 1347835369986885300378311 := by
  unfold tailWord_2624900
  simp only [CollatzResearch.WordTrace]
  refine ⟨47868984095221536037172077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63825312126962048049562769 47868984095221536037172077)
  ·
    refine ⟨17950869035708076013939529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47868984095221536037172077 17950869035708076013939529)
    ·
      refine ⟨13463151776781057010454647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17950869035708076013939529 13463151776781057010454647)
      ·
        refine ⟨20194727665171585515681971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13463151776781057010454647 20194727665171585515681971)
        ·
          refine ⟨30292091497757378273522957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194727665171585515681971 30292091497757378273522957)
          ·
            refine ⟨11359534311659016852571109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30292091497757378273522957 11359534311659016852571109)
            ·
              refine ⟨2129912683436065659857083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11359534311659016852571109 2129912683436065659857083)
              ·
                refine ⟨3194869025154098489785625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129912683436065659857083 3194869025154098489785625)
                ·
                  refine ⟨2396151768865573867339219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194869025154098489785625 2396151768865573867339219)
                  ·
                    refine ⟨3594227653298360801008829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396151768865573867339219 3594227653298360801008829)
                    ·
                      refine ⟨1347835369986885300378311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594227653298360801008829 1347835369986885300378311)
                      ·
                        rfl

theorem cell23_2624900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2624900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624900 prefixEnd_2624900 := by exact prefixLift 2624900
  have htrace : WordTrace (prefixWord ++ tailWord_2624900) baseStart_2624900 baseEnd_2624900 := by
    simpa [prefixWord, tailWord_2624900, baseEnd_2624900] using wordTrace_append hprefix tailTrace_2624900
  have hstable : (prefixWord ++ tailWord_2624900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624900).length < 2 ^ (prefixWord ++ tailWord_2624900).sum := by decide
  have hdescent : baseEnd_2624900 < baseStart_2624900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624910 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2624910 : Nat := 118140960795 + 2624910 * 2 ^ 59
def prefixEnd_2624910 : Nat := 4983230072969 + 3 ^ 40 * 2624910 * 2
def baseEnd_2624910 : Nat := 1347840504793430261253265

theorem tailTrace_2624910 : CollatzResearch.WordTrace tailWord_2624910 prefixEnd_2624910 1347840504793430261253265 := by
  unfold tailWord_2624910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967291615050855472776023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63825555280271229188138789 11967291615050855472776023)
  ·
    refine ⟨17950937422576283209164035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11967291615050855472776023 17950937422576283209164035)
    ·
      refine ⟨26926406133864424813746053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17950937422576283209164035 26926406133864424813746053)
      ·
        refine ⟨5048701150099579652577385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26926406133864424813746053 5048701150099579652577385)
        ·
          refine ⟨3786525862574684739433039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5048701150099579652577385 3786525862574684739433039)
          ·
            refine ⟨5679788793862027109149559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786525862574684739433039 5679788793862027109149559)
            ·
              refine ⟨8519683190793040663724339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679788793862027109149559 8519683190793040663724339)
              ·
                refine ⟨12779524786189560995586509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8519683190793040663724339 12779524786189560995586509)
                ·
                  refine ⟨4792321794821085373344941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12779524786189560995586509 4792321794821085373344941)
                  ·
                    refine ⟨1797120673057907015004353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4792321794821085373344941 1797120673057907015004353)
                    ·
                      refine ⟨1347840504793430261253265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797120673057907015004353 1347840504793430261253265)
                      ·
                        rfl

theorem cell23_2624910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2624910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624910 prefixEnd_2624910 := by exact prefixLift 2624910
  have htrace : WordTrace (prefixWord ++ tailWord_2624910) baseStart_2624910 baseEnd_2624910 := by
    simpa [prefixWord, tailWord_2624910, baseEnd_2624910] using wordTrace_append hprefix tailTrace_2624910
  have hstable : (prefixWord ++ tailWord_2624910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624910).length < 2 ^ (prefixWord ++ tailWord_2624910).sum := by decide
  have hdescent : baseEnd_2624910 < baseStart_2624910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624919 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2624919 : Nat := 118140960795 + 2624919 * 2 ^ 59
def prefixEnd_2624919 : Nat := 4983230072969 + 3 ^ 40 * 2624919 * 2
def baseEnd_2624919 : Nat := 1347845126119320726040723

theorem tailTrace_2624919 : CollatzResearch.WordTrace tailWord_2624919 prefixEnd_2624919 1347845126119320726040723 := by
  unfold tailWord_2624919
  simp only [CollatzResearch.WordTrace]
  refine ⟨95738661177374238319285811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63825774118249492212857207 95738661177374238319285811)
  ·
    refine ⟨143607991766061357478928717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95738661177374238319285811 143607991766061357478928717)
    ·
      refine ⟨53852996912273009054598269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143607991766061357478928717 53852996912273009054598269)
      ·
        refine ⟨20194873842102378395474351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53852996912273009054598269 20194873842102378395474351)
        ·
          refine ⟨30292310763153567593211527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20194873842102378395474351 30292310763153567593211527)
          ·
            refine ⟨45438466144730351389817291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30292310763153567593211527 45438466144730351389817291)
            ·
              refine ⟨68157699217095527084725937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45438466144730351389817291 68157699217095527084725937)
              ·
                refine ⟨51118274412821645313544453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68157699217095527084725937 51118274412821645313544453)
                ·
                  refine ⟨9584676452404058496289585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51118274412821645313544453 9584676452404058496289585)
                  ·
                    refine ⟨7188507339303043872217189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9584676452404058496289585 7188507339303043872217189)
                    ·
                      refine ⟨1347845126119320726040723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7188507339303043872217189 1347845126119320726040723)
                      ·
                        rfl

theorem cell23_2624919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2624919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624919 prefixEnd_2624919 := by exact prefixLift 2624919
  have htrace : WordTrace (prefixWord ++ tailWord_2624919) baseStart_2624919 baseEnd_2624919 := by
    simpa [prefixWord, tailWord_2624919, baseEnd_2624919] using wordTrace_append hprefix tailTrace_2624919
  have hstable : (prefixWord ++ tailWord_2624919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624919).length < 2 ^ (prefixWord ++ tailWord_2624919).sum := by decide
  have hdescent : baseEnd_2624919 < baseStart_2624919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624959 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 4, 5]
def baseStart_2624959 : Nat := 118140960795 + 2624959 * 2 ^ 59
def prefixEnd_2624959 : Nat := 4983230072969 + 3 ^ 40 * 2624959 * 2
def baseEnd_2624959 : Nat := 449288555115166856513513

theorem tailTrace_2624959 : CollatzResearch.WordTrace tailWord_2624959 prefixEnd_2624959 449288555115166856513513 := by
  unfold tailWord_2624959
  simp only [CollatzResearch.WordTrace]
  refine ⟨95740120097229325150741931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63826746731486216767161287 95740120097229325150741931)
  ·
    refine ⟨143610180145843987726112897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95740120097229325150741931 143610180145843987726112897)
    ·
      refine ⟨107707635109382990794584673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143610180145843987726112897 107707635109382990794584673)
      ·
        refine ⟨80780726332037243095938505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107707635109382990794584673 80780726332037243095938505)
        ·
          refine ⟨60585544749027932321953879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80780726332037243095938505 60585544749027932321953879)
          ·
            refine ⟨90878317123541898482930819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60585544749027932321953879 90878317123541898482930819)
            ·
              refine ⟨136317475685312847724396229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90878317123541898482930819 136317475685312847724396229)
              ·
                refine ⟨25559526690996158948324293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136317475685312847724396229 25559526690996158948324293)
                ·
                  refine ⟨4792411254561779802810805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25559526690996158948324293 4792411254561779802810805)
                  ·
                    refine ⟨449288555115166856513513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4792411254561779802810805 449288555115166856513513)
                    ·
                      rfl

theorem cell23_2624959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_2624959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624959 prefixEnd_2624959 := by exact prefixLift 2624959
  have htrace : WordTrace (prefixWord ++ tailWord_2624959) baseStart_2624959 baseEnd_2624959 := by
    simpa [prefixWord, tailWord_2624959, baseEnd_2624959] using wordTrace_append hprefix tailTrace_2624959
  have hstable : (prefixWord ++ tailWord_2624959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624959).length < 2 ^ (prefixWord ++ tailWord_2624959).sum := by decide
  have hdescent : baseEnd_2624959 < baseStart_2624959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624980 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 5]
def baseStart_2624980 : Nat := 118140960795 + 2624980 * 2 ^ 59
def prefixEnd_2624980 : Nat := 4983230072969 + 3 ^ 40 * 2624980 * 2
def baseEnd_2624980 : Nat := 149764049826582776375327

theorem tailTrace_2624980 : CollatzResearch.WordTrace tailWord_2624980 prefixEnd_2624980 149764049826582776375327 := by
  unfold tailWord_2624980
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870443015076622868628197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63827257353435497158170929 47870443015076622868628197)
  ·
    refine ⟨8975708065326866787867787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47870443015076622868628197 8975708065326866787867787)
    ·
      refine ⟨13463562097990300181801681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8975708065326866787867787 13463562097990300181801681)
      ·
        refine ⟨10097671573492725136351261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13463562097990300181801681 10097671573492725136351261)
        ·
          refine ⟨3786626840059771926131723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10097671573492725136351261 3786626840059771926131723)
          ·
            refine ⟨5679940260089657889197585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786626840059771926131723 5679940260089657889197585)
            ·
              refine ⟨4259955195067243416898189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679940260089657889197585 4259955195067243416898189)
              ·
                refine ⟨1597483198150216281336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259955195067243416898189 1597483198150216281336821)
                ·
                  refine ⟨149764049826582776375327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1597483198150216281336821 149764049826582776375327)
                  ·
                    rfl

theorem cell23_2624980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_2624980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624980 prefixEnd_2624980 := by exact prefixLift 2624980
  have htrace : WordTrace (prefixWord ++ tailWord_2624980) baseStart_2624980 baseEnd_2624980 := by
    simpa [prefixWord, tailWord_2624980, baseEnd_2624980] using wordTrace_append hprefix tailTrace_2624980
  have hstable : (prefixWord ++ tailWord_2624980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624980).length < 2 ^ (prefixWord ++ tailWord_2624980).sum := by decide
  have hdescent : baseEnd_2624980 < baseStart_2624980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624996 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_2624996 : Nat := 118140960795 + 2624996 * 2 ^ 59
def prefixEnd_2624996 : Nat := 4983230072969 + 3 ^ 40 * 2624996 * 2
def baseEnd_2624996 : Nat := 1347884664129716924777869

theorem tailTrace_2624996 : CollatzResearch.WordTrace tailWord_2624996 prefixEnd_2624996 1347884664129716924777869 := by
  unfold tailWord_2624996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47870734799047640234919421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63827646398730186979892561 47870734799047640234919421)
  ·
    refine ⟨17951525549642865088094783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47870734799047640234919421 17951525549642865088094783)
    ·
      refine ⟨26927288324464297632142175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17951525549642865088094783 26927288324464297632142175)
      ·
        refine ⟨40390932486696446448213263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26927288324464297632142175 40390932486696446448213263)
        ·
          refine ⟨60586398730044669672319895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40390932486696446448213263 60586398730044669672319895)
          ·
            refine ⟨90879598095067004508479843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60586398730044669672319895 90879598095067004508479843)
            ·
              refine ⟨136319397142600506762719765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90879598095067004508479843 136319397142600506762719765)
              ·
                refine ⟨6389971741059398754502489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136319397142600506762719765 6389971741059398754502489)
                ·
                  refine ⟨4792478805794549065876867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389971741059398754502489 4792478805794549065876867)
                  ·
                    refine ⟨7188718208691823598815301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4792478805794549065876867 7188718208691823598815301)
                    ·
                      refine ⟨1347884664129716924777869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7188718208691823598815301 1347884664129716924777869)
                      ·
                        rfl

theorem cell23_2624996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_2624996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624996 prefixEnd_2624996 := by exact prefixLift 2624996
  have htrace : WordTrace (prefixWord ++ tailWord_2624996) baseStart_2624996 baseEnd_2624996 := by
    simpa [prefixWord, tailWord_2624996, baseEnd_2624996] using wordTrace_append hprefix tailTrace_2624996
  have hstable : (prefixWord ++ tailWord_2624996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624996).length < 2 ^ (prefixWord ++ tailWord_2624996).sum := by decide
  have hdescent : baseEnd_2624996 < baseStart_2624996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625013 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2625013 : Nat := 118140960795 + 2625013 * 2 ^ 59
def prefixEnd_2625013 : Nat := 4983230072969 + 3 ^ 40 * 2625013 * 2
def baseEnd_2625013 : Nat := 1347893393300843358265291

theorem tailTrace_2625013 : CollatzResearch.WordTrace tailWord_2625013 prefixEnd_2625013 1347893393300843358265291 := by
  unfold tailWord_2625013
  simp only [CollatzResearch.WordTrace]
  refine ⟨95742089639033692373207693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63828059759355794915471795 95742089639033692373207693)
  ·
    refine ⟨35903283614637634639952885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95742089639033692373207693 35903283614637634639952885)
    ·
      refine ⟨3365932838872278247495583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35903283614637634639952885 3365932838872278247495583)
      ·
        refine ⟨5048899258308417371243375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365932838872278247495583 5048899258308417371243375)
        ·
          refine ⟨7573348887462626056865063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048899258308417371243375 7573348887462626056865063)
          ·
            refine ⟨11360023331193939085297595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7573348887462626056865063 11360023331193939085297595)
            ·
              refine ⟨17040034996790908627946393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11360023331193939085297595 17040034996790908627946393)
              ·
                refine ⟨12780026247593181470959795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17040034996790908627946393 12780026247593181470959795)
                ·
                  refine ⟨19170039371389772206439693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12780026247593181470959795 19170039371389772206439693)
                  ·
                    refine ⟨7188764764271164577414885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19170039371389772206439693 7188764764271164577414885)
                    ·
                      refine ⟨1347893393300843358265291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7188764764271164577414885 1347893393300843358265291)
                      ·
                        rfl

theorem cell23_2625013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2625013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625013 prefixEnd_2625013 := by exact prefixLift 2625013
  have htrace : WordTrace (prefixWord ++ tailWord_2625013) baseStart_2625013 baseEnd_2625013 := by
    simpa [prefixWord, tailWord_2625013, baseEnd_2625013] using wordTrace_append hprefix tailTrace_2625013
  have hstable : (prefixWord ++ tailWord_2625013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625013).length < 2 ^ (prefixWord ++ tailWord_2625013).sum := by decide
  have hdescent : baseEnd_2625013 < baseStart_2625013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625016 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_2625016 : Nat := 118140960795 + 2625016 * 2 ^ 59
def prefixEnd_2625016 : Nat := 4983230072969 + 3 ^ 40 * 2625016 * 2
def baseEnd_2625016 : Nat := 1347894933742806846527777

theorem tailTrace_2625016 : CollatzResearch.WordTrace tailWord_2625016 prefixEnd_2625016 1347894933742806846527777 := by
  unfold tailWord_2625016
  simp only [CollatzResearch.WordTrace]
  refine ⟨47871099529011411942783451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63828132705348549257044601 47871099529011411942783451)
  ·
    refine ⟨71806649293517117914175177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47871099529011411942783451 71806649293517117914175177)
    ·
      refine ⟨53854986970137838435631383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71806649293517117914175177 53854986970137838435631383)
      ·
        refine ⟨80782480455206757653447075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53854986970137838435631383 80782480455206757653447075)
        ·
          refine ⟨121173720682810136480170613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80782480455206757653447075 121173720682810136480170613)
          ·
            refine ⟨11360036314013450295015995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121173720682810136480170613 11360036314013450295015995)
            ·
              refine ⟨17040054471020175442523993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11360036314013450295015995 17040054471020175442523993)
              ·
                refine ⟨12780040853265131581892995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17040054471020175442523993 12780040853265131581892995)
                ·
                  refine ⟨19170061279897697372839493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12780040853265131581892995 19170061279897697372839493)
                  ·
                    refine ⟨3594386489980818257407405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19170061279897697372839493 3594386489980818257407405)
                    ·
                      refine ⟨1347894933742806846527777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594386489980818257407405 1347894933742806846527777)
                      ·
                        rfl

theorem cell23_2625016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_2625016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625016 prefixEnd_2625016 := by exact prefixLift 2625016
  have htrace : WordTrace (prefixWord ++ tailWord_2625016) baseStart_2625016 baseEnd_2625016 := by
    simpa [prefixWord, tailWord_2625016, baseEnd_2625016] using wordTrace_append hprefix tailTrace_2625016
  have hstable : (prefixWord ++ tailWord_2625016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625016).length < 2 ^ (prefixWord ++ tailWord_2625016).sum := by decide
  have hdescent : baseEnd_2625016 < baseStart_2625016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625057 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 1, 4]
def baseStart_2625057 : Nat := 118140960795 + 2625057 * 2 ^ 59
def prefixEnd_2625057 : Nat := 4983230072969 + 3 ^ 40 * 2625057 * 2
def baseEnd_2625057 : Nat := 449305328816547062038363

theorem tailTrace_2625057 : CollatzResearch.WordTrace tailWord_2625057 prefixEnd_2625057 449305328816547062038363 := by
  unfold tailWord_2625057
  simp only [CollatzResearch.WordTrace]
  refine ⟨95743694450874287887809425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63829129633916191925206283 95743694450874287887809425)
  ·
    refine ⟨71807770838155715915857069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95743694450874287887809425 71807770838155715915857069)
    ·
      refine ⟨26927914064308393468446401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71807770838155715915857069 26927914064308393468446401)
      ·
        refine ⟨20195935548231295101334801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26927914064308393468446401 20195935548231295101334801)
        ·
          refine ⟨15146951661173471326001101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20195935548231295101334801 15146951661173471326001101)
          ·
            refine ⟨5680106872940051747250413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15146951661173471326001101 5680106872940051747250413)
            ·
              refine ⟨2130040077352519405218905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5680106872940051747250413 2130040077352519405218905)
              ·
                refine ⟨1597530058014389553914179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130040077352519405218905 1597530058014389553914179)
                ·
                  refine ⟨2396295087021584330871269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597530058014389553914179 2396295087021584330871269)
                  ·
                    refine ⟨449305328816547062038363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396295087021584330871269 449305328816547062038363)
                    ·
                      rfl

theorem cell23_2625057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_2625057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625057 prefixEnd_2625057 := by exact prefixLift 2625057
  have htrace : WordTrace (prefixWord ++ tailWord_2625057) baseStart_2625057 baseEnd_2625057 := by
    simpa [prefixWord, tailWord_2625057, baseEnd_2625057] using wordTrace_append hprefix tailTrace_2625057
  have hstable : (prefixWord ++ tailWord_2625057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625057).length < 2 ^ (prefixWord ++ tailWord_2625057).sum := by decide
  have hdescent : baseEnd_2625057 < baseStart_2625057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625070 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_2625070 : Nat := 118140960795 + 2625070 * 2 ^ 59
def prefixEnd_2625070 : Nat := 4983230072969 + 3 ^ 40 * 2625070 * 2
def baseEnd_2625070 : Nat := 149769184633127737250281

theorem tailTrace_2625070 : CollatzResearch.WordTrace tailWord_2625070 prefixEnd_2625070 149769184633127737250281 := by
  unfold tailWord_2625070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11968021074978398888504083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63829445733218127405355109 11968021074978398888504083)
  ·
    refine ⟨17952031612467598332756125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11968021074978398888504083 17952031612467598332756125)
    ·
      refine ⟨6732011854675349374783547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17952031612467598332756125 6732011854675349374783547)
      ·
        refine ⟨10098017782013024062175321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6732011854675349374783547 10098017782013024062175321)
        ·
          refine ⟨7573513336509768046631491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10098017782013024062175321 7573513336509768046631491)
          ·
            refine ⟨11360270004764652069947237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7573513336509768046631491 11360270004764652069947237)
            ·
              refine ⟨2130050625893372263115107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11360270004764652069947237 2130050625893372263115107)
              ·
                refine ⟨3195075938840058394672661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130050625893372263115107 3195075938840058394672661)
                ·
                  refine ⟨149769184633127737250281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3195075938840058394672661 149769184633127737250281)
                  ·
                    rfl

theorem cell23_2625070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_2625070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625070 prefixEnd_2625070 := by exact prefixLift 2625070
  have htrace : WordTrace (prefixWord ++ tailWord_2625070) baseStart_2625070 baseEnd_2625070 := by
    simpa [prefixWord, tailWord_2625070, baseEnd_2625070] using wordTrace_append hprefix tailTrace_2625070
  have hstable : (prefixWord ++ tailWord_2625070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625070).length < 2 ^ (prefixWord ++ tailWord_2625070).sum := by decide
  have hdescent : baseEnd_2625070 < baseStart_2625070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625073 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_2625073 : Nat := 118140960795 + 2625073 * 2 ^ 59
def prefixEnd_2625073 : Nat := 4983230072969 + 3 ^ 40 * 2625073 * 2
def baseEnd_2625073 : Nat := 1347924202140113123515015

theorem tailTrace_2625073 : CollatzResearch.WordTrace tailWord_2625073 prefixEnd_2625073 1347924202140113123515015 := by
  unfold tailWord_2625073
  simp only [CollatzResearch.WordTrace]
  refine ⟨95744278018816322620391873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63829518679210881746927915 95744278018816322620391873)
  ·
    refine ⟨71808208514112241965293905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95744278018816322620391873 71808208514112241965293905)
    ·
      refine ⟨53856156385584181473970429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71808208514112241965293905 53856156385584181473970429)
      ·
        refine ⟨20196058644594068052738911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53856156385584181473970429 20196058644594068052738911)
        ·
          refine ⟨30294087966891102079108367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20196058644594068052738911 30294087966891102079108367)
          ·
            refine ⟨45441131950336653118662551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30294087966891102079108367 45441131950336653118662551)
            ·
              refine ⟨68161697925504979677993827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45441131950336653118662551 68161697925504979677993827)
              ·
                refine ⟨102242546888257469516990741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68161697925504979677993827 102242546888257469516990741)
                ·
                  refine ⟨4792619385387068883608941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102242546888257469516990741 4792619385387068883608941)
                  ·
                    refine ⟨1797232269520150831353353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4792619385387068883608941 1797232269520150831353353)
                    ·
                      refine ⟨1347924202140113123515015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797232269520150831353353 1347924202140113123515015)
                      ·
                        rfl

theorem cell23_2625073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_2625073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625073 prefixEnd_2625073 := by exact prefixLift 2625073
  have htrace : WordTrace (prefixWord ++ tailWord_2625073) baseStart_2625073 baseEnd_2625073 := by
    simpa [prefixWord, tailWord_2625073, baseEnd_2625073] using wordTrace_append hprefix tailTrace_2625073
  have hstable : (prefixWord ++ tailWord_2625073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625073).length < 2 ^ (prefixWord ++ tailWord_2625073).sum := by decide
  have hdescent : baseEnd_2625073 < baseStart_2625073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625100 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_2625100 : Nat := 118140960795 + 2625100 * 2 ^ 59
def prefixEnd_2625100 : Nat := 4983230072969 + 3 ^ 40 * 2625100 * 2
def baseEnd_2625100 : Nat := 449312688705928172625797

theorem tailTrace_2625100 : CollatzResearch.WordTrace tailWord_2625100 prefixEnd_2625100 449312688705928172625797 := by
  unfold tailWord_2625100
  simp only [CollatzResearch.WordTrace]
  refine ⟨47872631394859253115812377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63830175193145670821083169 47872631394859253115812377)
  ·
    refine ⟨35904473546144439836859283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47872631394859253115812377 35904473546144439836859283)
    ·
      refine ⟨53856710319216659755288925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35904473546144439836859283 53856710319216659755288925)
      ·
        refine ⟨20196266369706247408233347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53856710319216659755288925 20196266369706247408233347)
        ·
          refine ⟨30294399554559371112350021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20196266369706247408233347 30294399554559371112350021)
          ·
            refine ⟨5680199916479882083565629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30294399554559371112350021 5680199916479882083565629)
            ·
              refine ⟨2130074968679955781337111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5680199916479882083565629 2130074968679955781337111)
              ·
                refine ⟨3195112453019933672005667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130074968679955781337111 3195112453019933672005667)
                ·
                  refine ⟨4792668679529900508008501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195112453019933672005667 4792668679529900508008501)
                  ·
                    refine ⟨449312688705928172625797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4792668679529900508008501 449312688705928172625797)
                    ·
                      rfl

theorem cell23_2625100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_2625100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625100 prefixEnd_2625100 := by exact prefixLift 2625100
  have htrace : WordTrace (prefixWord ++ tailWord_2625100) baseStart_2625100 baseEnd_2625100 := by
    simpa [prefixWord, tailWord_2625100, baseEnd_2625100] using wordTrace_append hprefix tailTrace_2625100
  have hstable : (prefixWord ++ tailWord_2625100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625100).length < 2 ^ (prefixWord ++ tailWord_2625100).sum := by decide
  have hdescent : baseEnd_2625100 < baseStart_2625100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625120 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2]
def baseStart_2625120 : Nat := 118140960795 + 2625120 * 2 ^ 59
def prefixEnd_2625120 : Nat := 4983230072969 + 3 ^ 40 * 2625120 * 2
def baseEnd_2625120 : Nat := 1347948335730874439627299

theorem tailTrace_2625120 : CollatzResearch.WordTrace tailWord_2625120 prefixEnd_2625120 1347948335730874439627299 := by
  unfold tailWord_2625120
  simp only [CollatzResearch.WordTrace]
  refine ⟨47872996124823024823676407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63830661499764033098235209 47872996124823024823676407)
  ·
    refine ⟨71809494187234537235514611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47872996124823024823676407 71809494187234537235514611)
    ·
      refine ⟨107714241280851805853271917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71809494187234537235514611 107714241280851805853271917)
      ·
        refine ⟨40392840480319427194976969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107714241280851805853271917 40392840480319427194976969)
        ·
          refine ⟨30294630360239570396232727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40392840480319427194976969 30294630360239570396232727)
          ·
            refine ⟨45441945540359355594349091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30294630360239570396232727 45441945540359355594349091)
            ·
              refine ⟨68162918310539033391523637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45441945540359355594349091 68162918310539033391523637)
              ·
                refine ⟨6390273591613034380455341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68162918310539033391523637 6390273591613034380455341)
                ·
                  refine ⟨2396352596854887892670753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6390273591613034380455341 2396352596854887892670753)
                  ·
                    refine ⟨1797264447641165919503065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396352596854887892670753 1797264447641165919503065)
                    ·
                      refine ⟨1347948335730874439627299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797264447641165919503065 1347948335730874439627299)
                      ·
                        rfl

theorem cell23_2625120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_2625120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625120 prefixEnd_2625120 := by exact prefixLift 2625120
  have htrace : WordTrace (prefixWord ++ tailWord_2625120) baseStart_2625120 baseEnd_2625120 := by
    simpa [prefixWord, tailWord_2625120, baseEnd_2625120] using wordTrace_append hprefix tailTrace_2625120
  have hstable : (prefixWord ++ tailWord_2625120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625120).length < 2 ^ (prefixWord ++ tailWord_2625120).sum := by decide
  have hdescent : baseEnd_2625120 < baseStart_2625120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625123 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2625123 : Nat := 118140960795 + 2625123 * 2 ^ 59
def prefixEnd_2625123 : Nat := 4983230072969 + 3 ^ 40 * 2625123 * 2
def baseEnd_2625123 : Nat := 1347949876172837927889785

theorem tailTrace_2625123 : CollatzResearch.WordTrace tailWord_2625123 prefixEnd_2625123 1347949876172837927889785 := by
  unfold tailWord_2625123
  simp only [CollatzResearch.WordTrace]
  refine ⟨95746101668635181159712023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63830734445756787439808015 95746101668635181159712023)
  ·
    refine ⟨143619152502952771739568035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95746101668635181159712023 143619152502952771739568035)
    ·
      refine ⟨215428728754429157609352053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143619152502952771739568035 215428728754429157609352053)
      ·
        refine ⟨20196443320727733525876755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215428728754429157609352053 20196443320727733525876755)
        ·
          refine ⟨30294664981091600288815133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20196443320727733525876755 30294664981091600288815133)
          ·
            refine ⟨11360499367909350108305675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30294664981091600288815133 11360499367909350108305675)
            ·
              refine ⟨17040749051864025162458513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11360499367909350108305675 17040749051864025162458513)
              ·
                refine ⟨12780561788898018871843885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17040749051864025162458513 12780561788898018871843885)
                ·
                  refine ⟨4792710670836757076941457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12780561788898018871843885 4792710670836757076941457)
                  ·
                    refine ⟨3594533003127567807706093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792710670836757076941457 3594533003127567807706093)
                    ·
                      refine ⟨1347949876172837927889785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594533003127567807706093 1347949876172837927889785)
                      ·
                        rfl

theorem cell23_2625123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2625123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625123 prefixEnd_2625123 := by exact prefixLift 2625123
  have htrace : WordTrace (prefixWord ++ tailWord_2625123) baseStart_2625123 baseEnd_2625123 := by
    simpa [prefixWord, tailWord_2625123, baseEnd_2625123] using wordTrace_append hprefix tailTrace_2625123
  have hstable : (prefixWord ++ tailWord_2625123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625123).length < 2 ^ (prefixWord ++ tailWord_2625123).sum := by decide
  have hdescent : baseEnd_2625123 < baseStart_2625123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625130 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2625130 : Nat := 118140960795 + 2625130 * 2 ^ 59
def prefixEnd_2625130 : Nat := 4983230072969 + 3 ^ 40 * 2625130 * 2
def baseEnd_2625130 : Nat := 449317823512473133500751

theorem tailTrace_2625130 : CollatzResearch.WordTrace tailWord_2625130 prefixEnd_2625130 449317823512473133500751 := by
  unfold tailWord_2625130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23936589244902455338804211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63830904653073214236811229 23936589244902455338804211)
  ·
    refine ⟨35904883867353683008206317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23936589244902455338804211 35904883867353683008206317)
    ·
      refine ⟨13464331450257631128077369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35904883867353683008206317 13464331450257631128077369)
      ·
        refine ⟨10098248587693223346058027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13464331450257631128077369 10098248587693223346058027)
        ·
          refine ⟨15147372881539835019087041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10098248587693223346058027 15147372881539835019087041)
          ·
            refine ⟨11360529661154876264315281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15147372881539835019087041 11360529661154876264315281)
            ·
              refine ⟨8520397245866157198236461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11360529661154876264315281 8520397245866157198236461)
              ·
                refine ⟨3195148967199808949338673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8520397245866157198236461 3195148967199808949338673)
                ·
                  refine ⟨2396361725399856712004005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195148967199808949338673 2396361725399856712004005)
                  ·
                    refine ⟨449317823512473133500751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396361725399856712004005 449317823512473133500751)
                    ·
                      rfl

theorem cell23_2625130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2625130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625130 prefixEnd_2625130 := by exact prefixLift 2625130
  have htrace : WordTrace (prefixWord ++ tailWord_2625130) baseStart_2625130 baseEnd_2625130 := by
    simpa [prefixWord, tailWord_2625130, baseEnd_2625130] using wordTrace_append hprefix tailTrace_2625130
  have hstable : (prefixWord ++ tailWord_2625130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625130).length < 2 ^ (prefixWord ++ tailWord_2625130).sum := by decide
  have hdescent : baseEnd_2625130 < baseStart_2625130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625187 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 2, 1, 3]
def baseStart_2625187 : Nat := 118140960795 + 2625187 * 2 ^ 59
def prefixEnd_2625187 : Nat := 4983230072969 + 3 ^ 40 * 2625187 * 2
def baseEnd_2625187 : Nat := 1347982738934725677489491

theorem tailTrace_2625187 : CollatzResearch.WordTrace tailWord_2625187 prefixEnd_2625187 1347982738934725677489491 := by
  unfold tailWord_2625187
  simp only [CollatzResearch.WordTrace]
  refine ⟨95748435940403320090041815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63832290626935546726694543 95748435940403320090041815)
  ·
    refine ⟨143622653910604980135062723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95748435940403320090041815 143622653910604980135062723)
    ·
      refine ⟨215433980865907470202594085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143622653910604980135062723 215433980865907470202594085)
      ·
        refine ⟨40393871412357650662986391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215433980865907470202594085 40393871412357650662986391)
        ·
          refine ⟨60590807118536475994479587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40393871412357650662986391 60590807118536475994479587)
          ·
            refine ⟨90886210677804713991719381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60590807118536475994479587 90886210677804713991719381)
            ·
              refine ⟨2130145562761047984180923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90886210677804713991719381 2130145562761047984180923)
              ·
                refine ⟨3195218344141571976271385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130145562761047984180923 3195218344141571976271385)
                ·
                  refine ⟨2396413758106178982203539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195218344141571976271385 2396413758106178982203539)
                  ·
                    refine ⟨3594620637159268473305309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396413758106178982203539 3594620637159268473305309)
                    ·
                      refine ⟨1347982738934725677489491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594620637159268473305309 1347982738934725677489491)
                      ·
                        rfl

theorem cell23_2625187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_2625187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625187 prefixEnd_2625187 := by exact prefixLift 2625187
  have htrace : WordTrace (prefixWord ++ tailWord_2625187) baseStart_2625187 baseEnd_2625187 := by
    simpa [prefixWord, tailWord_2625187, baseEnd_2625187] using wordTrace_append hprefix tailTrace_2625187
  have hstable : (prefixWord ++ tailWord_2625187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625187).length < 2 ^ (prefixWord ++ tailWord_2625187).sum := by decide
  have hdescent : baseEnd_2625187 < baseStart_2625187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625196 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2625196 : Nat := 118140960795 + 2625196 * 2 ^ 59
def prefixEnd_2625196 : Nat := 4983230072969 + 3 ^ 40 * 2625196 * 2
def baseEnd_2625196 : Nat := 1347987360260616142276949

theorem tailTrace_2625196 : CollatzResearch.WordTrace tailWord_2625196 prefixEnd_2625196 1347987360260616142276949 := by
  unfold tailWord_2625196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47874382098685357313559721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63832509464913809751412961 47874382098685357313559721)
  ·
    refine ⟨35905786574014017985169791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47874382098685357313559721 35905786574014017985169791)
    ·
      refine ⟨53858679861021026977754687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35905786574014017985169791 53858679861021026977754687)
      ·
        refine ⟨80788019791531540466632031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53858679861021026977754687 80788019791531540466632031)
        ·
          refine ⟨121182029687297310699948047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80788019791531540466632031 121182029687297310699948047)
          ·
            refine ⟨181773044530945966049922071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121182029687297310699948047 181773044530945966049922071)
            ·
              refine ⟨272659566796418949074883107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181773044530945966049922071 272659566796418949074883107)
              ·
                refine ⟨408989350194628423612324661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272659566796418949074883107 408989350194628423612324661)
                ·
                  refine ⟨38342751580746414713655437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408989350194628423612324661 38342751580746414713655437)
                  ·
                    refine ⟨14378531842779905517620789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38342751580746414713655437 14378531842779905517620789)
                    ·
                      refine ⟨1347987360260616142276949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14378531842779905517620789 1347987360260616142276949)
                      ·
                        rfl

theorem cell23_2625196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2625196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625196 prefixEnd_2625196 := by exact prefixLift 2625196
  have htrace : WordTrace (prefixWord ++ tailWord_2625196) baseStart_2625196 baseEnd_2625196 := by
    simpa [prefixWord, tailWord_2625196, baseEnd_2625196] using wordTrace_append hprefix tailTrace_2625196
  have hstable : (prefixWord ++ tailWord_2625196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625196).length < 2 ^ (prefixWord ++ tailWord_2625196).sum := by decide
  have hdescent : baseEnd_2625196 < baseStart_2625196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625213 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2625213 : Nat := 118140960795 + 2625213 * 2 ^ 59
def prefixEnd_2625213 : Nat := 4983230072969 + 3 ^ 40 * 2625213 * 2
def baseEnd_2625213 : Nat := 1347996089431742575764371

theorem tailTrace_2625213 : CollatzResearch.WordTrace tailWord_2625213 prefixEnd_2625213 1347996089431742575764371 := by
  unfold tailWord_2625213
  simp only [CollatzResearch.WordTrace]
  refine ⟨95749384238309126530488293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63832922825539417686992195 95749384238309126530488293)
  ·
    refine ⟨17953009544682961224466555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95749384238309126530488293 17953009544682961224466555)
    ·
      refine ⟨26929514317024441836699833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17953009544682961224466555 26929514317024441836699833)
      ·
        refine ⟨20197135737768331377524875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26929514317024441836699833 20197135737768331377524875)
        ·
          refine ⟨30295703606652497066287313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20197135737768331377524875 30295703606652497066287313)
          ·
            refine ⟨22721777704989372799715485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30295703606652497066287313 22721777704989372799715485)
            ·
              refine ⟨8520666639371014799893307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22721777704989372799715485 8520666639371014799893307)
              ·
                refine ⟨12780999959056522199839961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520666639371014799893307 12780999959056522199839961)
                ·
                  refine ⟨9585749969292391649879971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12780999959056522199839961 9585749969292391649879971)
                  ·
                    refine ⟨14378624953938587474819957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9585749969292391649879971 14378624953938587474819957)
                    ·
                      refine ⟨1347996089431742575764371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14378624953938587474819957 1347996089431742575764371)
                      ·
                        rfl

theorem cell23_2625213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2625213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625213 prefixEnd_2625213 := by exact prefixLift 2625213
  have htrace : WordTrace (prefixWord ++ tailWord_2625213) baseStart_2625213 baseEnd_2625213 := by
    simpa [prefixWord, tailWord_2625213, baseEnd_2625213] using wordTrace_append hprefix tailTrace_2625213
  have hstable : (prefixWord ++ tailWord_2625213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625213).length < 2 ^ (prefixWord ++ tailWord_2625213).sum := by decide
  have hdescent : baseEnd_2625213 < baseStart_2625213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625233 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 7]
def baseStart_2625233 : Nat := 118140960795 + 2625233 * 2 ^ 59
def prefixEnd_2625233 : Nat := 4983230072969 + 3 ^ 40 * 2625233 * 2
def baseEnd_2625233 : Nat := 149778484338314721946031

theorem tailTrace_2625233 : CollatzResearch.WordTrace tailWord_2625233 prefixEnd_2625233 149778484338314721946031 := by
  unfold tailWord_2625233
  simp only [CollatzResearch.WordTrace]
  refine ⟨95750113698236669946216353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63833409132157779964144235 95750113698236669946216353)
  ·
    refine ⟨71812585273677502459662265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95750113698236669946216353 71812585273677502459662265)
    ·
      refine ⟨53859438955258126844746699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71812585273677502459662265 53859438955258126844746699)
      ·
        refine ⟨80789158432887190267120049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53859438955258126844746699 80789158432887190267120049)
        ·
          refine ⟨60591868824665392700340037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80789158432887190267120049 60591868824665392700340037)
          ·
            refine ⟨11360975404624761131313757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60591868824665392700340037 11360975404624761131313757)
            ·
              refine ⟨4260365776734285424242659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11360975404624761131313757 4260365776734285424242659)
              ·
                refine ⟨6390548665101428136363989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260365776734285424242659 6390548665101428136363989)
                ·
                  refine ⟨149778484338314721946031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6390548665101428136363989 149778484338314721946031)
                  ·
                    rfl

theorem cell23_2625233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_2625233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625233 prefixEnd_2625233 := by exact prefixLift 2625233
  have htrace : WordTrace (prefixWord ++ tailWord_2625233) baseStart_2625233 baseEnd_2625233 := by
    simpa [prefixWord, tailWord_2625233, baseEnd_2625233] using wordTrace_append hprefix tailTrace_2625233
  have hstable : (prefixWord ++ tailWord_2625233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625233).length < 2 ^ (prefixWord ++ tailWord_2625233).sum := by decide
  have hdescent : baseEnd_2625233 < baseStart_2625233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625284 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2625284 : Nat := 118140960795 + 2625284 * 2 ^ 59
def prefixEnd_2625284 : Nat := 4983230072969 + 3 ^ 40 * 2625284 * 2
def baseEnd_2625284 : Nat := 149781394062023533108505

theorem tailTrace_2625284 : CollatzResearch.WordTrace tailWord_2625284 prefixEnd_2625284 149781394062023533108505 := by
  unfold tailWord_2625284
  simp only [CollatzResearch.WordTrace]
  refine ⟨47875986910525952828161453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63834649214034603770881937 47875986910525952828161453)
  ·
    refine ⟨17953495091447232310560545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47875986910525952828161453 17953495091447232310560545)
    ·
      refine ⟨13465121318585424232920409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17953495091447232310560545 13465121318585424232920409)
      ·
        refine ⟨10098840988939068174690307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13465121318585424232920409 10098840988939068174690307)
        ·
          refine ⟨15148261483408602262035461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10098840988939068174690307 15148261483408602262035461)
          ·
            refine ⟨2840299028139112924131649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15148261483408602262035461 2840299028139112924131649)
            ·
              refine ⟨2130224271104334693098737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840299028139112924131649 2130224271104334693098737)
              ·
                refine ⟨1597668203328251019824053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130224271104334693098737 1597668203328251019824053)
                ·
                  refine ⟨149781394062023533108505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1597668203328251019824053 149781394062023533108505)
                  ·
                    rfl

theorem cell23_2625284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2625284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625284 prefixEnd_2625284 := by exact prefixLift 2625284
  have htrace : WordTrace (prefixWord ++ tailWord_2625284) baseStart_2625284 baseEnd_2625284 := by
    simpa [prefixWord, tailWord_2625284, baseEnd_2625284] using wordTrace_append hprefix tailTrace_2625284
  have hstable : (prefixWord ++ tailWord_2625284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625284).length < 2 ^ (prefixWord ++ tailWord_2625284).sum := by decide
  have hdescent : baseEnd_2625284 < baseStart_2625284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625317 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_2625317 : Nat := 118140960795 + 2625317 * 2 ^ 59
def prefixEnd_2625317 : Nat := 4983230072969 + 3 ^ 40 * 2625317 * 2
def baseEnd_2625317 : Nat := 1348049491419810168863893

theorem tailTrace_2625317 : CollatzResearch.WordTrace tailWord_2625317 prefixEnd_2625317 1348049491419810168863893 := by
  unfold tailWord_2625317
  simp only [CollatzResearch.WordTrace]
  refine ⟨95753177429932352292274205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63835451619954901528182803 95753177429932352292274205)
  ·
    refine ⟨35907441536224632109602827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95753177429932352292274205 35907441536224632109602827)
    ·
      refine ⟨53861162304336948164404241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35907441536224632109602827 53861162304336948164404241)
      ·
        refine ⟨40395871728252711123303181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53861162304336948164404241 40395871728252711123303181)
        ·
          refine ⟨15148451898094766671238693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40395871728252711123303181 15148451898094766671238693)
          ·
            refine ⟨2840334730892768750857255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15148451898094766671238693 2840334730892768750857255)
            ·
              refine ⟨4260502096339153126285883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840334730892768750857255 4260502096339153126285883)
              ·
                refine ⟨6390753144508729689428825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260502096339153126285883 6390753144508729689428825)
                ·
                  refine ⟨4793064858381547267071619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390753144508729689428825 4793064858381547267071619)
                  ·
                    refine ⟨7189597287572320900607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793064858381547267071619 7189597287572320900607429)
                    ·
                      refine ⟨1348049491419810168863893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7189597287572320900607429 1348049491419810168863893)
                      ·
                        rfl

theorem cell23_2625317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_2625317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625317 prefixEnd_2625317 := by exact prefixLift 2625317
  have htrace : WordTrace (prefixWord ++ tailWord_2625317) baseStart_2625317 baseEnd_2625317 := by
    simpa [prefixWord, tailWord_2625317, baseEnd_2625317] using wordTrace_append hprefix tailTrace_2625317
  have hstable : (prefixWord ++ tailWord_2625317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625317).length < 2 ^ (prefixWord ++ tailWord_2625317).sum := by decide
  have hdescent : baseEnd_2625317 < baseStart_2625317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625334 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2625334 : Nat := 118140960795 + 2625334 * 2 ^ 59
def prefixEnd_2625334 : Nat := 4983230072969 + 3 ^ 40 * 2625334 * 2
def baseEnd_2625334 : Nat := 1348058220590936602351315

theorem tailTrace_2625334 : CollatzResearch.WordTrace tailWord_2625334 prefixEnd_2625334 1348058220590936602351315 := by
  unfold tailWord_2625334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984612341929422762227691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63835864980580509463762037 5984612341929422762227691)
  ·
    refine ⟨8976918512894134143341537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5984612341929422762227691 8976918512894134143341537)
    ·
      refine ⟨6732688884670600607506153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8976918512894134143341537 6732688884670600607506153)
      ·
        refine ⟨5049516663502950455629615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6732688884670600607506153 5049516663502950455629615)
        ·
          refine ⟨7574274995254425683444423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049516663502950455629615 7574274995254425683444423)
          ·
            refine ⟨11361412492881638525166635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574274995254425683444423 11361412492881638525166635)
            ·
              refine ⟨17042118739322457787749953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11361412492881638525166635 17042118739322457787749953)
              ·
                refine ⟨12781589054491843340812465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17042118739322457787749953 12781589054491843340812465)
                ·
                  refine ⟨9586191790868882505609349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12781589054491843340812465 9586191790868882505609349)
                  ·
                    refine ⟨1797410960787915469801753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9586191790868882505609349 1797410960787915469801753)
                    ·
                      refine ⟨1348058220590936602351315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797410960787915469801753 1348058220590936602351315)
                      ·
                        rfl

theorem cell23_2625334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2625334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625334 prefixEnd_2625334 := by exact prefixLift 2625334
  have htrace : WordTrace (prefixWord ++ tailWord_2625334) baseStart_2625334 baseEnd_2625334 := by
    simpa [prefixWord, tailWord_2625334, baseEnd_2625334] using wordTrace_append hprefix tailTrace_2625334
  have hstable : (prefixWord ++ tailWord_2625334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625334).length < 2 ^ (prefixWord ++ tailWord_2625334).sum := by decide
  have hdescent : baseEnd_2625334 < baseStart_2625334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625340 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 6]
def baseStart_2625340 : Nat := 118140960795 + 2625340 * 2 ^ 59
def prefixEnd_2625340 : Nat := 4983230072969 + 3 ^ 40 * 2625340 * 2
def baseEnd_2625340 : Nat := 149784589052762619875143

theorem tailTrace_2625340 : CollatzResearch.WordTrace tailWord_2625340 prefixEnd_2625340 149784589052762619875143 := by
  unfold tailWord_2625340
  simp only [CollatzResearch.WordTrace]
  refine ⟨47877008154424513610180737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63836010872566018146907649 47877008154424513610180737)
  ·
    refine ⟨35907756115818385207635553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47877008154424513610180737 35907756115818385207635553)
    ·
      refine ⟨26930817086863788905726665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35907756115818385207635553 26930817086863788905726665)
      ·
        refine ⟨20198112815147841679294999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26930817086863788905726665 20198112815147841679294999)
        ·
          refine ⟨30297169222721762518942499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20198112815147841679294999 30297169222721762518942499)
          ·
            refine ⟨45445753834082643778413749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30297169222721762518942499 45445753834082643778413749)
            ·
              refine ⟨4260539421945247854226289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45445753834082643778413749 4260539421945247854226289)
              ·
                refine ⟨3195404566458935890669717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260539421945247854226289 3195404566458935890669717)
                ·
                  refine ⟨149784589052762619875143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3195404566458935890669717 149784589052762619875143)
                  ·
                    rfl

theorem cell23_2625340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_2625340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625340 prefixEnd_2625340 := by exact prefixLift 2625340
  have htrace : WordTrace (prefixWord ++ tailWord_2625340) baseStart_2625340 baseEnd_2625340 := by
    simpa [prefixWord, tailWord_2625340, baseEnd_2625340] using wordTrace_append hprefix tailTrace_2625340
  have hstable : (prefixWord ++ tailWord_2625340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625340).length < 2 ^ (prefixWord ++ tailWord_2625340).sum := by decide
  have hdescent : baseEnd_2625340 < baseStart_2625340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625377 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_2625377 : Nat := 118140960795 + 2625377 * 2 ^ 59
def prefixEnd_2625377 : Nat := 4983230072969 + 3 ^ 40 * 2625377 * 2
def baseEnd_2625377 : Nat := 1348080300259079934113617

theorem tailTrace_2625377 : CollatzResearch.WordTrace tailWord_2625377 prefixEnd_2625377 1348080300259079934113617 := by
  unfold tailWord_2625377
  simp only [CollatzResearch.WordTrace]
  refine ⟨95755365809714982539458385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63836910539809988359638923 95755365809714982539458385)
  ·
    refine ⟨71816524357286236904593789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95755365809714982539458385 71816524357286236904593789)
    ·
      refine ⟨26931196633982338839222671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71816524357286236904593789 26931196633982338839222671)
      ·
        refine ⟨40396794950973508258834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26931196633982338839222671 40396794950973508258834007)
        ·
          refine ⟨60595192426460262388251011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40396794950973508258834007 60595192426460262388251011)
          ·
            refine ⟨90892788639690393582376517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60595192426460262388251011 90892788639690393582376517)
            ·
              refine ⟨17042397869941948796695597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90892788639690393582376517 17042397869941948796695597)
              ·
                refine ⟨6390899201228230798760849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17042397869941948796695597 6390899201228230798760849)
                ·
                  refine ⟨4793174400921173099070637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390899201228230798760849 4793174400921173099070637)
                  ·
                    refine ⟨1797440400345439912151489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4793174400921173099070637 1797440400345439912151489)
                    ·
                      refine ⟨1348080300259079934113617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797440400345439912151489 1348080300259079934113617)
                      ·
                        rfl

theorem cell23_2625377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_2625377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625377 prefixEnd_2625377 := by exact prefixLift 2625377
  have htrace : WordTrace (prefixWord ++ tailWord_2625377) baseStart_2625377 baseEnd_2625377 := by
    simpa [prefixWord, tailWord_2625377, baseEnd_2625377] using wordTrace_append hprefix tailTrace_2625377
  have hstable : (prefixWord ++ tailWord_2625377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625377).length < 2 ^ (prefixWord ++ tailWord_2625377).sum := by decide
  have hdescent : baseEnd_2625377 < baseStart_2625377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625401 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 1, 1, 3]
def baseStart_2625401 : Nat := 118140960795 + 2625401 * 2 ^ 59
def prefixEnd_2625401 : Nat := 4983230072969 + 3 ^ 40 * 2625401 * 2
def baseEnd_2625401 : Nat := 1348092623794787840213507

theorem tailTrace_2625401 : CollatzResearch.WordTrace tailWord_2625401 prefixEnd_2625401 1348092623794787840213507 := by
  unfold tailWord_2625401
  simp only [CollatzResearch.WordTrace]
  refine ⟨95756241161628034638332057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63837494107752023092221371 95756241161628034638332057)
  ·
    refine ⟨71817180871221025978749043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95756241161628034638332057 71817180871221025978749043)
    ·
      refine ⟨107725771306831538968123565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71817180871221025978749043 107725771306831538968123565)
      ·
        refine ⟨40397164240061827113046337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107725771306831538968123565 40397164240061827113046337)
        ·
          refine ⟨30297873180046370334784753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40397164240061827113046337 30297873180046370334784753)
          ·
            refine ⟨22723404885034777751088565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30297873180046370334784753 22723404885034777751088565)
            ·
              refine ⟨2130319207972010414164553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22723404885034777751088565 2130319207972010414164553)
              ·
                refine ⟨1597739405979007810623415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130319207972010414164553 1597739405979007810623415)
                ·
                  refine ⟨2396609108968511715935123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597739405979007810623415 2396609108968511715935123)
                  ·
                    refine ⟨3594913663452767573902685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396609108968511715935123 3594913663452767573902685)
                    ·
                      refine ⟨1348092623794787840213507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594913663452767573902685 1348092623794787840213507)
                      ·
                        rfl

theorem cell23_2625401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_2625401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625401 prefixEnd_2625401 := by exact prefixLift 2625401
  have htrace : WordTrace (prefixWord ++ tailWord_2625401) baseStart_2625401 baseEnd_2625401 := by
    simpa [prefixWord, tailWord_2625401, baseEnd_2625401] using wordTrace_append hprefix tailTrace_2625401
  have hstable : (prefixWord ++ tailWord_2625401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625401).length < 2 ^ (prefixWord ++ tailWord_2625401).sum := by decide
  have hdescent : baseEnd_2625401 < baseStart_2625401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625417 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_2625417 : Nat := 118140960795 + 2625417 * 2 ^ 59
def prefixEnd_2625417 : Nat := 4983230072969 + 3 ^ 40 * 2625417 * 2
def baseEnd_2625417 : Nat := 449366946495086592537811

theorem tailTrace_2625417 : CollatzResearch.WordTrace tailWord_2625417 prefixEnd_2625417 449366946495086592537811 := by
  unfold tailWord_2625417
  simp only [CollatzResearch.WordTrace]
  refine ⟨95756824729570069370914505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63837883153046712913943003 95756824729570069370914505)
  ·
    refine ⟨71817618547177552028185879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95756824729570069370914505 71817618547177552028185879)
    ·
      refine ⟨107726427820766328042278819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71817618547177552028185879 107726427820766328042278819)
      ·
        refine ⟨161589641731149492063418229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107726427820766328042278819 161589641731149492063418229)
        ·
          refine ⟨15149028912295264880945459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161589641731149492063418229 15149028912295264880945459)
          ·
            refine ⟨22723543368442897321418189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15149028912295264880945459 22723543368442897321418189)
            ·
              refine ⟨8521328763166086495531821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22723543368442897321418189 8521328763166086495531821)
              ·
                refine ⟨3195498286187282435824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8521328763166086495531821 3195498286187282435824433)
                ·
                  refine ⟨2396623714640461826868325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195498286187282435824433 2396623714640461826868325)
                  ·
                    refine ⟨449366946495086592537811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396623714640461826868325 449366946495086592537811)
                    ·
                      rfl

theorem cell23_2625417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_2625417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625417 prefixEnd_2625417 := by exact prefixLift 2625417
  have htrace : WordTrace (prefixWord ++ tailWord_2625417) baseStart_2625417 baseEnd_2625417 := by
    simpa [prefixWord, tailWord_2625417, baseEnd_2625417] using wordTrace_append hprefix tailTrace_2625417
  have hstable : (prefixWord ++ tailWord_2625417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625417).length < 2 ^ (prefixWord ++ tailWord_2625417).sum := by decide
  have hdescent : baseEnd_2625417 < baseStart_2625417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625420 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2625420 : Nat := 118140960795 + 2625420 * 2 ^ 59
def prefixEnd_2625420 : Nat := 4983230072969 + 3 ^ 40 * 2625420 * 2
def baseEnd_2625420 : Nat := 1348102379927223265875919

theorem tailTrace_2625420 : CollatzResearch.WordTrace tailWord_2625420 prefixEnd_2625420 1348102379927223265875919 := by
  unfold tailWord_2625420
  simp only [CollatzResearch.WordTrace]
  refine ⟨47878467074279600441636857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63837956099039467255515809 47878467074279600441636857)
  ·
    refine ⟨35908850305709700331227643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47878467074279600441636857 35908850305709700331227643)
    ·
      refine ⟨53863275458564550496841465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35908850305709700331227643 53863275458564550496841465)
      ·
        refine ⟨40397456593923412872631099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53863275458564550496841465 40397456593923412872631099)
        ·
          refine ⟨60596184890885119308946649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40397456593923412872631099 60596184890885119308946649)
          ·
            refine ⟨45447138668163839481709987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60596184890885119308946649 45447138668163839481709987)
            ·
              refine ⟨68170708002245759222564981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45447138668163839481709987 68170708002245759222564981)
              ·
                refine ⟨6391003875210539927115467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68170708002245759222564981 6391003875210539927115467)
                ·
                  refine ⟨9586505812815809890673201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391003875210539927115467 9586505812815809890673201)
                  ·
                    refine ⟨7189879359611857418004901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9586505812815809890673201 7189879359611857418004901)
                    ·
                      refine ⟨1348102379927223265875919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7189879359611857418004901 1348102379927223265875919)
                      ·
                        rfl

theorem cell23_2625420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2625420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625420 prefixEnd_2625420 := by exact prefixLift 2625420
  have htrace : WordTrace (prefixWord ++ tailWord_2625420) baseStart_2625420 baseEnd_2625420 := by
    simpa [prefixWord, tailWord_2625420, baseEnd_2625420] using wordTrace_append hprefix tailTrace_2625420
  have hstable : (prefixWord ++ tailWord_2625420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625420).length < 2 ^ (prefixWord ++ tailWord_2625420).sum := by decide
  have hdescent : baseEnd_2625420 < baseStart_2625420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625437 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2625437 : Nat := 118140960795 + 2625437 * 2 ^ 59
def prefixEnd_2625437 : Nat := 4983230072969 + 3 ^ 40 * 2625437 * 2
def baseEnd_2625437 : Nat := 1348111109098349699363341

theorem tailTrace_2625437 : CollatzResearch.WordTrace tailWord_2625437 prefixEnd_2625437 1348111109098349699363341 := by
  unfold tailWord_2625437
  simp only [CollatzResearch.WordTrace]
  refine ⟨95757554189497612786642565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63838369459665075191095043 95757554189497612786642565)
  ·
    refine ⟨17954541410530802397495481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95757554189497612786642565 17954541410530802397495481)
    ·
      refine ⟨13465906057898101798121611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17954541410530802397495481 13465906057898101798121611)
      ·
        refine ⟨20198859086847152697182417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13465906057898101798121611 20198859086847152697182417)
        ·
          refine ⟨15149144315135364522886813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20198859086847152697182417 15149144315135364522886813)
          ·
            refine ⟨5680929118175761696082555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15149144315135364522886813 5680929118175761696082555)
            ·
              refine ⟨8521393677263642544123833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680929118175761696082555 8521393677263642544123833)
              ·
                refine ⟨6391045257947731908092875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521393677263642544123833 6391045257947731908092875)
                ·
                  refine ⟨9586567886921597862139313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6391045257947731908092875 9586567886921597862139313)
                  ·
                    refine ⟨7189925915191198396604485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9586567886921597862139313 7189925915191198396604485)
                    ·
                      refine ⟨1348111109098349699363341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7189925915191198396604485 1348111109098349699363341)
                      ·
                        rfl

theorem cell23_2625437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2625437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625437 prefixEnd_2625437 := by exact prefixLift 2625437
  have htrace : WordTrace (prefixWord ++ tailWord_2625437) baseStart_2625437 baseEnd_2625437 := by
    simpa [prefixWord, tailWord_2625437, baseEnd_2625437] using wordTrace_append hprefix tailTrace_2625437
  have hstable : (prefixWord ++ tailWord_2625437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625437).length < 2 ^ (prefixWord ++ tailWord_2625437).sum := by decide
  have hdescent : baseEnd_2625437 < baseStart_2625437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625438 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2625438 : Nat := 118140960795 + 2625438 * 2 ^ 59
def prefixEnd_2625438 : Nat := 4983230072969 + 3 ^ 40 * 2625438 * 2
def baseEnd_2625438 : Nat := 449370540859668065150279

theorem tailTrace_2625438 : CollatzResearch.WordTrace tailWord_2625438 prefixEnd_2625438 449370540859668065150279 := by
  unfold tailWord_2625438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969698832811748744678621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63838393774995993304952645 11969698832811748744678621)
  ·
    refine ⟨4488637062304405779254483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11969698832811748744678621 4488637062304405779254483)
    ·
      refine ⟨6732955593456608668881725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4488637062304405779254483 6732955593456608668881725)
      ·
        refine ⟨2524858347546228250830647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6732955593456608668881725 2524858347546228250830647)
        ·
          refine ⟨3787287521319342376245971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524858347546228250830647 3787287521319342376245971)
          ·
            refine ⟨5680931281979013564368957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787287521319342376245971 5680931281979013564368957)
            ·
              refine ⟨2130349230742130086638359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5680931281979013564368957 2130349230742130086638359)
              ·
                refine ⟨3195523846113195129957539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130349230742130086638359 3195523846113195129957539)
                ·
                  refine ⟨4793285769169792694936309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195523846113195129957539 4793285769169792694936309)
                  ·
                    refine ⟨449370540859668065150279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4793285769169792694936309 449370540859668065150279)
                    ·
                      rfl

theorem cell23_2625438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2625438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625438 prefixEnd_2625438 := by exact prefixLift 2625438
  have htrace : WordTrace (prefixWord ++ tailWord_2625438) baseStart_2625438 baseEnd_2625438 := by
    simpa [prefixWord, tailWord_2625438, baseEnd_2625438] using wordTrace_append hprefix tailTrace_2625438
  have hstable : (prefixWord ++ tailWord_2625438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625438).length < 2 ^ (prefixWord ++ tailWord_2625438).sum := by decide
  have hdescent : baseEnd_2625438 < baseStart_2625438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625441 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2625441 : Nat := 118140960795 + 2625441 * 2 ^ 59
def prefixEnd_2625441 : Nat := 4983230072969 + 3 ^ 40 * 2625441 * 2
def baseEnd_2625441 : Nat := 1348113163020967683713323

theorem tailTrace_2625441 : CollatzResearch.WordTrace tailWord_2625441 prefixEnd_2625441 1348113163020967683713323 := by
  unfold tailWord_2625441
  simp only [CollatzResearch.WordTrace]
  refine ⟨95757700081483121469788177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63838466720988747646525451 95757700081483121469788177)
  ·
    refine ⟨71818275061112341102341133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95757700081483121469788177 71818275061112341102341133)
    ·
      refine ⟨26931853147917127913377925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71818275061112341102341133 26931853147917127913377925)
      ·
        refine ⟨5049722465234461483758361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26931853147917127913377925 5049722465234461483758361)
        ·
          refine ⟨3787291848925846112818771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5049722465234461483758361 3787291848925846112818771)
          ·
            refine ⟨5680937773388769169228157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787291848925846112818771 5680937773388769169228157)
            ·
              refine ⟨2130351665020788438460559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5680937773388769169228157 2130351665020788438460559)
              ·
                refine ⟨3195527497531182657690839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130351665020788438460559 3195527497531182657690839)
                ·
                  refine ⟨4793291246296773986536259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3195527497531182657690839 4793291246296773986536259)
                  ·
                    refine ⟨7189936869445160979804389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4793291246296773986536259 7189936869445160979804389)
                    ·
                      refine ⟨1348113163020967683713323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7189936869445160979804389 1348113163020967683713323)
                      ·
                        rfl

theorem cell23_2625441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2625441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625441 prefixEnd_2625441 := by exact prefixLift 2625441
  have htrace : WordTrace (prefixWord ++ tailWord_2625441) baseStart_2625441 baseEnd_2625441 := by
    simpa [prefixWord, tailWord_2625441, baseEnd_2625441] using wordTrace_append hprefix tailTrace_2625441
  have hstable : (prefixWord ++ tailWord_2625441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625441).length < 2 ^ (prefixWord ++ tailWord_2625441).sum := by decide
  have hdescent : baseEnd_2625441 < baseStart_2625441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625467 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 3, 3, 2]
def baseStart_2625467 : Nat := 118140960795 + 2625467 * 2 ^ 59
def prefixEnd_2625467 : Nat := 4983230072969 + 3 ^ 40 * 2625467 * 2
def baseEnd_2625467 : Nat := 1348126513517984581988203

theorem tailTrace_2625467 : CollatzResearch.WordTrace tailWord_2625467 prefixEnd_2625467 1348126513517984581988203 := by
  unfold tailWord_2625467
  simp only [CollatzResearch.WordTrace]
  refine ⟨95758648379388927910234655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63839098919592618606823103 95758648379388927910234655)
  ·
    refine ⟨143637972569083391865351983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95758648379388927910234655 143637972569083391865351983)
    ·
      refine ⟨215456958853625087798027975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143637972569083391865351983 215456958853625087798027975)
      ·
        refine ⟨323185438280437631697041963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215456958853625087798027975 323185438280437631697041963)
        ·
          refine ⟨484778157420656447545562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323185438280437631697041963 484778157420656447545562945)
          ·
            refine ⟨363583618065492335659172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484778157420656447545562945 363583618065492335659172209)
            ·
              refine ⟨272687713549119251744379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363583618065492335659172209 272687713549119251744379157)
              ·
                refine ⟨12782236572614964925517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272687713549119251744379157 12782236572614964925517773)
                ·
                  refine ⟨4793338714730611847069165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12782236572614964925517773 4793338714730611847069165)
                  ·
                    refine ⟨1797502018023979442650937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4793338714730611847069165 1797502018023979442650937)
                    ·
                      refine ⟨1348126513517984581988203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797502018023979442650937 1348126513517984581988203)
                      ·
                        rfl

theorem cell23_2625467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 3, 2].length) (baseStart_2625467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625467 prefixEnd_2625467 := by exact prefixLift 2625467
  have htrace : WordTrace (prefixWord ++ tailWord_2625467) baseStart_2625467 baseEnd_2625467 := by
    simpa [prefixWord, tailWord_2625467, baseEnd_2625467] using wordTrace_append hprefix tailTrace_2625467
  have hstable : (prefixWord ++ tailWord_2625467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625467).length < 2 ^ (prefixWord ++ tailWord_2625467).sum := by decide
  have hdescent : baseEnd_2625467 < baseStart_2625467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625484 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2625484 : Nat := 118140960795 + 2625484 * 2 ^ 59
def prefixEnd_2625484 : Nat := 4983230072969 + 3 ^ 40 * 2625484 * 2
def baseEnd_2625484 : Nat := 1348135242689111015475625

theorem tailTrace_2625484 : CollatzResearch.WordTrace tailWord_2625484 prefixEnd_2625484 1348135242689111015475625 := by
  unfold tailWord_2625484
  simp only [CollatzResearch.WordTrace]
  refine ⟨47879634210163669906801753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63839512280218226542402337 47879634210163669906801753)
  ·
    refine ⟨35909725657622752430101315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47879634210163669906801753 35909725657622752430101315)
    ·
      refine ⟨53864588486434128645151973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35909725657622752430101315 53864588486434128645151973)
      ·
        refine ⟨10099610341206399120965995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53864588486434128645151973 10099610341206399120965995)
        ·
          refine ⟨15149415511809598681448993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10099610341206399120965995 15149415511809598681448993)
          ·
            refine ⟨11362061633857199011086745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15149415511809598681448993 11362061633857199011086745)
            ·
              refine ⟨8521546225392899258315059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11362061633857199011086745 8521546225392899258315059)
              ·
                refine ⟨12782319338089348887472589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8521546225392899258315059 12782319338089348887472589)
                ·
                  refine ⟨4793369751783505832802221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12782319338089348887472589 4793369751783505832802221)
                  ·
                    refine ⟨1797513656918814687300833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4793369751783505832802221 1797513656918814687300833)
                    ·
                      refine ⟨1348135242689111015475625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797513656918814687300833 1348135242689111015475625)
                      ·
                        rfl

theorem cell23_2625484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2625484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625484 prefixEnd_2625484 := by exact prefixLift 2625484
  have htrace : WordTrace (prefixWord ++ tailWord_2625484) baseStart_2625484 baseEnd_2625484 := by
    simpa [prefixWord, tailWord_2625484, baseEnd_2625484] using wordTrace_append hprefix tailTrace_2625484
  have hstable : (prefixWord ++ tailWord_2625484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625484).length < 2 ^ (prefixWord ++ tailWord_2625484).sum := by decide
  have hdescent : baseEnd_2625484 < baseStart_2625484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625520 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 7]
def baseStart_2625520 : Nat := 118140960795 + 2625520 * 2 ^ 59
def prefixEnd_2625520 : Nat := 4983230072969 + 3 ^ 40 * 2625520 * 2
def baseEnd_2625520 : Nat := 149794858665852541625051

theorem tailTrace_2625520 : CollatzResearch.WordTrace tailWord_2625520 prefixEnd_2625520 149794858665852541625051 := by
  unfold tailWord_2625520
  simp only [CollatzResearch.WordTrace]
  refine ⟨47880290724098458980957007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63840387632131278641276009 47880290724098458980957007)
  ·
    refine ⟨71820436086147688471435511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47880290724098458980957007 71820436086147688471435511)
    ·
      refine ⟨107730654129221532707153267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71820436086147688471435511 107730654129221532707153267)
      ·
        refine ⟨161595981193832299060729901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107730654129221532707153267 161595981193832299060729901)
        ·
          refine ⟨60598492947687112147773713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161595981193832299060729901 60598492947687112147773713)
          ·
            refine ⟨45448869710765334110830285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60598492947687112147773713 45448869710765334110830285)
            ·
              refine ⟨17043326141537000291561357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45448869710765334110830285 17043326141537000291561357)
              ·
                refine ⟨6391247303076375109335509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17043326141537000291561357 6391247303076375109335509)
                ·
                  refine ⟨149794858665852541625051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6391247303076375109335509 149794858665852541625051)
                  ·
                    rfl

theorem cell23_2625520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_2625520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625520 prefixEnd_2625520 := by exact prefixLift 2625520
  have htrace : WordTrace (prefixWord ++ tailWord_2625520) baseStart_2625520 baseEnd_2625520 := by
    simpa [prefixWord, tailWord_2625520, baseEnd_2625520] using wordTrace_append hprefix tailTrace_2625520
  have hstable : (prefixWord ++ tailWord_2625520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625520).length < 2 ^ (prefixWord ++ tailWord_2625520).sum := by decide
  have hdescent : baseEnd_2625520 < baseStart_2625520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625567 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 2, 5]
def baseStart_2625567 : Nat := 118140960795 + 2625567 * 2 ^ 59
def prefixEnd_2625567 : Nat := 4983230072969 + 3 ^ 40 * 2625567 * 2
def baseEnd_2625567 : Nat := 449392620527811396912581

theorem tailTrace_2625567 : CollatzResearch.WordTrace tailWord_2625567 prefixEnd_2625567 449392620527811396912581 := by
  unfold tailWord_2625567
  simp only [CollatzResearch.WordTrace]
  refine ⟨95762295679026644988874955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63841530452684429992583303 95762295679026644988874955)
  ·
    refine ⟨143643443518539967483312433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95762295679026644988874955 143643443518539967483312433)
    ·
      refine ⟨107732582638904975612484325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143643443518539967483312433 107732582638904975612484325)
      ·
        refine ⟨20199859244794682927340811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107732582638904975612484325 20199859244794682927340811)
        ·
          refine ⟨30299788867192024391011217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20199859244794682927340811 30299788867192024391011217)
          ·
            refine ⟨22724841650394018293258413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30299788867192024391011217 22724841650394018293258413)
            ·
              refine ⟨8521815618897756859971905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22724841650394018293258413 8521815618897756859971905)
              ·
                refine ⟨6391361714173317644978929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8521815618897756859971905 6391361714173317644978929)
                ·
                  refine ⟨4793521285629988233734197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391361714173317644978929 4793521285629988233734197)
                  ·
                    refine ⟨449392620527811396912581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4793521285629988233734197 449392620527811396912581)
                    ·
                      rfl

theorem cell23_2625567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_2625567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625567 prefixEnd_2625567 := by exact prefixLift 2625567
  have htrace : WordTrace (prefixWord ++ tailWord_2625567) baseStart_2625567 baseEnd_2625567 := by
    simpa [prefixWord, tailWord_2625567, baseEnd_2625567] using wordTrace_append hprefix tailTrace_2625567
  have hstable : (prefixWord ++ tailWord_2625567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625567).length < 2 ^ (prefixWord ++ tailWord_2625567).sum := by decide
  have hdescent : baseEnd_2625567 < baseStart_2625567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625580 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_2625580 : Nat := 118140960795 + 2625580 * 2 ^ 59
def prefixEnd_2625580 : Nat := 4983230072969 + 3 ^ 40 * 2625580 * 2
def baseEnd_2625580 : Nat := 449394845610647546625061

theorem tailTrace_2625580 : CollatzResearch.WordTrace tailWord_2625580 prefixEnd_2625580 449394845610647546625061 := by
  unfold tailWord_2625580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881384913989774104549097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63841846551986365472732129 47881384913989774104549097)
  ·
    refine ⟨35911038685492330578411823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47881384913989774104549097 35911038685492330578411823)
    ·
      refine ⟨53866558028238495867617735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35911038685492330578411823 53866558028238495867617735)
      ·
        refine ⟨80799837042357743801426603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53866558028238495867617735 80799837042357743801426603)
        ·
          refine ⟨121199755563536615702139905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80799837042357743801426603 121199755563536615702139905)
          ·
            refine ⟨90899816672652461776604929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121199755563536615702139905 90899816672652461776604929)
            ·
              refine ⟨68174862504489346332453697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90899816672652461776604929 68174862504489346332453697)
              ·
                refine ⟨51131146878367009749340273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68174862504489346332453697 51131146878367009749340273)
                ·
                  refine ⟨38348360158775257312005205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51131146878367009749340273 38348360158775257312005205)
                  ·
                    refine ⟨449394845610647546625061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38348360158775257312005205 449394845610647546625061)
                    ·
                      rfl

theorem cell23_2625580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_2625580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625580 prefixEnd_2625580 := by exact prefixLift 2625580
  have htrace : WordTrace (prefixWord ++ tailWord_2625580) baseStart_2625580 baseEnd_2625580 := by
    simpa [prefixWord, tailWord_2625580, baseEnd_2625580] using wordTrace_append hprefix tailTrace_2625580
  have hstable : (prefixWord ++ tailWord_2625580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625580).length < 2 ^ (prefixWord ++ tailWord_2625580).sum := by decide
  have hdescent : baseEnd_2625580 < baseStart_2625580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625624 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2625624 : Nat := 118140960795 + 2625624 * 2 ^ 59
def prefixEnd_2625624 : Nat := 4983230072969 + 3 ^ 40 * 2625624 * 2
def baseEnd_2625624 : Nat := 1348207129980740467724981

theorem tailTrace_2625624 : CollatzResearch.WordTrace tailWord_2625624 prefixEnd_2625624 1348207129980740467724981 := by
  unfold tailWord_2625624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47882187319910071861849963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63842916426546762482466617 47882187319910071861849963)
  ·
    refine ⟨71823280979865107792774945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47882187319910071861849963 71823280979865107792774945)
    ·
      refine ⟨53867460734898830844581209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71823280979865107792774945 53867460734898830844581209)
      ·
        refine ⟨40400595551174123133435907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53867460734898830844581209 40400595551174123133435907)
        ·
          refine ⟨60600893326761184700153861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40400595551174123133435907 60600893326761184700153861)
          ·
            refine ⟨11362667498767722131278849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60600893326761184700153861 11362667498767722131278849)
            ·
              refine ⟨8522000624075791598459137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11362667498767722131278849 8522000624075791598459137)
              ·
                refine ⟨6391500468056843698844353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8522000624075791598459137 6391500468056843698844353)
                ·
                  refine ⟨4793625351042632774133265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6391500468056843698844353 4793625351042632774133265)
                  ·
                    refine ⟨3595219013281974580599949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4793625351042632774133265 3595219013281974580599949)
                    ·
                      refine ⟨1348207129980740467724981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3595219013281974580599949 1348207129980740467724981)
                      ·
                        rfl

theorem cell23_2625624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2625624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625624 prefixEnd_2625624 := by exact prefixLift 2625624
  have htrace : WordTrace (prefixWord ++ tailWord_2625624) baseStart_2625624 baseEnd_2625624 := by
    simpa [prefixWord, tailWord_2625624, baseEnd_2625624] using wordTrace_append hprefix tailTrace_2625624
  have hstable : (prefixWord ++ tailWord_2625624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625624).length < 2 ^ (prefixWord ++ tailWord_2625624).sum := by decide
  have hdescent : baseEnd_2625624 < baseStart_2625624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625678 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_2625678 : Nat := 118140960795 + 2625678 * 2 ^ 59
def prefixEnd_2625678 : Nat := 4983230072969 + 3 ^ 40 * 2625678 * 2
def baseEnd_2625678 : Nat := 149803873104009250716637

theorem tailTrace_2625678 : CollatzResearch.WordTrace tailWord_2625678 prefixEnd_2625678 149803873104009250716637 := by
  unfold tailWord_2625678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970793022703063868270711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63844229454416340630777125 11970793022703063868270711)
  ·
    refine ⟨17956189534054595802406067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11970793022703063868270711 17956189534054595802406067)
    ·
      refine ⟨26934284301081893703609101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17956189534054595802406067 26934284301081893703609101)
      ·
        refine ⟨10100356612905710138853413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26934284301081893703609101 10100356612905710138853413)
        ·
          refine ⟨1893816864919820651035015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10100356612905710138853413 1893816864919820651035015)
          ·
            refine ⟨2840725297379730976552523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893816864919820651035015 2840725297379730976552523)
            ·
              refine ⟨4261087946069596464828785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840725297379730976552523 4261087946069596464828785)
              ·
                refine ⟨3195815959552197348621589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261087946069596464828785 3195815959552197348621589)
                ·
                  refine ⟨149803873104009250716637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3195815959552197348621589 149803873104009250716637)
                  ·
                    rfl

theorem cell23_2625678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_2625678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625678 prefixEnd_2625678 := by exact prefixLift 2625678
  have htrace : WordTrace (prefixWord ++ tailWord_2625678) baseStart_2625678 baseEnd_2625678 := by
    simpa [prefixWord, tailWord_2625678, baseEnd_2625678] using wordTrace_append hprefix tailTrace_2625678
  have hstable : (prefixWord ++ tailWord_2625678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625678).length < 2 ^ (prefixWord ++ tailWord_2625678).sum := by decide
  have hdescent : baseEnd_2625678 < baseStart_2625678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625688 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2625688 : Nat := 118140960795 + 2625688 * 2 ^ 59
def prefixEnd_2625688 : Nat := 4983230072969 + 3 ^ 40 * 2625688 * 2
def baseEnd_2625688 : Nat := 1348239992742628217324687

theorem tailTrace_2625688 : CollatzResearch.WordTrace tailWord_2625688 prefixEnd_2625688 1348239992742628217324687 := by
  unfold tailWord_2625688
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883354455794141327014859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63844472607725521769353145 47883354455794141327014859)
  ·
    refine ⟨71825031683691211990522289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47883354455794141327014859 71825031683691211990522289)
    ·
      refine ⟨53868773762768408992891717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71825031683691211990522289 53868773762768408992891717)
      ·
        refine ⟨10100395080519076686167197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53868773762768408992891717 10100395080519076686167197)
        ·
          refine ⟨3787648155194653757312699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10100395080519076686167197 3787648155194653757312699)
          ·
            refine ⟨5681472232791980635969049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787648155194653757312699 5681472232791980635969049)
            ·
              refine ⟨4261104174593985476976787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681472232791980635969049 4261104174593985476976787)
              ·
                refine ⟨6391656261890978215465181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4261104174593985476976787 6391656261890978215465181)
                ·
                  refine ⟨2396871098209116830799443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6391656261890978215465181 2396871098209116830799443)
                  ·
                    refine ⟨3595306647313675246199165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396871098209116830799443 3595306647313675246199165)
                    ·
                      refine ⟨1348239992742628217324687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3595306647313675246199165 1348239992742628217324687)
                      ·
                        rfl

theorem cell23_2625688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2625688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625688 prefixEnd_2625688 := by exact prefixLift 2625688
  have htrace : WordTrace (prefixWord ++ tailWord_2625688) baseStart_2625688 baseEnd_2625688 := by
    simpa [prefixWord, tailWord_2625688, baseEnd_2625688] using wordTrace_append hprefix tailTrace_2625688
  have hstable : (prefixWord ++ tailWord_2625688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625688).length < 2 ^ (prefixWord ++ tailWord_2625688).sum := by decide
  have hdescent : baseEnd_2625688 < baseStart_2625688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625716 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2625716 : Nat := 118140960795 + 2625716 * 2 ^ 59
def prefixEnd_2625716 : Nat := 4983230072969 + 3 ^ 40 * 2625716 * 2
def baseEnd_2625716 : Nat := 449418123400318035924853

theorem tailTrace_2625716 : CollatzResearch.WordTrace tailWord_2625716 prefixEnd_2625716 449418123400318035924853 := by
  unfold tailWord_2625716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47883865077743421718024501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63845153436991228957366001 47883865077743421718024501)
  ·
    refine ⟨4489112351038445786064797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47883865077743421718024501 4489112351038445786064797)
    ·
      refine ⟨1683417131639417169774299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4489112351038445786064797 1683417131639417169774299)
      ·
        refine ⟨2525125697459125754661449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683417131639417169774299 2525125697459125754661449)
        ·
          refine ⟨1893844273094344315996087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525125697459125754661449 1893844273094344315996087)
          ·
            refine ⟨2840766409641516473994131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893844273094344315996087 2840766409641516473994131)
            ·
              refine ⟨4261149614462274710991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840766409641516473994131 4261149614462274710991197)
              ·
                refine ⟨1597931105423353016621699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4261149614462274710991197 1597931105423353016621699)
                ·
                  refine ⟨2396896658135029524932549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597931105423353016621699 2396896658135029524932549)
                  ·
                    refine ⟨449418123400318035924853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396896658135029524932549 449418123400318035924853)
                    ·
                      rfl

theorem cell23_2625716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2625716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625716 prefixEnd_2625716 := by exact prefixLift 2625716
  have htrace : WordTrace (prefixWord ++ tailWord_2625716) baseStart_2625716 baseEnd_2625716 := by
    simpa [prefixWord, tailWord_2625716, baseEnd_2625716] using wordTrace_append hprefix tailTrace_2625716
  have hstable : (prefixWord ++ tailWord_2625716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625716).length < 2 ^ (prefixWord ++ tailWord_2625716).sum := by decide
  have hdescent : baseEnd_2625716 < baseStart_2625716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625771 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 3, 3, 2]
def baseStart_2625771 : Nat := 118140960795 + 2625771 * 2 ^ 59
def prefixEnd_2625771 : Nat := 4983230072969 + 3 ^ 40 * 2625771 * 2
def baseEnd_2625771 : Nat := 1348282611636951392586805

theorem tailTrace_2625771 : CollatzResearch.WordTrace tailWord_2625771 prefixEnd_2625771 1348282611636951392586805 := by
  unfold tailWord_2625771
  simp only [CollatzResearch.WordTrace]
  refine ⟨95769736170287587829301167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63846490780191725219534111 95769736170287587829301167)
  ·
    refine ⟨143654604255431381743951751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95769736170287587829301167 143654604255431381743951751)
    ·
      refine ⟨215481906383147072615927627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143654604255431381743951751 215481906383147072615927627)
      ·
        refine ⟨323222859574720608923891441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215481906383147072615927627 323222859574720608923891441)
        ·
          refine ⟨242417144681040456692918581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323222859574720608923891441 242417144681040456692918581)
          ·
            refine ⟨22726607313847542814961117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242417144681040456692918581 22726607313847542814961117)
            ·
              refine ⟨8522477742692828555610419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22726607313847542814961117 8522477742692828555610419)
              ·
                refine ⟨12783716614039242833415629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8522477742692828555610419 12783716614039242833415629)
                ·
                  refine ⟨4793893730264716062530861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12783716614039242833415629 4793893730264716062530861)
                  ·
                    refine ⟨1797710148849268523449073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4793893730264716062530861 1797710148849268523449073)
                    ·
                      refine ⟨1348282611636951392586805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797710148849268523449073 1348282611636951392586805)
                      ·
                        rfl

theorem cell23_2625771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3, 2].length) (baseStart_2625771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625771 prefixEnd_2625771 := by exact prefixLift 2625771
  have htrace : WordTrace (prefixWord ++ tailWord_2625771) baseStart_2625771 baseEnd_2625771 := by
    simpa [prefixWord, tailWord_2625771, baseEnd_2625771] using wordTrace_append hprefix tailTrace_2625771
  have hstable : (prefixWord ++ tailWord_2625771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625771).length < 2 ^ (prefixWord ++ tailWord_2625771).sum := by decide
  have hdescent : baseEnd_2625771 < baseStart_2625771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625796 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_2625796 : Nat := 118140960795 + 2625796 * 2 ^ 59
def prefixEnd_2625796 : Nat := 4983230072969 + 3 ^ 40 * 2625796 * 2
def baseEnd_2625796 : Nat := 1348295448653313794774191

theorem tailTrace_2625796 : CollatzResearch.WordTrace tailWord_2625796 prefixEnd_2625796 1348295448653313794774191 := by
  unfold tailWord_2625796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47885323997598508549480621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63847098663464678065974161 47885323997598508549480621)
  ·
    refine ⟨17956996499099440706055233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47885323997598508549480621 17956996499099440706055233)
    ·
      refine ⟨13467747374324580529541425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17956996499099440706055233 13467747374324580529541425)
      ·
        refine ⟨10100810530743435397156069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13467747374324580529541425 10100810530743435397156069)
        ·
          refine ⟨1893901974514394136966763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10100810530743435397156069 1893901974514394136966763)
          ·
            refine ⟨2840852961771591205450145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893901974514394136966763 2840852961771591205450145)
            ·
              refine ⟨2130639721328693404087609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840852961771591205450145 2130639721328693404087609)
              ·
                refine ⟨1597979790996520053065707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130639721328693404087609 1597979790996520053065707)
                ·
                  refine ⟨2396969686494780079598561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597979790996520053065707 2396969686494780079598561)
                  ·
                    refine ⟨1797727264871085059698921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2396969686494780079598561 1797727264871085059698921)
                    ·
                      refine ⟨1348295448653313794774191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797727264871085059698921 1348295448653313794774191)
                      ·
                        rfl

theorem cell23_2625796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_2625796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625796 prefixEnd_2625796 := by exact prefixLift 2625796
  have htrace : WordTrace (prefixWord ++ tailWord_2625796) baseStart_2625796 baseEnd_2625796 := by
    simpa [prefixWord, tailWord_2625796, baseEnd_2625796] using wordTrace_append hprefix tailTrace_2625796
  have hstable : (prefixWord ++ tailWord_2625796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625796).length < 2 ^ (prefixWord ++ tailWord_2625796).sum := by decide
  have hdescent : baseEnd_2625796 < baseStart_2625796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625804 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2625804 : Nat := 118140960795 + 2625804 * 2 ^ 59
def prefixEnd_2625804 : Nat := 4983230072969 + 3 ^ 40 * 2625804 * 2
def baseEnd_2625804 : Nat := 1348299556498549763474153

theorem tailTrace_2625804 : CollatzResearch.WordTrace tailWord_2625804 prefixEnd_2625804 1348299556498549763474153 := by
  unfold tailWord_2625804
  simp only [CollatzResearch.WordTrace]
  refine ⟨47885469889584017232626233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63847293186112022976834977 47885469889584017232626233)
  ·
    refine ⟨35914102417188012924469675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47885469889584017232626233 35914102417188012924469675)
    ·
      refine ⟨53871153625782019386704513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35914102417188012924469675 53871153625782019386704513)
      ·
        refine ⟨40403365219336514540028385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53871153625782019386704513 40403365219336514540028385)
        ·
          refine ⟨30302523914502385905021289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40403365219336514540028385 30302523914502385905021289)
          ·
            refine ⟨22726892935876789428765967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30302523914502385905021289 22726892935876789428765967)
            ·
              refine ⟨34090339403815184143148951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22726892935876789428765967 34090339403815184143148951)
              ·
                refine ⟨51135509105722776214723427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34090339403815184143148951 51135509105722776214723427)
                ·
                  refine ⟨76703263658584164322085141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51135509105722776214723427 76703263658584164322085141)
                  ·
                    refine ⟨3595465483996132702597741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76703263658584164322085141 3595465483996132702597741)
                    ·
                      refine ⟨1348299556498549763474153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3595465483996132702597741 1348299556498549763474153)
                      ·
                        rfl

theorem cell23_2625804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2625804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625804 prefixEnd_2625804 := by exact prefixLift 2625804
  have htrace : WordTrace (prefixWord ++ tailWord_2625804) baseStart_2625804 baseEnd_2625804 := by
    simpa [prefixWord, tailWord_2625804, baseEnd_2625804] using wordTrace_append hprefix tailTrace_2625804
  have hstable : (prefixWord ++ tailWord_2625804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625804).length < 2 ^ (prefixWord ++ tailWord_2625804).sum := by decide
  have hdescent : baseEnd_2625804 < baseStart_2625804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625807 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 11]
def baseStart_2625807 : Nat := 118140960795 + 2625807 * 2 ^ 59
def prefixEnd_2625807 : Nat := 4983230072969 + 3 ^ 40 * 2625807 * 2
def baseEnd_2625807 : Nat := 149811232993390361304071

theorem tailTrace_2625807 : CollatzResearch.WordTrace tailWord_2625807 prefixEnd_2625807 149811232993390361304071 := by
  unfold tailWord_2625807
  simp only [CollatzResearch.WordTrace]
  refine ⟨95771049198157165977611675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63847366132104777318407783 95771049198157165977611675)
  ·
    refine ⟨143656573797235748966417513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95771049198157165977611675 143656573797235748966417513)
    ·
      refine ⟨107742430347926811724813135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143656573797235748966417513 107742430347926811724813135)
      ·
        refine ⟨161613645521890217587219703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107742430347926811724813135 161613645521890217587219703)
        ·
          refine ⟨242420468282835326380829555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161613645521890217587219703 242420468282835326380829555)
          ·
            refine ⟨363630702424252989571244333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242420468282835326380829555 363630702424252989571244333)
            ·
              refine ⟨136361513409094871089216625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363630702424252989571244333 136361513409094871089216625)
              ·
                refine ⟨102271135056821153316912469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136361513409094871089216625 102271135056821153316912469)
                ·
                  refine ⟨149811232993390361304071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 102271135056821153316912469 149811232993390361304071)
                  ·
                    rfl

theorem cell23_2625807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 11].length) (baseStart_2625807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625807 prefixEnd_2625807 := by exact prefixLift 2625807
  have htrace : WordTrace (prefixWord ++ tailWord_2625807) baseStart_2625807 baseEnd_2625807 := by
    simpa [prefixWord, tailWord_2625807, baseEnd_2625807] using wordTrace_append hprefix tailTrace_2625807
  have hstable : (prefixWord ++ tailWord_2625807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625807).length < 2 ^ (prefixWord ++ tailWord_2625807).sum := by decide
  have hdescent : baseEnd_2625807 < baseStart_2625807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625824 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 9]
def baseStart_2625824 : Nat := 118140960795 + 2625824 * 2 ^ 59
def prefixEnd_2625824 : Nat := 4983230072969 + 3 ^ 40 * 2625824 * 2
def baseEnd_2625824 : Nat := 149812202901293298358229

theorem tailTrace_2625824 : CollatzResearch.WordTrace tailWord_2625824 prefixEnd_2625824 149812202901293298358229 := by
  unfold tailWord_2625824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47885834619547788940490263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63847779492730385253987017 47885834619547788940490263)
  ·
    refine ⟨71828751929321683410735395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47885834619547788940490263 71828751929321683410735395)
    ·
      refine ⟨107743127893982525116103093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71828751929321683410735395 107743127893982525116103093)
      ·
        refine ⟨10100918240060861729634665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107743127893982525116103093 10100918240060861729634665)
        ·
          refine ⟨7575688680045646297225999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10100918240060861729634665 7575688680045646297225999)
          ·
            refine ⟨11363533020068469445838999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7575688680045646297225999 11363533020068469445838999)
            ·
              refine ⟨17045299530102704168758499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11363533020068469445838999 17045299530102704168758499)
              ·
                refine ⟨25567949295154056253137749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17045299530102704168758499 25567949295154056253137749)
                ·
                  refine ⟨149812202901293298358229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25567949295154056253137749 149812202901293298358229)
                  ·
                    rfl

theorem cell23_2625824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_2625824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625824 prefixEnd_2625824 := by exact prefixLift 2625824
  have htrace : WordTrace (prefixWord ++ tailWord_2625824) baseStart_2625824 baseEnd_2625824 := by
    simpa [prefixWord, tailWord_2625824, baseEnd_2625824] using wordTrace_append hprefix tailTrace_2625824
  have hstable : (prefixWord ++ tailWord_2625824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625824).length < 2 ^ (prefixWord ++ tailWord_2625824).sum := by decide
  have hdescent : baseEnd_2625824 < baseStart_2625824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625864 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2625864 : Nat := 118140960795 + 2625864 * 2 ^ 59
def prefixEnd_2625864 : Nat := 4983230072969 + 3 ^ 40 * 2625864 * 2
def baseEnd_2625864 : Nat := 1348330365337819528723877

theorem tailTrace_2625864 : CollatzResearch.WordTrace tailWord_2625864 prefixEnd_2625864 1348330365337819528723877 := by
  unfold tailWord_2625864
  simp only [CollatzResearch.WordTrace]
  refine ⟨47886564079475332356218323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63848752105967109808291097 47886564079475332356218323)
  ·
    refine ⟨71829846119212998534327485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47886564079475332356218323 71829846119212998534327485)
    ·
      refine ⟨26936192294704874450372807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71829846119212998534327485 26936192294704874450372807)
      ·
        refine ⟨40404288442057311675559211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26936192294704874450372807 40404288442057311675559211)
        ·
          refine ⟨60606432663085967513338817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40404288442057311675559211 60606432663085967513338817)
          ·
            refine ⟨45454824497314475635004113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60606432663085967513338817 45454824497314475635004113)
            ·
              refine ⟨34091118372985856726253085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45454824497314475635004113 34091118372985856726253085)
              ·
                refine ⟨12784169389869696272344907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34091118372985856726253085 12784169389869696272344907)
                ·
                  refine ⟨19176254084804544408517361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784169389869696272344907 19176254084804544408517361)
                  ·
                    refine ⟨14382190563603408306388021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19176254084804544408517361 14382190563603408306388021)
                    ·
                      refine ⟨1348330365337819528723877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14382190563603408306388021 1348330365337819528723877)
                      ·
                        rfl

theorem cell23_2625864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2625864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625864 prefixEnd_2625864 := by exact prefixLift 2625864
  have htrace : WordTrace (prefixWord ++ tailWord_2625864) baseStart_2625864 baseEnd_2625864 := by
    simpa [prefixWord, tailWord_2625864, baseEnd_2625864] using wordTrace_append hprefix tailTrace_2625864
  have hstable : (prefixWord ++ tailWord_2625864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625864).length < 2 ^ (prefixWord ++ tailWord_2625864).sum := by decide
  have hdescent : baseEnd_2625864 < baseStart_2625864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625891 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2625891 : Nat := 118140960795 + 2625891 * 2 ^ 59
def prefixEnd_2625891 : Nat := 4983230072969 + 3 ^ 40 * 2625891 * 2
def baseEnd_2625891 : Nat := 1348344229315490923086253

theorem tailTrace_2625891 : CollatzResearch.WordTrace tailWord_2625891 prefixEnd_2625891 1348344229315490923086253 := by
  unfold tailWord_2625891
  simp only [CollatzResearch.WordTrace]
  refine ⟨95774112929852848323669527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63849408619901898882446351 95774112929852848323669527)
  ·
    refine ⟨143661169394779272485504291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95774112929852848323669527 143661169394779272485504291)
    ·
      refine ⟨215491754092168908728256437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143661169394779272485504291 215491754092168908728256437)
      ·
        refine ⟨20202351946140835193274041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215491754092168908728256437 20202351946140835193274041)
        ·
          refine ⟨15151763959605626394955531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20202351946140835193274041 15151763959605626394955531)
          ·
            refine ⟨22727645939408439592433297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15151763959605626394955531 22727645939408439592433297)
            ·
              refine ⟨17045734454556329694324973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22727645939408439592433297 17045734454556329694324973)
              ·
                refine ⟨6392150420458623635371865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17045734454556329694324973 6392150420458623635371865)
                ·
                  refine ⟨4794112815343967726528899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6392150420458623635371865 4794112815343967726528899)
                  ·
                    refine ⟨7191169223015951589793349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794112815343967726528899 7191169223015951589793349)
                    ·
                      refine ⟨1348344229315490923086253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7191169223015951589793349 1348344229315490923086253)
                      ·
                        rfl

theorem cell23_2625891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2625891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625891 prefixEnd_2625891 := by exact prefixLift 2625891
  have htrace : WordTrace (prefixWord ++ tailWord_2625891) baseStart_2625891 baseEnd_2625891 := by
    simpa [prefixWord, tailWord_2625891, baseEnd_2625891] using wordTrace_append hprefix tailTrace_2625891
  have hstable : (prefixWord ++ tailWord_2625891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625891).length < 2 ^ (prefixWord ++ tailWord_2625891).sum := by decide
  have hdescent : baseEnd_2625891 < baseStart_2625891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625931 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 6]
def baseStart_2625931 : Nat := 118140960795 + 2625931 * 2 ^ 59
def prefixEnd_2625931 : Nat := 4983230072969 + 3 ^ 40 * 2625931 * 2
def baseEnd_2625931 : Nat := 149818307615741196287341

theorem tailTrace_2625931 : CollatzResearch.WordTrace tailWord_2625931 prefixEnd_2625931 149818307615741196287341 := by
  unfold tailWord_2625931
  simp only [CollatzResearch.WordTrace]
  refine ⟨95775571849707935155125647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63850381233138623436750431 95775571849707935155125647)
  ·
    refine ⟨143663357774561902732688471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95775571849707935155125647 143663357774561902732688471)
    ·
      refine ⟨215495036661842854099032707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143663357774561902732688471 215495036661842854099032707)
      ·
        refine ⟨323242554992764281148549061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215495036661842854099032707 323242554992764281148549061)
        ·
          refine ⟨60607979061143302715352949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323242554992764281148549061 60607979061143302715352949)
          ·
            refine ⟨5681998036982184629564339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60607979061143302715352949 5681998036982184629564339)
            ·
              refine ⟨8522997055473276944346509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681998036982184629564339 8522997055473276944346509)
              ·
                refine ⟨3196123895802478854129941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8522997055473276944346509 3196123895802478854129941)
                ·
                  refine ⟨149818307615741196287341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3196123895802478854129941 149818307615741196287341)
                  ·
                    rfl

theorem cell23_2625931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 6].length) (baseStart_2625931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625931 prefixEnd_2625931 := by exact prefixLift 2625931
  have htrace : WordTrace (prefixWord ++ tailWord_2625931) baseStart_2625931 baseEnd_2625931 := by
    simpa [prefixWord, tailWord_2625931, baseEnd_2625931] using wordTrace_append hprefix tailTrace_2625931
  have hstable : (prefixWord ++ tailWord_2625931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625931).length < 2 ^ (prefixWord ++ tailWord_2625931).sum := by decide
  have hdescent : baseEnd_2625931 < baseStart_2625931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625961 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_2625961 : Nat := 118140960795 + 2625961 * 2 ^ 59
def prefixEnd_2625961 : Nat := 4983230072969 + 3 ^ 40 * 2625961 * 2
def baseEnd_2625961 : Nat := 449460057653768549736977

theorem tailTrace_2625961 : CollatzResearch.WordTrace tailWord_2625961 prefixEnd_2625961 449460057653768549736977 := by
  unfold tailWord_2625961
  simp only [CollatzResearch.WordTrace]
  refine ⟨95776666039599250278717737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63851110693066166852478491 95776666039599250278717737)
  ·
    refine ⟨71832499529699437709038303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95776666039599250278717737 71832499529699437709038303)
    ·
      refine ⟨107748749294549156563557455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71832499529699437709038303 107748749294549156563557455)
      ·
        refine ⟨161623123941823734845336183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107748749294549156563557455 161623123941823734845336183)
        ·
          refine ⟨242434685912735602268004275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161623123941823734845336183 242434685912735602268004275)
          ·
            refine ⟨363652028869103403402006413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242434685912735602268004275 363652028869103403402006413)
            ·
              refine ⟨136369510825913776275752405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 363652028869103403402006413 136369510825913776275752405)
              ·
                refine ⟨3196160409982354131462947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136369510825913776275752405 3196160409982354131462947)
                ·
                  refine ⟨4794240614973531197194421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196160409982354131462947 4794240614973531197194421)
                  ·
                    refine ⟨449460057653768549736977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4794240614973531197194421 449460057653768549736977)
                    ·
                      rfl

theorem cell23_2625961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_2625961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625961 prefixEnd_2625961 := by exact prefixLift 2625961
  have htrace : WordTrace (prefixWord ++ tailWord_2625961) baseStart_2625961 baseEnd_2625961 := by
    simpa [prefixWord, tailWord_2625961, baseEnd_2625961] using wordTrace_append hprefix tailTrace_2625961
  have hstable : (prefixWord ++ tailWord_2625961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625961).length < 2 ^ (prefixWord ++ tailWord_2625961).sum := by decide
  have hdescent : baseEnd_2625961 < baseStart_2625961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625965 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2625965 : Nat := 118140960795 + 2625965 * 2 ^ 59
def prefixEnd_2625965 : Nat := 4983230072969 + 3 ^ 40 * 2625965 * 2
def baseEnd_2625965 : Nat := 149820247431547070395657

theorem tailTrace_2625965 : CollatzResearch.WordTrace tailWord_2625965 prefixEnd_2625965 149820247431547070395657 := by
  unfold tailWord_2625965
  simp only [CollatzResearch.WordTrace]
  refine ⟨95776811931584758961863349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63851207954389839307908899 95776811931584758961863349)
  ·
    refine ⟨8979076118586071152674689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95776811931584758961863349 8979076118586071152674689)
    ·
      refine ⟨6734307088939553364506017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8979076118586071152674689 6734307088939553364506017)
      ·
        refine ⟨5050730316704665023379513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6734307088939553364506017 5050730316704665023379513)
        ·
          refine ⟨3788047737528498767534635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5050730316704665023379513 3788047737528498767534635)
          ·
            refine ⟨5682071606292748151301953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788047737528498767534635 5682071606292748151301953)
            ·
              refine ⟨4261553704719561113476465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682071606292748151301953 4261553704719561113476465)
              ·
                refine ⟨3196165278539670835107349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261553704719561113476465 3196165278539670835107349)
                ·
                  refine ⟨149820247431547070395657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3196165278539670835107349 149820247431547070395657)
                  ·
                    rfl

theorem cell23_2625965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2625965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625965 prefixEnd_2625965 := by exact prefixLift 2625965
  have htrace : WordTrace (prefixWord ++ tailWord_2625965) baseStart_2625965 baseEnd_2625965 := by
    simpa [prefixWord, tailWord_2625965, baseEnd_2625965] using wordTrace_append hprefix tailTrace_2625965
  have hstable : (prefixWord ++ tailWord_2625965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625965).length < 2 ^ (prefixWord ++ tailWord_2625965).sum := by decide
  have hdescent : baseEnd_2625965 < baseStart_2625965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625991 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2625991 : Nat := 118140960795 + 2625991 * 2 ^ 59
def prefixEnd_2625991 : Nat := 4983230072969 + 3 ^ 40 * 2625991 * 2
def baseEnd_2625991 : Nat := 449465192460313510611931

theorem tailTrace_2625991 : CollatzResearch.WordTrace tailWord_2625991 prefixEnd_2625991 449465192460313510611931 := by
  unfold tailWord_2625991
  simp only [CollatzResearch.WordTrace]
  refine ⟨95777760229490565402309827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63851840152993710268206551 95777760229490565402309827)
  ·
    refine ⟨143666640344235848103464741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95777760229490565402309827 143666640344235848103464741)
    ·
      refine ⟨26937495064544221519399639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143666640344235848103464741 26937495064544221519399639)
      ·
        refine ⟨40406242596816332279099459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26937495064544221519399639 40406242596816332279099459)
        ·
          refine ⟨60609363895224498418649189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40406242596816332279099459 60609363895224498418649189)
          ·
            refine ⟨11364255730354593453496723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60609363895224498418649189 11364255730354593453496723)
            ·
              refine ⟨17046383595531890180245085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11364255730354593453496723 17046383595531890180245085)
              ·
                refine ⟨6392393848324458817591907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17046383595531890180245085 6392393848324458817591907)
                ·
                  refine ⟨9588590772486688226387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6392393848324458817591907 9588590772486688226387861)
                  ·
                    refine ⟨449465192460313510611931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9588590772486688226387861 449465192460313510611931)
                    ·
                      rfl

theorem cell23_2625991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2625991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625991 prefixEnd_2625991 := by exact prefixLift 2625991
  have htrace : WordTrace (prefixWord ++ tailWord_2625991) baseStart_2625991 baseEnd_2625991 := by
    simpa [prefixWord, tailWord_2625991, baseEnd_2625991] using wordTrace_append hprefix tailTrace_2625991
  have hstable : (prefixWord ++ tailWord_2625991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625991).length < 2 ^ (prefixWord ++ tailWord_2625991).sum := by decide
  have hdescent : baseEnd_2625991 < baseStart_2625991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2625998 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_2625998 : Nat := 118140960795 + 2625998 * 2 ^ 59
def prefixEnd_2625998 : Nat := 4983230072969 + 3 ^ 40 * 2625998 * 2
def baseEnd_2625998 : Nat := 1348399171745522004448261

theorem tailTrace_2625998 : CollatzResearch.WordTrace tailWord_2625998 prefixEnd_2625998 1348399171745522004448261 := by
  unfold tailWord_2625998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972251942558150699726831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63852010360310137065209765 11972251942558150699726831)
  ·
    refine ⟨17958377913837226049590247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11972251942558150699726831 17958377913837226049590247)
    ·
      refine ⟨26937566870755839074385371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17958377913837226049590247 26937566870755839074385371)
      ·
        refine ⟨40406350306133758611578057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26937566870755839074385371 40406350306133758611578057)
        ·
          refine ⟨30304762729600318958683543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40406350306133758611578057 30304762729600318958683543)
          ·
            refine ⟨45457144094400478438025315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30304762729600318958683543 45457144094400478438025315)
            ·
              refine ⟨68185716141600717657037973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45457144094400478438025315 68185716141600717657037973)
              ·
                refine ⟨3196205444137533640173655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68185716141600717657037973 3196205444137533640173655)
                ·
                  refine ⟨4794308166206300460260483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196205444137533640173655 4794308166206300460260483)
                  ·
                    refine ⟨7191462249309450690390725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794308166206300460260483 7191462249309450690390725)
                    ·
                      refine ⟨1348399171745522004448261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7191462249309450690390725 1348399171745522004448261)
                      ·
                        rfl

theorem cell23_2625998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_2625998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2625998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2625998 prefixEnd_2625998 := by exact prefixLift 2625998
  have htrace : WordTrace (prefixWord ++ tailWord_2625998) baseStart_2625998 baseEnd_2625998 := by
    simpa [prefixWord, tailWord_2625998, baseEnd_2625998] using wordTrace_append hprefix tailTrace_2625998
  have hstable : (prefixWord ++ tailWord_2625998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2625998).length < 2 ^ (prefixWord ++ tailWord_2625998).sum := by decide
  have hdescent : baseEnd_2625998 < baseStart_2625998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2625998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626002 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2626002 : Nat := 118140960795 + 2626002 * 2 ^ 59
def prefixEnd_2626002 : Nat := 4983230072969 + 3 ^ 40 * 2626002 * 2
def baseEnd_2626002 : Nat := 1348401225668139988798243

theorem tailTrace_2626002 : CollatzResearch.WordTrace tailWord_2626002 prefixEnd_2626002 1348401225668139988798243 := by
  unfold tailWord_2626002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23944540358112678570240065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63852107621633809520640173 23944540358112678570240065)
  ·
    refine ⟨17958405268584508927680049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23944540358112678570240065 17958405268584508927680049)
    ·
      refine ⟨13468803951438381695760037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17958405268584508927680049 13468803951438381695760037)
      ·
        refine ⟨2525400740894696567955007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13468803951438381695760037 2525400740894696567955007)
        ·
          refine ⟨3788101111342044851932511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525400740894696567955007 3788101111342044851932511)
          ·
            refine ⟨5682151667013067277898767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788101111342044851932511 5682151667013067277898767)
            ·
              refine ⟨8523227500519600916848151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682151667013067277898767 8523227500519600916848151)
              ·
                refine ⟨12784841250779401375272227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523227500519600916848151 12784841250779401375272227)
                ·
                  refine ⟨19177261876169102062908341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12784841250779401375272227 19177261876169102062908341)
                  ·
                    refine ⟨1797868300890853318397657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19177261876169102062908341 1797868300890853318397657)
                    ·
                      refine ⟨1348401225668139988798243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797868300890853318397657 1348401225668139988798243)
                      ·
                        rfl

theorem cell23_2626002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2626002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626002 prefixEnd_2626002 := by exact prefixLift 2626002
  have htrace : WordTrace (prefixWord ++ tailWord_2626002) baseStart_2626002 baseEnd_2626002 := by
    simpa [prefixWord, tailWord_2626002, baseEnd_2626002] using wordTrace_append hprefix tailTrace_2626002
  have hstable : (prefixWord ++ tailWord_2626002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626002).length < 2 ^ (prefixWord ++ tailWord_2626002).sum := by decide
  have hdescent : baseEnd_2626002 < baseStart_2626002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626015 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 1, 1, 4]
def baseStart_2626015 : Nat := 118140960795 + 2626015 * 2 ^ 59
def prefixEnd_2626015 : Nat := 4983230072969 + 3 ^ 40 * 2626015 * 2
def baseEnd_2626015 : Nat := 1348407900916648437935683

theorem tailTrace_2626015 : CollatzResearch.WordTrace tailWord_2626015 prefixEnd_2626015 1348407900916648437935683 := by
  unfold tailWord_2626015
  simp only [CollatzResearch.WordTrace]
  refine ⟨95778635581403617501183499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63852423720935745000788999 95778635581403617501183499)
  ·
    refine ⟨143667953372105426251775249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95778635581403617501183499 143667953372105426251775249)
    ·
      refine ⟨107750965029079069688831437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143667953372105426251775249 107750965029079069688831437)
      ·
        refine ⟨40406611885904651133311789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107750965029079069688831437 40406611885904651133311789)
        ·
          refine ⟨15152479457214244174991921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40406611885904651133311789 15152479457214244174991921)
          ·
            refine ⟨11364359592910683131243941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15152479457214244174991921 11364359592910683131243941)
            ·
              refine ⟨2130817423670753087108239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11364359592910683131243941 2130817423670753087108239)
              ·
                refine ⟨3196226135506129630662359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130817423670753087108239 3196226135506129630662359)
                ·
                  refine ⟨4794339203259194445993539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196226135506129630662359 4794339203259194445993539)
                  ·
                    refine ⟨7191508804888791668990309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794339203259194445993539 7191508804888791668990309)
                    ·
                      refine ⟨1348407900916648437935683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7191508804888791668990309 1348407900916648437935683)
                      ·
                        rfl

theorem cell23_2626015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_2626015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626015 prefixEnd_2626015 := by exact prefixLift 2626015
  have htrace : WordTrace (prefixWord ++ tailWord_2626015) baseStart_2626015 baseEnd_2626015 := by
    simpa [prefixWord, tailWord_2626015, baseEnd_2626015] using wordTrace_append hprefix tailTrace_2626015
  have hstable : (prefixWord ++ tailWord_2626015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626015).length < 2 ^ (prefixWord ++ tailWord_2626015).sum := by decide
  have hdescent : baseEnd_2626015 < baseStart_2626015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626032 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 1, 2, 2]
def baseStart_2626032 : Nat := 118140960795 + 2626032 * 2 ^ 59
def prefixEnd_2626032 : Nat := 4983230072969 + 3 ^ 40 * 2626032 * 2
def baseEnd_2626032 : Nat := 1348416630087774871423105

theorem tailTrace_2626032 : CollatzResearch.WordTrace tailWord_2626032 prefixEnd_2626032 1348416630087774871423105 := by
  unfold tailWord_2626032
  simp only [CollatzResearch.WordTrace]
  refine ⟨47889627811171014702276175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63852837081561352936368233 47889627811171014702276175)
  ·
    refine ⟨71834441716756522053414263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47889627811171014702276175 71834441716756522053414263)
    ·
      refine ⟨107751662575134783080121395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71834441716756522053414263 107751662575134783080121395)
      ·
        refine ⟨161627493862702174620182093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107751662575134783080121395 161627493862702174620182093)
        ·
          refine ⟨60610310198513315482568285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161627493862702174620182093 60610310198513315482568285)
          ·
            refine ⟨22728866324442493305963107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60610310198513315482568285 22728866324442493305963107)
            ·
              refine ⟨34093299486663739958944661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22728866324442493305963107 34093299486663739958944661)
              ·
                refine ⟨1598123413437362810575531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34093299486663739958944661 1598123413437362810575531)
                ·
                  refine ⟨2397185120156044215863297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598123413437362810575531 2397185120156044215863297)
                  ·
                    refine ⟨1797888840117033161897473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2397185120156044215863297 1797888840117033161897473)
                    ·
                      refine ⟨1348416630087774871423105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797888840117033161897473 1348416630087774871423105)
                      ·
                        rfl

theorem cell23_2626032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 2, 2].length) (baseStart_2626032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626032 prefixEnd_2626032 := by exact prefixLift 2626032
  have htrace : WordTrace (prefixWord ++ tailWord_2626032) baseStart_2626032 baseEnd_2626032 := by
    simpa [prefixWord, tailWord_2626032, baseEnd_2626032] using wordTrace_append hprefix tailTrace_2626032
  have hstable : (prefixWord ++ tailWord_2626032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626032).length < 2 ^ (prefixWord ++ tailWord_2626032).sum := by decide
  have hdescent : baseEnd_2626032 < baseStart_2626032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626052 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2626052 : Nat := 118140960795 + 2626052 * 2 ^ 59
def prefixEnd_2626052 : Nat := 4983230072969 + 3 ^ 40 * 2626052 * 2
def baseEnd_2626052 : Nat := 1348426899700864793173013

theorem tailTrace_2626052 : CollatzResearch.WordTrace tailWord_2626052 prefixEnd_2626052 1348426899700864793173013 := by
  unfold tailWord_2626052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47889992541134786410140205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63853323388179715213520273 47889992541134786410140205)
  ·
    refine ⟨17958747202925544903802577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47889992541134786410140205 17958747202925544903802577)
    ·
      refine ⟨13469060402194158677851933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17958747202925544903802577 13469060402194158677851933)
      ·
        refine ⟨5050897650822809504194475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13469060402194158677851933 5050897650822809504194475)
        ·
          refine ⟨7576346476234214256291713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050897650822809504194475 7576346476234214256291713)
          ·
            refine ⟨5682259857175660692218785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576346476234214256291713 5682259857175660692218785)
            ·
              refine ⟨4261694892881745519164089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682259857175660692218785 4261694892881745519164089)
              ·
                refine ⟨3196271169661309139373067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261694892881745519164089 3196271169661309139373067)
                ·
                  refine ⟨4794406754491963709059601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196271169661309139373067 4794406754491963709059601)
                  ·
                    refine ⟨3595805065868972781794701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4794406754491963709059601 3595805065868972781794701)
                    ·
                      refine ⟨1348426899700864793173013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3595805065868972781794701 1348426899700864793173013)
                      ·
                        rfl

theorem cell23_2626052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2626052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626052 prefixEnd_2626052 := by exact prefixLift 2626052
  have htrace : WordTrace (prefixWord ++ tailWord_2626052) baseStart_2626052 baseEnd_2626052 := by
    simpa [prefixWord, tailWord_2626052, baseEnd_2626052] using wordTrace_append hprefix tailTrace_2626052
  have hstable : (prefixWord ++ tailWord_2626052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626052).length < 2 ^ (prefixWord ++ tailWord_2626052).sum := by decide
  have hdescent : baseEnd_2626052 < baseStart_2626052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626055 : List Nat := [1, 1, 4, 3, 3, 2, 2, 7]
def baseStart_2626055 : Nat := 118140960795 + 2626055 * 2 ^ 59
def prefixEnd_2626055 : Nat := 4983230072969 + 3 ^ 40 * 2626055 * 2
def baseEnd_2626055 : Nat := 49941794079364010423537

theorem tailTrace_2626055 : CollatzResearch.WordTrace tailWord_2626055 prefixEnd_2626055 49941794079364010423537 := by
  unfold tailWord_2626055
  simp only [CollatzResearch.WordTrace]
  refine ⟨95780094501258704332639619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63853396334172469555093079 95780094501258704332639619)
  ·
    refine ⟨143670141751888056498959429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95780094501258704332639619 143670141751888056498959429)
    ·
      refine ⟨26938151578479010593554893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143670141751888056498959429 26938151578479010593554893)
      ·
        refine ⟨10101806841929628972583085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26938151578479010593554893 10101806841929628972583085)
        ·
          refine ⟨3788177565723610864718657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10101806841929628972583085 3788177565723610864718657)
          ·
            refine ⟨2841133174292708148538993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788177565723610864718657 2841133174292708148538993)
            ·
              refine ⟨2130849880719531111404245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841133174292708148538993 2130849880719531111404245)
              ·
                refine ⟨49941794079364010423537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2130849880719531111404245 49941794079364010423537)
                ·
                  rfl

theorem cell23_2626055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 7].length) (baseStart_2626055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626055 prefixEnd_2626055 := by exact prefixLift 2626055
  have htrace : WordTrace (prefixWord ++ tailWord_2626055) baseStart_2626055 baseEnd_2626055 := by
    simpa [prefixWord, tailWord_2626055, baseEnd_2626055] using wordTrace_append hprefix tailTrace_2626055
  have hstable : (prefixWord ++ tailWord_2626055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626055).length < 2 ^ (prefixWord ++ tailWord_2626055).sum := by decide
  have hdescent : baseEnd_2626055 < baseStart_2626055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626093 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2626093 : Nat := 118140960795 + 2626093 * 2 ^ 59
def prefixEnd_2626093 : Nat := 4983230072969 + 3 ^ 40 * 2626093 * 2
def baseEnd_2626093 : Nat := 449482650802566377586775

theorem tailTrace_2626093 : CollatzResearch.WordTrace tailWord_2626093 prefixEnd_2626093 449482650802566377586775 := by
  unfold tailWord_2626093
  simp only [CollatzResearch.WordTrace]
  refine ⟨95781480475121036822522933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63854320316747357881681955 95781480475121036822522933)
  ·
    refine ⟨8979513794542597202111525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95781480475121036822522933 8979513794542597202111525)
    ·
      refine ⟨1683658836476736975395911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8979513794542597202111525 1683658836476736975395911)
      ·
        refine ⟨2525488254715105463093867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683658836476736975395911 2525488254715105463093867)
        ·
          refine ⟨3788232382072658194640801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525488254715105463093867 3788232382072658194640801)
          ·
            refine ⟨2841174286554493645980601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788232382072658194640801 2841174286554493645980601)
            ·
              refine ⟨2130880714915870234485451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841174286554493645980601 2130880714915870234485451)
              ·
                refine ⟨3196321072373805351728177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130880714915870234485451 3196321072373805351728177)
                ·
                  refine ⟨2397240804280354013796133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3196321072373805351728177 2397240804280354013796133)
                  ·
                    refine ⟨449482650802566377586775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397240804280354013796133 449482650802566377586775)
                    ·
                      rfl

theorem cell23_2626093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2626093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626093 prefixEnd_2626093 := by exact prefixLift 2626093
  have htrace : WordTrace (prefixWord ++ tailWord_2626093) baseStart_2626093 baseEnd_2626093 := by
    simpa [prefixWord, tailWord_2626093, baseEnd_2626093] using wordTrace_append hprefix tailTrace_2626093
  have hstable : (prefixWord ++ tailWord_2626093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626093).length < 2 ^ (prefixWord ++ tailWord_2626093).sum := by decide
  have hdescent : baseEnd_2626093 < baseStart_2626093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626105 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2626105 : Nat := 118140960795 + 2626105 * 2 ^ 59
def prefixEnd_2626105 : Nat := 4983230072969 + 3 ^ 40 * 2626105 * 2
def baseEnd_2626105 : Nat := 1348454114175553085810269

theorem tailTrace_2626105 : CollatzResearch.WordTrace tailWord_2626105 prefixEnd_2626105 1348454114175553085810269 := by
  unfold tailWord_2626105
  simp only [CollatzResearch.WordTrace]
  refine ⟨95781918151077562871959769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63854612100718375247973179 95781918151077562871959769)
  ·
    refine ⟨71836438613308172153969827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95781918151077562871959769 71836438613308172153969827)
    ·
      refine ⟨107754657919962258230954741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71836438613308172153969827 107754657919962258230954741)
      ·
        refine ⟨10101999179996461709152007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107754657919962258230954741 10101999179996461709152007)
        ·
          refine ⟨15152998769994692563728011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10101999179996461709152007 15152998769994692563728011)
          ·
            refine ⟨22729498154992038845592017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15152998769994692563728011 22729498154992038845592017)
            ·
              refine ⟨17047123616244029134194013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22729498154992038845592017 17047123616244029134194013)
              ·
                refine ⟨6392671356091510925322755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17047123616244029134194013 6392671356091510925322755)
                ·
                  refine ⟨9589007034137266387984133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6392671356091510925322755 9589007034137266387984133)
                  ·
                    refine ⟨1797938818900737447747025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9589007034137266387984133 1797938818900737447747025)
                    ·
                      refine ⟨1348454114175553085810269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797938818900737447747025 1348454114175553085810269)
                      ·
                        rfl

theorem cell23_2626105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2626105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626105 prefixEnd_2626105 := by exact prefixLift 2626105
  have htrace : WordTrace (prefixWord ++ tailWord_2626105) baseStart_2626105 baseEnd_2626105 := by
    simpa [prefixWord, tailWord_2626105, baseEnd_2626105] using wordTrace_append hprefix tailTrace_2626105
  have hstable : (prefixWord ++ tailWord_2626105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626105).length < 2 ^ (prefixWord ++ tailWord_2626105).sum := by decide
  have hdescent : baseEnd_2626105 < baseStart_2626105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626108 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2626108 : Nat := 118140960795 + 2626108 * 2 ^ 59
def prefixEnd_2626108 : Nat := 4983230072969 + 3 ^ 40 * 2626108 * 2
def baseEnd_2626108 : Nat := 1348455654617516574072755

theorem tailTrace_2626108 : CollatzResearch.WordTrace tailWord_2626108 prefixEnd_2626108 1348455654617516574072755 := by
  unfold tailWord_2626108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47891013785033347192159489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63854685046711129589545985 47891013785033347192159489)
  ·
    refine ⟨35918260338775010394119617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47891013785033347192159489 35918260338775010394119617)
    ·
      refine ⟨26938695254081257795589713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35918260338775010394119617 26938695254081257795589713)
      ·
        refine ⟨20204021440560943346692285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26938695254081257795589713 20204021440560943346692285)
        ·
          refine ⟨7576508040210353755009607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20204021440560943346692285 7576508040210353755009607)
          ·
            refine ⟨11364762060315530632514411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576508040210353755009607 11364762060315530632514411)
            ·
              refine ⟨17047143090473295948771617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11364762060315530632514411 17047143090473295948771617)
              ·
                refine ⟨12785357317854971961578713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17047143090473295948771617 12785357317854971961578713)
                ·
                  refine ⟨9589017988391228971184035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12785357317854971961578713 9589017988391228971184035)
                  ·
                    refine ⟨14383526982586843456776053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9589017988391228971184035 14383526982586843456776053)
                    ·
                      refine ⟨1348455654617516574072755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14383526982586843456776053 1348455654617516574072755)
                      ·
                        rfl

theorem cell23_2626108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2626108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626108 prefixEnd_2626108 := by exact prefixLift 2626108
  have htrace : WordTrace (prefixWord ++ tailWord_2626108) baseStart_2626108 baseEnd_2626108 := by
    simpa [prefixWord, tailWord_2626108, baseEnd_2626108] using wordTrace_append hprefix tailTrace_2626108
  have hstable : (prefixWord ++ tailWord_2626108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626108).length < 2 ^ (prefixWord ++ tailWord_2626108).sum := by decide
  have hdescent : baseEnd_2626108 < baseStart_2626108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626109 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2626109 : Nat := 118140960795 + 2626109 * 2 ^ 59
def prefixEnd_2626109 : Nat := 4983230072969 + 3 ^ 40 * 2626109 * 2
def baseEnd_2626109 : Nat := 1348456168098171070160251

theorem tailTrace_2626109 : CollatzResearch.WordTrace tailWord_2626109 prefixEnd_2626109 1348456168098171070160251 := by
  unfold tailWord_2626109
  simp only [CollatzResearch.WordTrace]
  refine ⟨95782064043063071555105381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63854709362042047703403587 95782064043063071555105381)
  ·
    refine ⟨17959137008074325916582259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95782064043063071555105381 17959137008074325916582259)
    ·
      refine ⟨26938705512111488874873389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17959137008074325916582259 26938705512111488874873389)
      ·
        refine ⟨10102014567041808328077521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26938705512111488874873389 10102014567041808328077521)
        ·
          refine ⟨7576510925281356246058141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10102014567041808328077521 7576510925281356246058141)
          ·
            refine ⟨2841191596980508592271803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7576510925281356246058141 2841191596980508592271803)
            ·
              refine ⟨4261787395470762888407705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841191596980508592271803 4261787395470762888407705)
              ·
                refine ⟨3196340546603072166305779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261787395470762888407705 3196340546603072166305779)
                ·
                  refine ⟨4794510819904608249458669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196340546603072166305779 4794510819904608249458669)
                  ·
                    refine ⟨1797941557464228093547001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4794510819904608249458669 1797941557464228093547001)
                    ·
                      refine ⟨1348456168098171070160251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797941557464228093547001 1348456168098171070160251)
                      ·
                        rfl

theorem cell23_2626109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2626109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626109 prefixEnd_2626109 := by exact prefixLift 2626109
  have htrace : WordTrace (prefixWord ++ tailWord_2626109) baseStart_2626109 baseEnd_2626109 := by
    simpa [prefixWord, tailWord_2626109, baseEnd_2626109] using wordTrace_append hprefix tailTrace_2626109
  have hstable : (prefixWord ++ tailWord_2626109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626109).length < 2 ^ (prefixWord ++ tailWord_2626109).sum := by decide
  have hdescent : baseEnd_2626109 < baseStart_2626109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626111 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 9]
def baseStart_2626111 : Nat := 118140960795 + 2626111 * 2 ^ 59
def prefixEnd_2626111 : Nat := 4983230072969 + 3 ^ 40 * 2626111 * 2
def baseEnd_2626111 : Nat := 149828577228831118037249

theorem tailTrace_2626111 : CollatzResearch.WordTrace tailWord_2626111 prefixEnd_2626111 149828577228831118037249 := by
  unfold tailWord_2626111
  simp only [CollatzResearch.WordTrace]
  refine ⟨95782136989055825896678187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63854757992703883931118791 95782136989055825896678187)
  ·
    refine ⟨143673205483583738845017281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95782136989055825896678187 143673205483583738845017281)
    ·
      refine ⟨107754904112687804133762961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143673205483583738845017281 107754904112687804133762961)
      ·
        refine ⟨80816178084515853100322221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107754904112687804133762961 80816178084515853100322221)
        ·
          refine ⟨30306066781693444912620833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80816178084515853100322221 30306066781693444912620833)
          ·
            refine ⟨22729550086270083684465625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30306066781693444912620833 22729550086270083684465625)
            ·
              refine ⟨17047162564702562763349219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22729550086270083684465625 17047162564702562763349219)
              ·
                refine ⟨25570743847053844145023829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17047162564702562763349219 25570743847053844145023829)
                ·
                  refine ⟨149828577228831118037249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25570743847053844145023829 149828577228831118037249)
                  ·
                    rfl

theorem cell23_2626111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 9].length) (baseStart_2626111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626111 prefixEnd_2626111 := by exact prefixLift 2626111
  have htrace : WordTrace (prefixWord ++ tailWord_2626111) baseStart_2626111 baseEnd_2626111 := by
    simpa [prefixWord, tailWord_2626111, baseEnd_2626111] using wordTrace_append hprefix tailTrace_2626111
  have hstable : (prefixWord ++ tailWord_2626111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626111).length < 2 ^ (prefixWord ++ tailWord_2626111).sum := by decide
  have hdescent : baseEnd_2626111 < baseStart_2626111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626125 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2626125 : Nat := 118140960795 + 2626125 * 2 ^ 59
def prefixEnd_2626125 : Nat := 4983230072969 + 3 ^ 40 * 2626125 * 2
def baseEnd_2626125 : Nat := 1348464383788643007560177

theorem tailTrace_2626125 : CollatzResearch.WordTrace tailWord_2626125 prefixEnd_2626125 1348464383788643007560177 := by
  unfold tailWord_2626125
  simp only [CollatzResearch.WordTrace]
  refine ⟨95782647611005106287687829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63855098407336737525125219 95782647611005106287687829)
  ·
    refine ⟨4489811606765864357235367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95782647611005106287687829 4489811606765864357235367)
    ·
      refine ⟨6734717410148796535853051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4489811606765864357235367 6734717410148796535853051)
      ·
        refine ⟨10102076115223194803779577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6734717410148796535853051 10102076115223194803779577)
        ·
          refine ⟨7576557086417396102834683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10102076115223194803779577 7576557086417396102834683)
          ·
            refine ⟨11364835629626094154252025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576557086417396102834683 11364835629626094154252025)
            ·
              refine ⟨8523626722219570615689019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11364835629626094154252025 8523626722219570615689019)
              ·
                refine ⟨12785440083329355923533529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523626722219570615689019 12785440083329355923533529)
                ·
                  refine ⟨9589080062497016942650147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12785440083329355923533529 9589080062497016942650147)
                  ·
                    refine ⟨14383620093745525413975221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9589080062497016942650147 14383620093745525413975221)
                    ·
                      refine ⟨1348464383788643007560177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14383620093745525413975221 1348464383788643007560177)
                      ·
                        rfl

theorem cell23_2626125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2626125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626125 prefixEnd_2626125 := by exact prefixLift 2626125
  have htrace : WordTrace (prefixWord ++ tailWord_2626125) baseStart_2626125 baseEnd_2626125 := by
    simpa [prefixWord, tailWord_2626125, baseEnd_2626125] using wordTrace_append hprefix tailTrace_2626125
  have hstable : (prefixWord ++ tailWord_2626125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626125).length < 2 ^ (prefixWord ++ tailWord_2626125).sum := by decide
  have hdescent : baseEnd_2626125 < baseStart_2626125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626145 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 5]
def baseStart_2626145 : Nat := 118140960795 + 2626145 * 2 ^ 59
def prefixEnd_2626145 : Nat := 4983230072969 + 3 ^ 40 * 2626145 * 2
def baseEnd_2626145 : Nat := 149830517044636992145565

theorem tailTrace_2626145 : CollatzResearch.WordTrace tailWord_2626145 prefixEnd_2626145 149830517044636992145565 := by
  unfold tailWord_2626145
  simp only [CollatzResearch.WordTrace]
  refine ⟨95783377070932649703415889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63855584713955099802277259 95783377070932649703415889)
  ·
    refine ⟨71837532803199487277561917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95783377070932649703415889 71837532803199487277561917)
    ·
      refine ⟨26939074801199807729085719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71837532803199487277561917 26939074801199807729085719)
      ·
        refine ⟨40408612201799711593628579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26939074801199807729085719 40408612201799711593628579)
        ·
          refine ⟨60612918302699567390442869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40408612201799711593628579 60612918302699567390442869)
          ·
            refine ⟨5682461090878084442854019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60612918302699567390442869 5682461090878084442854019)
            ·
              refine ⟨8523691636317126664281029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682461090878084442854019 8523691636317126664281029)
              ·
                refine ⟨1598192181809461249552693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8523691636317126664281029 1598192181809461249552693)
                ·
                  refine ⟨149830517044636992145565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1598192181809461249552693 149830517044636992145565)
                  ·
                    rfl

theorem cell23_2626145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 5].length) (baseStart_2626145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626145 prefixEnd_2626145 := by exact prefixLift 2626145
  have htrace : WordTrace (prefixWord ++ tailWord_2626145) baseStart_2626145 baseEnd_2626145 := by
    simpa [prefixWord, tailWord_2626145, baseEnd_2626145] using wordTrace_append hprefix tailTrace_2626145
  have hstable : (prefixWord ++ tailWord_2626145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626145).length < 2 ^ (prefixWord ++ tailWord_2626145).sum := by decide
  have hdescent : baseEnd_2626145 < baseStart_2626145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626171 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 10]
def baseStart_2626171 : Nat := 118140960795 + 2626171 * 2 ^ 59
def prefixEnd_2626171 : Nat := 4983230072969 + 3 ^ 40 * 2626171 * 2
def baseEnd_2626171 : Nat := 449496001299583275861655

theorem tailTrace_2626171 : CollatzResearch.WordTrace tailWord_2626171 prefixEnd_2626171 449496001299583275861655 := by
  unfold tailWord_2626171
  simp only [CollatzResearch.WordTrace]
  refine ⟨95784325368838456143862367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63856216912558970762574911 95784325368838456143862367)
  ·
    refine ⟨143676488053257684215793551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95784325368838456143862367 143676488053257684215793551)
    ·
      refine ⟨215514732079886526323690327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143676488053257684215793551 215514732079886526323690327)
      ·
        refine ⟨323272098119829789485535491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215514732079886526323690327 323272098119829789485535491)
        ·
          refine ⟨484908147179744684228303237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323272098119829789485535491 484908147179744684228303237)
          ·
            refine ⟨90920277596202128292806857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 484908147179744684228303237 90920277596202128292806857)
            ·
              refine ⟨68190208197151596219605143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90920277596202128292806857 68190208197151596219605143)
              ·
                refine ⟨102285312295727394329407715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68190208197151596219605143 102285312295727394329407715)
                ·
                  refine ⟨153427968443591091494111573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102285312295727394329407715 153427968443591091494111573)
                  ·
                    refine ⟨449496001299583275861655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 153427968443591091494111573 449496001299583275861655)
                    ·
                      rfl

theorem cell23_2626171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_2626171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626171 prefixEnd_2626171 := by exact prefixLift 2626171
  have htrace : WordTrace (prefixWord ++ tailWord_2626171) baseStart_2626171 baseEnd_2626171 := by
    simpa [prefixWord, tailWord_2626171, baseEnd_2626171] using wordTrace_append hprefix tailTrace_2626171
  have hstable : (prefixWord ++ tailWord_2626171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626171).length < 2 ^ (prefixWord ++ tailWord_2626171).sum := by decide
  have hdescent : baseEnd_2626171 < baseStart_2626171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626205 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2626205 : Nat := 118140960795 + 2626205 * 2 ^ 59
def prefixEnd_2626205 : Nat := 4983230072969 + 3 ^ 40 * 2626205 * 2
def baseEnd_2626205 : Nat := 449501820747000898186603

theorem tailTrace_2626205 : CollatzResearch.WordTrace tailWord_2626205 prefixEnd_2626205 449501820747000898186603 := by
  unfold tailWord_2626205
  simp only [CollatzResearch.WordTrace]
  refine ⟨95785565450715279950600069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63857043633810186633733379 95785565450715279950600069)
  ·
    refine ⟨17959793522009114990737513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95785565450715279950600069 17959793522009114990737513)
    ·
      refine ⟨13469845141506836243053135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17959793522009114990737513 13469845141506836243053135)
      ·
        refine ⟨20204767712260254364579703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13469845141506836243053135 20204767712260254364579703)
        ·
          refine ⟨30307151568390381546869555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20204767712260254364579703 30307151568390381546869555)
          ·
            refine ⟨45460727352585572320304333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30307151568390381546869555 45460727352585572320304333)
            ·
              refine ⟨17047772757219589620114125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45460727352585572320304333 17047772757219589620114125)
              ·
                refine ⟨6392914783957346107542797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17047772757219589620114125 6392914783957346107542797)
                ·
                  refine ⟨2397343043984004790328549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6392914783957346107542797 2397343043984004790328549)
                  ·
                    refine ⟨449501820747000898186603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397343043984004790328549 449501820747000898186603)
                    ·
                      rfl

theorem cell23_2626205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2626205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626205 prefixEnd_2626205 := by exact prefixLift 2626205
  have htrace : WordTrace (prefixWord ++ tailWord_2626205) baseStart_2626205 baseEnd_2626205 := by
    simpa [prefixWord, tailWord_2626205, baseEnd_2626205] using wordTrace_append hprefix tailTrace_2626205
  have hstable : (prefixWord ++ tailWord_2626205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626205).length < 2 ^ (prefixWord ++ tailWord_2626205).sum := by decide
  have hdescent : baseEnd_2626205 < baseStart_2626205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626239 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 1, 4]
def baseStart_2626239 : Nat := 118140960795 + 2626239 * 2 ^ 59
def prefixEnd_2626239 : Nat := 4983230072969 + 3 ^ 40 * 2626239 * 2
def baseEnd_2626239 : Nat := 449507640194418520511551

theorem tailTrace_2626239 : CollatzResearch.WordTrace tailWord_2626239 prefixEnd_2626239 449507640194418520511551 := by
  unfold tailWord_2626239
  simp only [CollatzResearch.WordTrace]
  refine ⟨95786805532592103757337771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63857870355061402504891847 95786805532592103757337771)
  ·
    refine ⟨143680208298888155636006657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95786805532592103757337771 143680208298888155636006657)
    ·
      refine ⟨107760156224166116727004993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143680208298888155636006657 107760156224166116727004993)
      ·
        refine ⟨80820117168124587545253745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107760156224166116727004993 80820117168124587545253745)
        ·
          refine ⟨60615087876093440658940309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80820117168124587545253745 60615087876093440658940309)
          ·
            refine ⟨2841332244191880030887827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60615087876093440658940309 2841332244191880030887827)
            ·
              refine ⟨4261998366287820046331741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841332244191880030887827 4261998366287820046331741)
              ·
                refine ⟨1598249387357932517374403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4261998366287820046331741 1598249387357932517374403)
                ·
                  refine ⟨2397374081036898776061605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598249387357932517374403 2397374081036898776061605)
                  ·
                    refine ⟨449507640194418520511551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397374081036898776061605 449507640194418520511551)
                    ·
                      rfl

theorem cell23_2626239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_2626239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626239 prefixEnd_2626239 := by exact prefixLift 2626239
  have htrace : WordTrace (prefixWord ++ tailWord_2626239) baseStart_2626239 baseEnd_2626239 := by
    simpa [prefixWord, tailWord_2626239, baseEnd_2626239] using wordTrace_append hprefix tailTrace_2626239
  have hstable : (prefixWord ++ tailWord_2626239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626239).length < 2 ^ (prefixWord ++ tailWord_2626239).sum := by decide
  have hdescent : baseEnd_2626239 < baseStart_2626239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626246 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2626246 : Nat := 118140960795 + 2626246 * 2 ^ 59
def prefixEnd_2626246 : Nat := 4983230072969 + 3 ^ 40 * 2626246 * 2
def baseEnd_2626246 : Nat := 1348526514947837034147121

theorem tailTrace_2626246 : CollatzResearch.WordTrace tailWord_2626246 prefixEnd_2626246 1348526514947837034147121 := by
  unfold tailWord_2626246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993345651361460748526331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63858040562377829301895061 2993345651361460748526331)
  ·
    refine ⟨4490018477042191122789497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993345651361460748526331 4490018477042191122789497)
    ·
      refine ⟨3367513857781643342092123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490018477042191122789497 3367513857781643342092123)
      ·
        refine ⟨5051270786672465013138185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367513857781643342092123 5051270786672465013138185)
        ·
          refine ⟨3788453090004348759853639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5051270786672465013138185 3788453090004348759853639)
          ·
            refine ⟨5682679635006523139780459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788453090004348759853639 5682679635006523139780459)
            ·
              refine ⟨8524019452509784709670689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682679635006523139780459 8524019452509784709670689)
              ·
                refine ⟨6393014589382338532253017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8524019452509784709670689 6393014589382338532253017)
                ·
                  refine ⟨4794760942036753899189763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6393014589382338532253017 4794760942036753899189763)
                  ·
                    refine ⟨7192141413055130848784645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4794760942036753899189763 7192141413055130848784645)
                    ·
                      refine ⟨1348526514947837034147121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7192141413055130848784645 1348526514947837034147121)
                      ·
                        rfl

theorem cell23_2626246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2626246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626246 prefixEnd_2626246 := by exact prefixLift 2626246
  have htrace : WordTrace (prefixWord ++ tailWord_2626246) baseStart_2626246 baseEnd_2626246 := by
    simpa [prefixWord, tailWord_2626246, baseEnd_2626246] using wordTrace_append hprefix tailTrace_2626246
  have hstable : (prefixWord ++ tailWord_2626246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626246).length < 2 ^ (prefixWord ++ tailWord_2626246).sum := by decide
  have hdescent : baseEnd_2626246 < baseStart_2626246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626312 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_2626312 : Nat := 118140960795 + 2626312 * 2 ^ 59
def prefixEnd_2626312 : Nat := 4983230072969 + 3 ^ 40 * 2626312 * 2
def baseEnd_2626312 : Nat := 449520134890344591973939

theorem tailTrace_2626312 : CollatzResearch.WordTrace tailWord_2626312 prefixEnd_2626312 449520134890344591973939 := by
  unfold tailWord_2626312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47894734030663818612372595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63859645374218424816496793 47894734030663818612372595)
  ·
    refine ⟨71842101045995727918558893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47894734030663818612372595 71842101045995727918558893)
    ·
      refine ⟨26940787892248397969459585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71842101045995727918558893 26940787892248397969459585)
      ·
        refine ⟨20205590919186298477094689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26940787892248397969459585 20205590919186298477094689)
        ·
          refine ⟨15154193189389723857821017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20205590919186298477094689 15154193189389723857821017)
          ·
            refine ⟨11365644892042292893365763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15154193189389723857821017 11365644892042292893365763)
            ·
              refine ⟨17048467338063439340048645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365644892042292893365763 17048467338063439340048645)
              ·
                refine ⟨3196587625886894876259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17048467338063439340048645 3196587625886894876259121)
                ·
                  refine ⟨2397440719415171157194341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3196587625886894876259121 2397440719415171157194341)
                  ·
                    refine ⟨449520134890344591973939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397440719415171157194341 449520134890344591973939)
                    ·
                      rfl

theorem cell23_2626312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_2626312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626312 prefixEnd_2626312 := by exact prefixLift 2626312
  have htrace : WordTrace (prefixWord ++ tailWord_2626312) baseStart_2626312 baseEnd_2626312 := by
    simpa [prefixWord, tailWord_2626312, baseEnd_2626312] using wordTrace_append hprefix tailTrace_2626312
  have hstable : (prefixWord ++ tailWord_2626312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626312).length < 2 ^ (prefixWord ++ tailWord_2626312).sum := by decide
  have hdescent : baseEnd_2626312 < baseStart_2626312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626332 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2626332 : Nat := 118140960795 + 2626332 * 2 ^ 59
def prefixEnd_2626332 : Nat := 4983230072969 + 3 ^ 40 * 2626332 * 2
def baseEnd_2626332 : Nat := 1348570674284123697671725

theorem tailTrace_2626332 : CollatzResearch.WordTrace tailWord_2626332 prefixEnd_2626332 1348570674284123697671725 := by
  unfold tailWord_2626332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47895098760627590320236625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63860131680836787093648833 47895098760627590320236625)
  ·
    refine ⟨35921324070470692740177469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47895098760627590320236625 35921324070470692740177469)
    ·
      refine ⟨13470496526426509777566551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35921324070470692740177469 13470496526426509777566551)
      ·
        refine ⟨20205744789639764666349827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13470496526426509777566551 20205744789639764666349827)
        ·
          refine ⟨30308617184459646999524741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20205744789639764666349827 30308617184459646999524741)
          ·
            refine ⟨5682865722086183812410889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30308617184459646999524741 5682865722086183812410889)
            ·
              refine ⟨4262149291564637859308167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682865722086183812410889 4262149291564637859308167)
              ·
                refine ⟨6393223937346956788962251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262149291564637859308167 6393223937346956788962251)
                ·
                  refine ⟨9589835906020435183443377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6393223937346956788962251 9589835906020435183443377)
                  ·
                    refine ⟨7192376929515326387582533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9589835906020435183443377 7192376929515326387582533)
                    ·
                      refine ⟨1348570674284123697671725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7192376929515326387582533 1348570674284123697671725)
                      ·
                        rfl

theorem cell23_2626332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2626332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626332 prefixEnd_2626332 := by exact prefixLift 2626332
  have htrace : WordTrace (prefixWord ++ tailWord_2626332) baseStart_2626332 baseEnd_2626332 := by
    simpa [prefixWord, tailWord_2626332, baseEnd_2626332] using wordTrace_append hprefix tailTrace_2626332
  have hstable : (prefixWord ++ tailWord_2626332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626332).length < 2 ^ (prefixWord ++ tailWord_2626332).sum := by decide
  have hdescent : baseEnd_2626332 < baseStart_2626332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626356 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2626356 : Nat := 118140960795 + 2626356 * 2 ^ 59
def prefixEnd_2626356 : Nat := 4983230072969 + 3 ^ 40 * 2626356 * 2
def baseEnd_2626356 : Nat := 1348582997819831603771615

theorem tailTrace_2626356 : CollatzResearch.WordTrace tailWord_2626356 prefixEnd_2626356 1348582997819831603771615 := by
  unfold tailWord_2626356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47895536436584116369673461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63860715248778821826231281 47895536436584116369673461)
  ·
    refine ⟨4490206540929760909656887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47895536436584116369673461 4490206540929760909656887)
    ·
      refine ⟨6735309811394641364485331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4490206540929760909656887 6735309811394641364485331)
      ·
        refine ⟨10102964717091962046727997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6735309811394641364485331 10102964717091962046727997)
        ·
          refine ⟨3788611768909485767522999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10102964717091962046727997 3788611768909485767522999)
          ·
            refine ⟨5682917653364228651284499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788611768909485767522999 5682917653364228651284499)
            ·
              refine ⟨8524376480046342976926749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682917653364228651284499 8524376480046342976926749)
              ·
                refine ⟨3196641180017378616347531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8524376480046342976926749 3196641180017378616347531)
                ·
                  refine ⟨4794961770026067924521297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196641180017378616347531 4794961770026067924521297)
                  ·
                    refine ⟨3596221327519550943390973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4794961770026067924521297 3596221327519550943390973)
                    ·
                      refine ⟨1348582997819831603771615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3596221327519550943390973 1348582997819831603771615)
                      ·
                        rfl

theorem cell23_2626356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2626356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626356 prefixEnd_2626356 := by exact prefixLift 2626356
  have htrace : WordTrace (prefixWord ++ tailWord_2626356) baseStart_2626356 baseEnd_2626356 := by
    simpa [prefixWord, tailWord_2626356, baseEnd_2626356] using wordTrace_append hprefix tailTrace_2626356
  have hstable : (prefixWord ++ tailWord_2626356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626356).length < 2 ^ (prefixWord ++ tailWord_2626356).sum := by decide
  have hdescent : baseEnd_2626356 < baseStart_2626356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626386 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_2626386 : Nat := 118140960795 + 2626386 * 2 ^ 59
def prefixEnd_2626386 : Nat := 4983230072969 + 3 ^ 40 * 2626386 * 2
def baseEnd_2626386 : Nat := 1348598402239466486396477

theorem tailTrace_2626386 : CollatzResearch.WordTrace tailWord_2626386 prefixEnd_2626386 1348598402239466486396477 := by
  unfold tailWord_2626386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23948041765764886965734753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63861444708706365241959341 23948041765764886965734753)
  ·
    refine ⟨17961031324323665224301065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23948041765764886965734753 17961031324323665224301065)
    ·
      refine ⟨13470773493242748918225799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17961031324323665224301065 13470773493242748918225799)
      ·
        refine ⟨20206160239864123377338699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13470773493242748918225799 20206160239864123377338699)
        ·
          refine ⟨30309240359796185066008049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206160239864123377338699 30309240359796185066008049)
          ·
            refine ⟨22731930269847138799506037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30309240359796185066008049 22731930269847138799506037)
            ·
              refine ⟨2131118462798169262453691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22731930269847138799506037 2131118462798169262453691)
              ·
                refine ⟨3196677694197253893680537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131118462798169262453691 3196677694197253893680537)
                ·
                  refine ⟨2397508270647940420260403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3196677694197253893680537 2397508270647940420260403)
                  ·
                    refine ⟨3596262405971910630390605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2397508270647940420260403 3596262405971910630390605)
                    ·
                      refine ⟨1348598402239466486396477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3596262405971910630390605 1348598402239466486396477)
                      ·
                        rfl

theorem cell23_2626386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_2626386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626386 prefixEnd_2626386 := by exact prefixLift 2626386
  have htrace : WordTrace (prefixWord ++ tailWord_2626386) baseStart_2626386 baseEnd_2626386 := by
    simpa [prefixWord, tailWord_2626386, baseEnd_2626386] using wordTrace_append hprefix tailTrace_2626386
  have hstable : (prefixWord ++ tailWord_2626386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626386).length < 2 ^ (prefixWord ++ tailWord_2626386).sum := by decide
  have hdescent : baseEnd_2626386 < baseStart_2626386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626396 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2626396 : Nat := 118140960795 + 2626396 * 2 ^ 59
def prefixEnd_2626396 : Nat := 4983230072969 + 3 ^ 40 * 2626396 * 2
def baseEnd_2626396 : Nat := 1348603537046011447271431

theorem tailTrace_2626396 : CollatzResearch.WordTrace tailWord_2626396 prefixEnd_2626396 1348603537046011447271431 := by
  unfold tailWord_2626396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47896265896511659785401521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63861687862015546380535361 47896265896511659785401521)
  ·
    refine ⟨35922199422383744839051141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47896265896511659785401521 35922199422383744839051141)
    ·
      refine ⟨6735412391696952157322089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35922199422383744839051141 6735412391696952157322089)
      ·
        refine ⟨5051559293772714117991567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6735412391696952157322089 5051559293772714117991567)
        ·
          refine ⟨7577338940659071176987351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051559293772714117991567 7577338940659071176987351)
          ·
            refine ⟨11366008410988606765481027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7577338940659071176987351 11366008410988606765481027)
            ·
              refine ⟨17049012616482910148221541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11366008410988606765481027 17049012616482910148221541)
              ·
                refine ⟨3196689865590545652791539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17049012616482910148221541 3196689865590545652791539)
                ·
                  refine ⟨4795034798385818479187309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196689865590545652791539 4795034798385818479187309)
                  ·
                    refine ⟨1798138049394681929695241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4795034798385818479187309 1798138049394681929695241)
                    ·
                      refine ⟨1348603537046011447271431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798138049394681929695241 1348603537046011447271431)
                      ·
                        rfl

theorem cell23_2626396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2626396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626396 prefixEnd_2626396 := by exact prefixLift 2626396
  have htrace : WordTrace (prefixWord ++ tailWord_2626396) baseStart_2626396 baseEnd_2626396 := by
    simpa [prefixWord, tailWord_2626396, baseEnd_2626396] using wordTrace_append hprefix tailTrace_2626396
  have hstable : (prefixWord ++ tailWord_2626396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626396).length < 2 ^ (prefixWord ++ tailWord_2626396).sum := by decide
  have hdescent : baseEnd_2626396 < baseStart_2626396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626405 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2626405 : Nat := 118140960795 + 2626405 * 2 ^ 59
def prefixEnd_2626405 : Nat := 4983230072969 + 3 ^ 40 * 2626405 * 2
def baseEnd_2626405 : Nat := 1348608158371901912058889

theorem tailTrace_2626405 : CollatzResearch.WordTrace tailWord_2626405 prefixEnd_2626405 1348608158371901912058889 := by
  unfold tailWord_2626405
  simp only [CollatzResearch.WordTrace]
  refine ⟨95792860049990714107880669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63861906699993809405253779 95792860049990714107880669)
  ·
    refine ⟨35922322518746517790455251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95792860049990714107880669 35922322518746517790455251)
    ·
      refine ⟨53883483778119776685682877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35922322518746517790455251 53883483778119776685682877)
      ·
        refine ⟨20206306416794916257131079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53883483778119776685682877 20206306416794916257131079)
        ·
          refine ⟨30309459625192374385696619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206306416794916257131079 30309459625192374385696619)
          ·
            refine ⟨45464189437788561578544929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30309459625192374385696619 45464189437788561578544929)
            ·
              refine ⟨34098142078341421183908697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45464189437788561578544929 34098142078341421183908697)
              ·
                refine ⟨25573606558756065887931523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34098142078341421183908697 25573606558756065887931523)
                ·
                  refine ⟨38360409838134098831897285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25573606558756065887931523 38360409838134098831897285)
                  ·
                    refine ⟨7192576844650143530980741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38360409838134098831897285 7192576844650143530980741)
                    ·
                      refine ⟨1348608158371901912058889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7192576844650143530980741 1348608158371901912058889)
                      ·
                        rfl

theorem cell23_2626405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2626405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626405 prefixEnd_2626405 := by exact prefixLift 2626405
  have htrace : WordTrace (prefixWord ++ tailWord_2626405) baseStart_2626405 baseEnd_2626405 := by
    simpa [prefixWord, tailWord_2626405, baseEnd_2626405] using wordTrace_append hprefix tailTrace_2626405
  have hstable : (prefixWord ++ tailWord_2626405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626405).length < 2 ^ (prefixWord ++ tailWord_2626405).sum := by decide
  have hdescent : baseEnd_2626405 < baseStart_2626405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626455 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2626455 : Nat := 118140960795 + 2626455 * 2 ^ 59
def prefixEnd_2626455 : Nat := 4983230072969 + 3 ^ 40 * 2626455 * 2
def baseEnd_2626455 : Nat := 1348633832404626716433659

theorem tailTrace_2626455 : CollatzResearch.WordTrace tailWord_2626455 prefixEnd_2626455 1348633832404626716433659 := by
  unfold tailWord_2626455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95794683699809572647200819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63863122466539715098133879 95794683699809572647200819)
  ·
    refine ⟨143692025549714358970801229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95794683699809572647200819 143692025549714358970801229)
    ·
      refine ⟨53884509581142884614050461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143692025549714358970801229 53884509581142884614050461)
      ·
        refine ⟨20206691092928581730268923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53884509581142884614050461 20206691092928581730268923)
        ·
          refine ⟨30310036639392872595403385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20206691092928581730268923 30310036639392872595403385)
          ·
            refine ⟨22732527479544654446552539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30310036639392872595403385 22732527479544654446552539)
            ·
              refine ⟨34098791219316981669828809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22732527479544654446552539 34098791219316981669828809)
              ·
                refine ⟨25574093414487736252371607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34098791219316981669828809 25574093414487736252371607)
                ·
                  refine ⟨38361140121731604378557411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25574093414487736252371607 38361140121731604378557411)
                  ·
                    refine ⟨57541710182597406567836117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38361140121731604378557411 57541710182597406567836117)
                    ·
                      refine ⟨1348633832404626716433659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57541710182597406567836117 1348633832404626716433659)
                      ·
                        rfl

theorem cell23_2626455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2626455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626455 prefixEnd_2626455 := by exact prefixLift 2626455
  have htrace : WordTrace (prefixWord ++ tailWord_2626455) baseStart_2626455 baseEnd_2626455 := by
    simpa [prefixWord, tailWord_2626455, baseEnd_2626455] using wordTrace_append hprefix tailTrace_2626455
  have hstable : (prefixWord ++ tailWord_2626455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626455).length < 2 ^ (prefixWord ++ tailWord_2626455).sum := by decide
  have hdescent : baseEnd_2626455 < baseStart_2626455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626495 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2626495 : Nat := 118140960795 + 2626495 * 2 ^ 59
def prefixEnd_2626495 : Nat := 4983230072969 + 3 ^ 40 * 2626495 * 2
def baseEnd_2626495 : Nat := 1348654371630806559933475

theorem tailTrace_2626495 : CollatzResearch.WordTrace tailWord_2626495 prefixEnd_2626495 1348654371630806559933475 := by
  unfold tailWord_2626495
  simp only [CollatzResearch.WordTrace]
  refine ⟨95796142619664659478656939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63864095079776439652437959 95796142619664659478656939)
  ·
    refine ⟨143694213929496989217985409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95796142619664659478656939 143694213929496989217985409)
    ·
      refine ⟨107770660447122741913489057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143694213929496989217985409 107770660447122741913489057)
      ·
        refine ⟨80827995335342056435116793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107770660447122741913489057 80827995335342056435116793)
        ·
          refine ⟨60620996501506542326337595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80827995335342056435116793 60620996501506542326337595)
          ·
            refine ⟨90931494752259813489506393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60620996501506542326337595 90931494752259813489506393)
            ·
              refine ⟨68198621064194860117129795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90931494752259813489506393 68198621064194860117129795)
              ·
                refine ⟨102297931596292290175694693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68198621064194860117129795 102297931596292290175694693)
                ·
                  refine ⟨19180862174304804407942755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102297931596292290175694693 19180862174304804407942755)
                  ·
                    refine ⟨28771293261457206611914133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19180862174304804407942755 28771293261457206611914133)
                    ·
                      refine ⟨1348654371630806559933475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28771293261457206611914133 1348654371630806559933475)
                      ·
                        rfl

theorem cell23_2626495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2626495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626495 prefixEnd_2626495 := by exact prefixLift 2626495
  have htrace : WordTrace (prefixWord ++ tailWord_2626495) baseStart_2626495 baseEnd_2626495 := by
    simpa [prefixWord, tailWord_2626495, baseEnd_2626495] using wordTrace_append hprefix tailTrace_2626495
  have hstable : (prefixWord ++ tailWord_2626495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626495).length < 2 ^ (prefixWord ++ tailWord_2626495).sum := by decide
  have hdescent : baseEnd_2626495 < baseStart_2626495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626516 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2626516 : Nat := 118140960795 + 2626516 * 2 ^ 59
def prefixEnd_2626516 : Nat := 4983230072969 + 3 ^ 40 * 2626516 * 2
def baseEnd_2626516 : Nat := 1348665154724550977770879

theorem tailTrace_2626516 : CollatzResearch.WordTrace tailWord_2626516 prefixEnd_2626516 1348665154724550977770879 := by
  unfold tailWord_2626516
  simp only [CollatzResearch.WordTrace]
  refine ⟨47898454276294290032585701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63864605701725720043447601 47898454276294290032585701)
  ·
    refine ⟨8980960176805179381109819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47898454276294290032585701 8980960176805179381109819)
    ·
      refine ⟨13471440265207769071664729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8980960176805179381109819 13471440265207769071664729)
      ·
        refine ⟨10103580198905826803748547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13471440265207769071664729 10103580198905826803748547)
        ·
          refine ⟨15155370298358740205622821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10103580198905826803748547 15155370298358740205622821)
          ·
            refine ⟨2841631930942263788554279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15155370298358740205622821 2841631930942263788554279)
            ·
              refine ⟨4262447896413395682831419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841631930942263788554279 4262447896413395682831419)
              ·
                refine ⟨6393671844620093524247129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262447896413395682831419 6393671844620093524247129)
                ·
                  refine ⟨4795253883465070143185347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6393671844620093524247129 4795253883465070143185347)
                  ·
                    refine ⟨7192880825197605214778021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4795253883465070143185347 7192880825197605214778021)
                    ·
                      refine ⟨1348665154724550977770879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7192880825197605214778021 1348665154724550977770879)
                      ·
                        rfl

theorem cell23_2626516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2626516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626516 prefixEnd_2626516 := by exact prefixLift 2626516
  have htrace : WordTrace (prefixWord ++ tailWord_2626516) baseStart_2626516 baseEnd_2626516 := by
    simpa [prefixWord, tailWord_2626516, baseEnd_2626516] using wordTrace_append hprefix tailTrace_2626516
  have hstable : (prefixWord ++ tailWord_2626516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626516).length < 2 ^ (prefixWord ++ tailWord_2626516).sum := by decide
  have hdescent : baseEnd_2626516 < baseStart_2626516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626609 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2626609 : Nat := 118140960795 + 2626609 * 2 ^ 59
def prefixEnd_2626609 : Nat := 4983230072969 + 3 ^ 40 * 2626609 * 2
def baseEnd_2626609 : Nat := 1348712908425419113907951

theorem tailTrace_2626609 : CollatzResearch.WordTrace tailWord_2626609 prefixEnd_2626609 1348712908425419113907951 := by
  unfold tailWord_2626609
  simp only [CollatzResearch.WordTrace]
  refine ⟨95800300541251656948306881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63866867027501104632204587 95800300541251656948306881)
  ·
    refine ⟨71850225405938742711230161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95800300541251656948306881 71850225405938742711230161)
    ·
      refine ⟨53887669054454057033422621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71850225405938742711230161 53887669054454057033422621)
      ·
        refine ⟨20207875895420271387533483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53887669054454057033422621 20207875895420271387533483)
        ·
          refine ⟨30311813843130407081300225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20207875895420271387533483 30311813843130407081300225)
          ·
            refine ⟨22733860382347805310975169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30311813843130407081300225 22733860382347805310975169)
            ·
              refine ⟨17050395286760853983231377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22733860382347805310975169 17050395286760853983231377)
              ·
                refine ⟨12787796465070640487423533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17050395286760853983231377 12787796465070640487423533)
                ·
                  refine ⟨4795423674401490182783825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12787796465070640487423533 4795423674401490182783825)
                  ·
                    refine ⟨3596567755801117637087869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4795423674401490182783825 3596567755801117637087869)
                    ·
                      refine ⟨1348712908425419113907951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3596567755801117637087869 1348712908425419113907951)
                      ·
                        rfl

theorem cell23_2626609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2626609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626609 prefixEnd_2626609 := by exact prefixLift 2626609
  have htrace : WordTrace (prefixWord ++ tailWord_2626609) baseStart_2626609 baseEnd_2626609 := by
    simpa [prefixWord, tailWord_2626609, baseEnd_2626609] using wordTrace_append hprefix tailTrace_2626609
  have hstable : (prefixWord ++ tailWord_2626609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626609).length < 2 ^ (prefixWord ++ tailWord_2626609).sum := by decide
  have hdescent : baseEnd_2626609 < baseStart_2626609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626616 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_2626616 : Nat := 118140960795 + 2626616 * 2 ^ 59
def prefixEnd_2626616 : Nat := 4983230072969 + 3 ^ 40 * 2626616 * 2
def baseEnd_2626616 : Nat := 449572167596666862173473

theorem tailTrace_2626616 : CollatzResearch.WordTrace tailWord_2626616 prefixEnd_2626616 449572167596666862173473 := by
  unfold tailWord_2626616
  simp only [CollatzResearch.WordTrace]
  refine ⟨47900277926113148571905851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63867037234817531429207801 47900277926113148571905851)
  ·
    refine ⟨71850416889169722857858777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47900277926113148571905851 71850416889169722857858777)
    ·
      refine ⟨53887812666877292143394083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71850416889169722857858777 53887812666877292143394083)
      ·
        refine ⟨80831719000315938215091125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53887812666877292143394083 80831719000315938215091125)
        ·
          refine ⟨7577973656279619207664793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80831719000315938215091125 7577973656279619207664793)
          ·
            refine ⟨5683480242209714405748595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7577973656279619207664793 5683480242209714405748595)
            ·
              refine ⟨8525220363314571608622893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683480242209714405748595 8525220363314571608622893)
              ·
                refine ⟨3196957636242964353233585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8525220363314571608622893 3196957636242964353233585)
                ·
                  refine ⟨2397718227182223264925189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3196957636242964353233585 2397718227182223264925189)
                  ·
                    refine ⟨449572167596666862173473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397718227182223264925189 449572167596666862173473)
                    ·
                      rfl

theorem cell23_2626616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_2626616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626616 prefixEnd_2626616 := by exact prefixLift 2626616
  have htrace : WordTrace (prefixWord ++ tailWord_2626616) baseStart_2626616 baseEnd_2626616 := by
    simpa [prefixWord, tailWord_2626616, baseEnd_2626616] using wordTrace_append hprefix tailTrace_2626616
  have hstable : (prefixWord ++ tailWord_2626616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626616).length < 2 ^ (prefixWord ++ tailWord_2626616).sum := by decide
  have hdescent : baseEnd_2626616 < baseStart_2626616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626646 : List Nat := [5, 2, 2, 1, 2, 11]
def baseStart_2626646 : Nat := 118140960795 + 2626646 * 2 ^ 59
def prefixEnd_2626646 : Nat := 4983230072969 + 3 ^ 40 * 2626646 * 2
def baseEnd_2626646 : Nat := 5550337066706318803067

theorem tailTrace_2626646 : CollatzResearch.WordTrace tailWord_2626646 prefixEnd_2626646 5550337066706318803067 := by
  unfold tailWord_2626646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987603127632350766712737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63867766694745074844935861 5987603127632350766712737)
  ·
    refine ⟨4490702345724263075034553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5987603127632350766712737 4490702345724263075034553)
    ·
      refine ⟨3368026759293197306275915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490702345724263075034553 3368026759293197306275915)
      ·
        refine ⟨5052040138939795959413873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368026759293197306275915 5052040138939795959413873)
        ·
          refine ⟨3789030104204846969560405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052040138939795959413873 3789030104204846969560405)
          ·
            refine ⟨5550337066706318803067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3789030104204846969560405 5550337066706318803067)
            ·
              rfl

theorem cell23_2626646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 11].length) (baseStart_2626646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626646 prefixEnd_2626646 := by exact prefixLift 2626646
  have htrace : WordTrace (prefixWord ++ tailWord_2626646) baseStart_2626646 baseEnd_2626646 := by
    simpa [prefixWord, tailWord_2626646, baseEnd_2626646] using wordTrace_append hprefix tailTrace_2626646
  have hstable : (prefixWord ++ tailWord_2626646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626646).length < 2 ^ (prefixWord ++ tailWord_2626646).sum := by decide
  have hdescent : baseEnd_2626646 < baseStart_2626646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626730 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2626730 : Nat := 118140960795 + 2626730 * 2 ^ 59
def prefixEnd_2626730 : Nat := 4983230072969 + 3 ^ 40 * 2626730 * 2
def baseEnd_2626730 : Nat := 1348775039584613140494895

theorem tailTrace_2626730 : CollatzResearch.WordTrace tailWord_2626730 prefixEnd_2626730 1348775039584613140494895 := by
  unfold tailWord_2626730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951178443453323653365411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63869809182542196408974429 23951178443453323653365411)
  ·
    refine ⟨35926767665179985480048117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23951178443453323653365411 35926767665179985480048117)
    ·
      refine ⟨3368134468610623638754511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35926767665179985480048117 3368134468610623638754511)
      ·
        refine ⟨5052201702915935458131767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368134468610623638754511 5052201702915935458131767)
        ·
          refine ⟨7578302554373903187197651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052201702915935458131767 7578302554373903187197651)
          ·
            refine ⟨11367453831560854780796477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578302554373903187197651 11367453831560854780796477)
            ·
              refine ⟨4262795186835320542798679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11367453831560854780796477 4262795186835320542798679)
              ·
                refine ⟨6394192780252980814198019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262795186835320542798679 6394192780252980814198019)
                ·
                  refine ⟨9591289170379471221297029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394192780252980814198019 9591289170379471221297029)
                  ·
                    refine ⟨1798366719446150853993193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9591289170379471221297029 1798366719446150853993193)
                    ·
                      refine ⟨1348775039584613140494895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798366719446150853993193 1348775039584613140494895)
                      ·
                        rfl

theorem cell23_2626730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2626730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626730 prefixEnd_2626730 := by exact prefixLift 2626730
  have htrace : WordTrace (prefixWord ++ tailWord_2626730) baseStart_2626730 baseEnd_2626730 := by
    simpa [prefixWord, tailWord_2626730, baseEnd_2626730] using wordTrace_append hprefix tailTrace_2626730
  have hstable : (prefixWord ++ tailWord_2626730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626730).length < 2 ^ (prefixWord ++ tailWord_2626730).sum := by decide
  have hdescent : baseEnd_2626730 < baseStart_2626730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626749 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2626749 : Nat := 118140960795 + 2626749 * 2 ^ 59
def prefixEnd_2626749 : Nat := 4983230072969 + 3 ^ 40 * 2626749 * 2
def baseEnd_2626749 : Nat := 449594931905682855385769

theorem tailTrace_2626749 : CollatzResearch.WordTrace tailWord_2626749 prefixEnd_2626749 449594931905682855385769 := by
  unfold tailWord_2626749
  simp only [CollatzResearch.WordTrace]
  refine ⟨95805406760744460858403301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63870271173829640572268867 95805406760744460858403301)
  ·
    refine ⟨17963513767639586410950619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95805406760744460858403301 17963513767639586410950619)
    ·
      refine ⟨26945270651459379616425929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17963513767639586410950619 26945270651459379616425929)
      ·
        refine ⟨20208952988594534712319447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26945270651459379616425929 20208952988594534712319447)
        ·
          refine ⟨30313429482891802068479171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20208952988594534712319447 30313429482891802068479171)
          ·
            refine ⟨45470144224337703102718757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30313429482891802068479171 45470144224337703102718757)
            ·
              refine ⟨8525652042063319331759767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45470144224337703102718757 8525652042063319331759767)
              ·
                refine ⟨12788478063094978997639651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525652042063319331759767 12788478063094978997639651)
                ·
                  refine ⟨19182717094642468496459477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12788478063094978997639651 19182717094642468496459477)
                  ·
                    refine ⟨449594931905682855385769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19182717094642468496459477 449594931905682855385769)
                    ·
                      rfl

theorem cell23_2626749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2626749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626749 prefixEnd_2626749 := by exact prefixLift 2626749
  have htrace : WordTrace (prefixWord ++ tailWord_2626749) baseStart_2626749 baseEnd_2626749 := by
    simpa [prefixWord, tailWord_2626749, baseEnd_2626749] using wordTrace_append hprefix tailTrace_2626749
  have hstable : (prefixWord ++ tailWord_2626749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626749).length < 2 ^ (prefixWord ++ tailWord_2626749).sum := by decide
  have hdescent : baseEnd_2626749 < baseStart_2626749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626776 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2626776 : Nat := 118140960795 + 2626776 * 2 ^ 59
def prefixEnd_2626776 : Nat := 4983230072969 + 3 ^ 40 * 2626776 * 2
def baseEnd_2626776 : Nat := 1348798659694719960519683

theorem tailTrace_2626776 : CollatzResearch.WordTrace tailWord_2626776 prefixEnd_2626776 1348798659694719960519683 := by
  unfold tailWord_2626776
  simp only [CollatzResearch.WordTrace]
  refine ⟨47903195765823322234818091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63870927687764429646424121 47903195765823322234818091)
  ·
    refine ⟨71854793648734983352227137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47903195765823322234818091 71854793648734983352227137)
    ·
      refine ⟨53891095236551237514170353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71854793648734983352227137 53891095236551237514170353)
      ·
        refine ⟨40418321427413428135627765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53891095236551237514170353 40418321427413428135627765)
        ·
          refine ⟨3789217633820008887715103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40418321427413428135627765 3789217633820008887715103)
          ·
            refine ⟨5683826450730013331572655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789217633820008887715103 5683826450730013331572655)
            ·
              refine ⟨8525739676095019997358983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683826450730013331572655 8525739676095019997358983)
              ·
                refine ⟨12788609514142529996038475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8525739676095019997358983 12788609514142529996038475)
                ·
                  refine ⟨19182914271213794994057713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12788609514142529996038475 19182914271213794994057713)
                  ·
                    refine ⟨14387185703410346245543285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19182914271213794994057713 14387185703410346245543285)
                    ·
                      refine ⟨1348798659694719960519683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14387185703410346245543285 1348798659694719960519683)
                      ·
                        rfl

theorem cell23_2626776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2626776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626776 prefixEnd_2626776 := by exact prefixLift 2626776
  have htrace : WordTrace (prefixWord ++ tailWord_2626776) baseStart_2626776 baseEnd_2626776 := by
    simpa [prefixWord, tailWord_2626776, baseEnd_2626776] using wordTrace_append hprefix tailTrace_2626776
  have hstable : (prefixWord ++ tailWord_2626776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626776).length < 2 ^ (prefixWord ++ tailWord_2626776).sum := by decide
  have hdescent : baseEnd_2626776 < baseStart_2626776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626781 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2626781 : Nat := 118140960795 + 2626781 * 2 ^ 59
def prefixEnd_2626781 : Nat := 4983230072969 + 3 ^ 40 * 2626781 * 2
def baseEnd_2626781 : Nat := 1348801227097992440957161

theorem tailTrace_2626781 : CollatzResearch.WordTrace tailWord_2626781 prefixEnd_2626781 1348801227097992440957161 := by
  unfold tailWord_2626781
  simp only [CollatzResearch.WordTrace]
  refine ⟨95806573896628530323568197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63871049264419020215712131 95806573896628530323568197)
  ·
    refine ⟨17963732605617849435669037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95806573896628530323568197 17963732605617849435669037)
    ·
      refine ⟨6736399727106693538375889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17963732605617849435669037 6736399727106693538375889)
      ·
        refine ⟨5052299795330020153781917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6736399727106693538375889 5052299795330020153781917)
        ·
          refine ⟨1894612423248757557668219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5052299795330020153781917 1894612423248757557668219)
          ·
            refine ⟨2841918634873136336502329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894612423248757557668219 2841918634873136336502329)
            ·
              refine ⟨2131438976154852252376747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841918634873136336502329 2131438976154852252376747)
              ·
                refine ⟨3197158464232278378565121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131438976154852252376747 3197158464232278378565121)
                ·
                  refine ⟨2397868848174208783923841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197158464232278378565121 2397868848174208783923841)
                  ·
                    refine ⟨1798401636130656587942881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2397868848174208783923841 1798401636130656587942881)
                    ·
                      refine ⟨1348801227097992440957161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798401636130656587942881 1348801227097992440957161)
                      ·
                        rfl

theorem cell23_2626781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2626781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626781 prefixEnd_2626781 := by exact prefixLift 2626781
  have htrace : WordTrace (prefixWord ++ tailWord_2626781) baseStart_2626781 baseEnd_2626781 := by
    simpa [prefixWord, tailWord_2626781, baseEnd_2626781] using wordTrace_append hprefix tailTrace_2626781
  have hstable : (prefixWord ++ tailWord_2626781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626781).length < 2 ^ (prefixWord ++ tailWord_2626781).sum := by decide
  have hdescent : baseEnd_2626781 < baseStart_2626781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626830 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2626830 : Nat := 118140960795 + 2626830 * 2 ^ 59
def prefixEnd_2626830 : Nat := 4983230072969 + 3 ^ 40 * 2626830 * 2
def baseEnd_2626830 : Nat := 449608795883354249748145

theorem tailTrace_2626830 : CollatzResearch.WordTrace tailWord_2626830 prefixEnd_2626830 449608795883354249748145 := by
  unfold tailWord_2626830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976045134181376461512743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63872240715634007794734629 11976045134181376461512743)
  ·
    refine ⟨17964067701272064692269115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976045134181376461512743 17964067701272064692269115)
    ·
      refine ⟨26946101551908097038403673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964067701272064692269115 26946101551908097038403673)
      ·
        refine ⟨20209576163931072778802755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26946101551908097038403673 20209576163931072778802755)
        ·
          refine ⟨30314364245896609168204133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209576163931072778802755 30314364245896609168204133)
          ·
            refine ⟨5683943296105614219038275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30314364245896609168204133 5683943296105614219038275)
            ·
              refine ⟨8525914944158421328557413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5683943296105614219038275 8525914944158421328557413)
              ·
                refine ⟨1598609052029703999104515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8525914944158421328557413 1598609052029703999104515)
                ·
                  refine ⟨2397913578044555998656773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598609052029703999104515 2397913578044555998656773)
                  ·
                    refine ⟨449608795883354249748145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397913578044555998656773 449608795883354249748145)
                    ·
                      rfl

theorem cell23_2626830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2626830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626830 prefixEnd_2626830 := by exact prefixLift 2626830
  have htrace : WordTrace (prefixWord ++ tailWord_2626830) baseStart_2626830 baseEnd_2626830 := by
    simpa [prefixWord, tailWord_2626830, baseEnd_2626830] using wordTrace_append hprefix tailTrace_2626830
  have hstable : (prefixWord ++ tailWord_2626830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626830).length < 2 ^ (prefixWord ++ tailWord_2626830).sum := by decide
  have hdescent : baseEnd_2626830 < baseStart_2626830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626849 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2626849 : Nat := 118140960795 + 2626849 * 2 ^ 59
def prefixEnd_2626849 : Nat := 4983230072969 + 3 ^ 40 * 2626849 * 2
def baseEnd_2626849 : Nat := 1348836143782498174906847

theorem tailTrace_2626849 : CollatzResearch.WordTrace tailWord_2626849 prefixEnd_2626849 1348836143782498174906847 := by
  unfold tailWord_2626849
  simp only [CollatzResearch.WordTrace]
  refine ⟨95809054060382177937043601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872702706921451958029067 95809054060382177937043601)
  ·
    refine ⟨71856790545286633452782701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95809054060382177937043601 71856790545286633452782701)
    ·
      refine ⟨26946296454482487544793513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71856790545286633452782701 26946296454482487544793513)
      ·
        refine ⟨20209722340861865658595135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26946296454482487544793513 20209722340861865658595135)
        ·
          refine ⟨30314583511292798487892703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209722340861865658595135 30314583511292798487892703)
          ·
            refine ⟨45471875266939197731839055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30314583511292798487892703 45471875266939197731839055)
            ·
              refine ⟨68207812900408796597758583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45471875266939197731839055 68207812900408796597758583)
              ·
                refine ⟨102311719350613194896637875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68207812900408796597758583 102311719350613194896637875)
                ·
                  refine ⟨153467579025919792344956813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102311719350613194896637875 153467579025919792344956813)
                  ·
                    refine ⟨57550342134719922129358805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153467579025919792344956813 57550342134719922129358805)
                    ·
                      refine ⟨1348836143782498174906847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57550342134719922129358805 1348836143782498174906847)
                      ·
                        rfl

theorem cell23_2626849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2626849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626849 prefixEnd_2626849 := by exact prefixLift 2626849
  have htrace : WordTrace (prefixWord ++ tailWord_2626849) baseStart_2626849 baseEnd_2626849 := by
    simpa [prefixWord, tailWord_2626849, baseEnd_2626849] using wordTrace_append hprefix tailTrace_2626849
  have hstable : (prefixWord ++ tailWord_2626849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626849).length < 2 ^ (prefixWord ++ tailWord_2626849).sum := by decide
  have hdescent : baseEnd_2626849 < baseStart_2626849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626853 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_2626853 : Nat := 118140960795 + 2626853 * 2 ^ 59
def prefixEnd_2626853 : Nat := 4983230072969 + 3 ^ 40 * 2626853 * 2
def baseEnd_2626853 : Nat := 1348838197705116159256829

theorem tailTrace_2626853 : CollatzResearch.WordTrace tailWord_2626853 prefixEnd_2626853 1348838197705116159256829 := by
  unfold tailWord_2626853
  simp only [CollatzResearch.WordTrace]
  refine ⟨95809199952367686620189213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872799968245124413459475 95809199952367686620189213)
  ·
    refine ⟨35928449982137882482570955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95809199952367686620189213 35928449982137882482570955)
    ·
      refine ⟨53892674973206823723856433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35928449982137882482570955 53892674973206823723856433)
      ·
        refine ⟨40419506229905117792892325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53892674973206823723856433 40419506229905117792892325)
        ·
          refine ⟨7578657418107209586167311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40419506229905117792892325 7578657418107209586167311)
          ·
            refine ⟨11367986127160814379250967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578657418107209586167311 11367986127160814379250967)
            ·
              refine ⟨17051979190741221568876451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11367986127160814379250967 17051979190741221568876451)
              ·
                refine ⟨25577968786111832353314677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17051979190741221568876451 25577968786111832353314677)
                ·
                  refine ⟨2397934573697984283123251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25577968786111832353314677 2397934573697984283123251)
                  ·
                    refine ⟨3596901860546976424684877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2397934573697984283123251 3596901860546976424684877)
                    ·
                      refine ⟨1348838197705116159256829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3596901860546976424684877 1348838197705116159256829)
                      ·
                        rfl

theorem cell23_2626853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_2626853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626853 prefixEnd_2626853 := by exact prefixLift 2626853
  have htrace : WordTrace (prefixWord ++ tailWord_2626853) baseStart_2626853 baseEnd_2626853 := by
    simpa [prefixWord, tailWord_2626853, baseEnd_2626853] using wordTrace_append hprefix tailTrace_2626853
  have hstable : (prefixWord ++ tailWord_2626853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626853).length < 2 ^ (prefixWord ++ tailWord_2626853).sum := by decide
  have hdescent : baseEnd_2626853 < baseStart_2626853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626859 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_2626859 : Nat := 118140960795 + 2626859 * 2 ^ 59
def prefixEnd_2626859 : Nat := 4983230072969 + 3 ^ 40 * 2626859 * 2
def baseEnd_2626859 : Nat := 1348841278589043135781801

theorem tailTrace_2626859 : CollatzResearch.WordTrace tailWord_2626859 prefixEnd_2626859 1348841278589043135781801 := by
  unfold tailWord_2626859
  simp only [CollatzResearch.WordTrace]
  refine ⟨95809418790345949644907631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63872945860230633096605087 95809418790345949644907631)
  ·
    refine ⟨143714128185518924467361447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95809418790345949644907631 143714128185518924467361447)
    ·
      refine ⟨215571192278278386701042171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143714128185518924467361447 215571192278278386701042171)
      ·
        refine ⟨323356788417417580051563257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215571192278278386701042171 323356788417417580051563257)
        ·
          refine ⟨242517591313063185038672443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323356788417417580051563257 242517591313063185038672443)
          ·
            refine ⟨363776386969594777558008665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242517591313063185038672443 363776386969594777558008665)
            ·
              refine ⟨272832290227196083168506499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363776386969594777558008665 272832290227196083168506499)
              ·
                refine ⟨409248435340794124752759749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272832290227196083168506499 409248435340794124752759749)
                ·
                  refine ⟨76734081626398898391142453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409248435340794124752759749 76734081626398898391142453)
                  ·
                    refine ⟨7193820152474896724169605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76734081626398898391142453 7193820152474896724169605)
                    ·
                      refine ⟨1348841278589043135781801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7193820152474896724169605 1348841278589043135781801)
                      ·
                        rfl

theorem cell23_2626859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_2626859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626859 prefixEnd_2626859 := by exact prefixLift 2626859
  have htrace : WordTrace (prefixWord ++ tailWord_2626859) baseStart_2626859 baseEnd_2626859 := by
    simpa [prefixWord, tailWord_2626859, baseEnd_2626859] using wordTrace_append hprefix tailTrace_2626859
  have hstable : (prefixWord ++ tailWord_2626859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626859).length < 2 ^ (prefixWord ++ tailWord_2626859).sum := by decide
  have hdescent : baseEnd_2626859 < baseStart_2626859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626877 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 6]
def baseStart_2626877 : Nat := 118140960795 + 2626877 * 2 ^ 59
def prefixEnd_2626877 : Nat := 4983230072969 + 3 ^ 40 * 2626877 * 2
def baseEnd_2626877 : Nat := 149872280137869340595191

theorem tailTrace_2626877 : CollatzResearch.WordTrace tailWord_2626877 prefixEnd_2626877 149872280137869340595191 := by
  unfold tailWord_2626877
  simp only [CollatzResearch.WordTrace]
  refine ⟨95810075304280738719062885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63873383536187159146041923 95810075304280738719062885)
  ·
    refine ⟨17964389119552638509824291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95810075304280738719062885 17964389119552638509824291)
    ·
      refine ⟨26946583679328957764736437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964389119552638509824291 26946583679328957764736437)
      ·
        refine ⟨2526242219937089790444041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26946583679328957764736437 2526242219937089790444041)
        ·
          refine ⟨1894681664952817342833031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526242219937089790444041 1894681664952817342833031)
          ·
            refine ⟨2842022497429226014249547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894681664952817342833031 2842022497429226014249547)
            ·
              refine ⟨4263033746143839021374321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842022497429226014249547 4263033746143839021374321)
              ·
                refine ⟨3197275309607879266030741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4263033746143839021374321 3197275309607879266030741)
                ·
                  refine ⟨149872280137869340595191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3197275309607879266030741 149872280137869340595191)
                  ·
                    rfl

theorem cell23_2626877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_2626877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626877 prefixEnd_2626877 := by exact prefixLift 2626877
  have htrace : WordTrace (prefixWord ++ tailWord_2626877) baseStart_2626877 baseEnd_2626877 := by
    simpa [prefixWord, tailWord_2626877, baseEnd_2626877] using wordTrace_append hprefix tailTrace_2626877
  have hstable : (prefixWord ++ tailWord_2626877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626877).length < 2 ^ (prefixWord ++ tailWord_2626877).sum := by decide
  have hdescent : baseEnd_2626877 < baseStart_2626877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626896 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_2626896 : Nat := 118140960795 + 2626896 * 2 ^ 59
def prefixEnd_2626896 : Nat := 4983230072969 + 3 ^ 40 * 2626896 * 2
def baseEnd_2626896 : Nat := 1348860277373259491019131

theorem tailTrace_2626896 : CollatzResearch.WordTrace tailWord_2626896 prefixEnd_2626896 1348860277373259491019131 := by
  unfold tailWord_2626896
  simp only [CollatzResearch.WordTrace]
  refine ⟨47905384145605952482002271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63873845527474603309336361 47905384145605952482002271)
  ·
    refine ⟨71858076218408928723003407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47905384145605952482002271 71858076218408928723003407)
    ·
      refine ⟨107787114327613393084505111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71858076218408928723003407 107787114327613393084505111)
      ·
        refine ⟨161680671491420089626757667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107787114327613393084505111 161680671491420089626757667)
        ·
          refine ⟨242521007237130134440136501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161680671491420089626757667 242521007237130134440136501)
          ·
            refine ⟨22736344428480950103762797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242521007237130134440136501 22736344428480950103762797)
            ·
              refine ⟨8526129160680356288911049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22736344428480950103762797 8526129160680356288911049)
              ·
                refine ⟨6394596870510267216683287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8526129160680356288911049 6394596870510267216683287)
                ·
                  refine ⟨9591895305765400825024931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394596870510267216683287 9591895305765400825024931)
                  ·
                    refine ⟨14387842958648101237537397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9591895305765400825024931 14387842958648101237537397)
                    ·
                      refine ⟨1348860277373259491019131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14387842958648101237537397 1348860277373259491019131)
                      ·
                        rfl

theorem cell23_2626896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_2626896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626896 prefixEnd_2626896 := by exact prefixLift 2626896
  have htrace : WordTrace (prefixWord ++ tailWord_2626896) baseStart_2626896 baseEnd_2626896 := by
    simpa [prefixWord, tailWord_2626896, baseEnd_2626896] using wordTrace_append hprefix tailTrace_2626896
  have hstable : (prefixWord ++ tailWord_2626896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626896).length < 2 ^ (prefixWord ++ tailWord_2626896).sum := by decide
  have hdescent : baseEnd_2626896 < baseStart_2626896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626899 : List Nat := [1, 1, 1, 2, 1, 1, 6, 10]
def baseStart_2626899 : Nat := 118140960795 + 2626899 * 2 ^ 59
def prefixEnd_2626899 : Nat := 4983230072969 + 3 ^ 40 * 2626899 * 2
def baseEnd_2626899 : Nat := 49957845104267517751171

theorem tailTrace_2626899 : CollatzResearch.WordTrace tailWord_2626899 prefixEnd_2626899 49957845104267517751171 := by
  unfold tailWord_2626899
  simp only [CollatzResearch.WordTrace]
  refine ⟨95810877710201036476363751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63873918473467357650909167 95810877710201036476363751)
  ·
    refine ⟨143716316565301554714545627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95810877710201036476363751 143716316565301554714545627)
    ·
      refine ⟨215574474847952332071818441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143716316565301554714545627 215574474847952332071818441)
      ·
        refine ⟨161680856135964249053863831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215574474847952332071818441 161680856135964249053863831)
        ·
          refine ⟨242521284203946373580795747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161680856135964249053863831 242521284203946373580795747)
          ·
            refine ⟨363781926305919560371193621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242521284203946373580795747 363781926305919560371193621)
            ·
              refine ⟨17052277795589979392399701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 363781926305919560371193621 17052277795589979392399701)
              ·
                refine ⟨49957845104267517751171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17052277795589979392399701 49957845104267517751171)
                ·
                  rfl

theorem cell23_2626899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 10].length) (baseStart_2626899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626899 prefixEnd_2626899 := by exact prefixLift 2626899
  have htrace : WordTrace (prefixWord ++ tailWord_2626899) baseStart_2626899 baseEnd_2626899 := by
    simpa [prefixWord, tailWord_2626899, baseEnd_2626899] using wordTrace_append hprefix tailTrace_2626899
  have hstable : (prefixWord ++ tailWord_2626899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626899).length < 2 ^ (prefixWord ++ tailWord_2626899).sum := by decide
  have hdescent : baseEnd_2626899 < baseStart_2626899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626903 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 6]
def baseStart_2626903 : Nat := 118140960795 + 2626903 * 2 ^ 59
def prefixEnd_2626903 : Nat := 4983230072969 + 3 ^ 40 * 2626903 * 2
def baseEnd_2626903 : Nat := 449621290579280321210533

theorem tailTrace_2626903 : CollatzResearch.WordTrace tailWord_2626903 prefixEnd_2626903 449621290579280321210533 := by
  unfold tailWord_2626903
  simp only [CollatzResearch.WordTrace]
  refine ⟨95811023602186545159509363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63874015734791030106339575 95811023602186545159509363)
  ·
    refine ⟨143716535403279817739264045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95811023602186545159509363 143716535403279817739264045)
    ·
      refine ⟨53893700776229931652224017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143716535403279817739264045 53893700776229931652224017)
      ·
        refine ⟨40420275582172448739168013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53893700776229931652224017 40420275582172448739168013)
        ·
          refine ⟨15157603343314668277188005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40420275582172448739168013 15157603343314668277188005)
          ·
            refine ⟨2842050626871500301972751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15157603343314668277188005 2842050626871500301972751)
            ·
              refine ⟨4263075940307250452959127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842050626871500301972751 4263075940307250452959127)
              ·
                refine ⟨6394613910460875679438691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263075940307250452959127 6394613910460875679438691)
                ·
                  refine ⟨9591920865691313519158037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394613910460875679438691 9591920865691313519158037)
                  ·
                    refine ⟨449621290579280321210533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9591920865691313519158037 449621290579280321210533)
                    ·
                      rfl

theorem cell23_2626903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_2626903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626903 prefixEnd_2626903 := by exact prefixLift 2626903
  have htrace : WordTrace (prefixWord ++ tailWord_2626903) baseStart_2626903 baseEnd_2626903 := by
    simpa [prefixWord, tailWord_2626903, baseEnd_2626903] using wordTrace_append hprefix tailTrace_2626903
  have hstable : (prefixWord ++ tailWord_2626903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626903).length < 2 ^ (prefixWord ++ tailWord_2626903).sum := by decide
  have hdescent : baseEnd_2626903 < baseStart_2626903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626916 : List Nat := [2, 3, 1, 1, 3, 3, 1, 9]
def baseStart_2626916 : Nat := 118140960795 + 2626916 * 2 ^ 59
def prefixEnd_2626916 : Nat := 4983230072969 + 3 ^ 40 * 2626916 * 2
def baseEnd_2626916 : Nat := 49958168406901830102557

theorem tailTrace_2626916 : CollatzResearch.WordTrace tailWord_2626916 prefixEnd_2626916 49958168406901830102557 := by
  unfold tailWord_2626916
  simp only [CollatzResearch.WordTrace]
  refine ⟨47905748875569724189866301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63874331834092965586488401 47905748875569724189866301)
  ·
    refine ⟨17964655828338646571199863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47905748875569724189866301 17964655828338646571199863)
    ·
      refine ⟨26946983742507969856799795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964655828338646571199863 26946983742507969856799795)
      ·
        refine ⟨40420475613761954785199693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26946983742507969856799795 40420475613761954785199693)
        ·
          refine ⟨15157678355160733044449885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40420475613761954785199693 15157678355160733044449885)
          ·
            refine ⟨5684129383185274891668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15157678355160733044449885 5684129383185274891668707)
            ·
              refine ⟨8526194074777912337503061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684129383185274891668707 8526194074777912337503061)
              ·
                refine ⟨49958168406901830102557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8526194074777912337503061 49958168406901830102557)
                ·
                  rfl

theorem cell23_2626916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 9].length) (baseStart_2626916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626916 prefixEnd_2626916 := by exact prefixLift 2626916
  have htrace : WordTrace (prefixWord ++ tailWord_2626916) baseStart_2626916 baseEnd_2626916 := by
    simpa [prefixWord, tailWord_2626916, baseEnd_2626916] using wordTrace_append hprefix tailTrace_2626916
  have hstable : (prefixWord ++ tailWord_2626916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626916).length < 2 ^ (prefixWord ++ tailWord_2626916).sum := by decide
  have hdescent : baseEnd_2626916 < baseStart_2626916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626933 : List Nat := [1, 3, 4, 1, 3, 2, 9]
def baseStart_2626933 : Nat := 118140960795 + 2626933 * 2 ^ 59
def prefixEnd_2626933 : Nat := 4983230072969 + 3 ^ 40 * 2626933 * 2
def baseEnd_2626933 : Nat := 16652830569845380817981

theorem tailTrace_2626933 : CollatzResearch.WordTrace tailWord_2626933 prefixEnd_2626933 16652830569845380817981 := by
  unfold tailWord_2626933
  simp only [CollatzResearch.WordTrace]
  refine ⟨95812117792077860283101453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63874745194718573522067635 95812117792077860283101453)
  ·
    refine ⟨35929544172029197606163045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95812117792077860283101453 35929544172029197606163045)
    ·
      refine ⟨6736789532255474551155571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35929544172029197606163045 6736789532255474551155571)
      ·
        refine ⟨10105184298383211826733357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736789532255474551155571 10105184298383211826733357)
        ·
          refine ⟨3789444111893704435025009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10105184298383211826733357 3789444111893704435025009)
          ·
            refine ⟨2842083083920278326268757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789444111893704435025009 2842083083920278326268757)
            ·
              refine ⟨16652830569845380817981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2842083083920278326268757 16652830569845380817981)
              ·
                rfl

theorem cell23_2626933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 9].length) (baseStart_2626933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626933 prefixEnd_2626933 := by exact prefixLift 2626933
  have htrace : WordTrace (prefixWord ++ tailWord_2626933) baseStart_2626933 baseEnd_2626933 := by
    simpa [prefixWord, tailWord_2626933, baseEnd_2626933] using wordTrace_append hprefix tailTrace_2626933
  have hstable : (prefixWord ++ tailWord_2626933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626933).length < 2 ^ (prefixWord ++ tailWord_2626933).sum := by decide
  have hdescent : baseEnd_2626933 < baseStart_2626933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2626970 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2626970 : Nat := 118140960795 + 2626970 * 2 ^ 59
def prefixEnd_2626970 : Nat := 4983230072969 + 3 ^ 40 * 2626970 * 2
def baseEnd_2626970 : Nat := 1348898274941692201493791

theorem tailTrace_2626970 : CollatzResearch.WordTrace tailWord_2626970 prefixEnd_2626970 1348898274941692201493791 := by
  unfold tailWord_2626970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23953366823235953900549591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63875644861962543734798909 23953366823235953900549591)
  ·
    refine ⟨35930050234853930850824387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23953366823235953900549591 35930050234853930850824387)
    ·
      refine ⟨53895075352280896276236581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35930050234853930850824387 53895075352280896276236581)
      ·
        refine ⟨10105326628552668051794359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53895075352280896276236581 10105326628552668051794359)
        ·
          refine ⟨15157989942829002077691539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10105326628552668051794359 15157989942829002077691539)
          ·
            refine ⟨22736984914243503116537309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15157989942829002077691539 22736984914243503116537309)
            ·
              refine ⟨8526369342841313668701491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22736984914243503116537309 8526369342841313668701491)
              ·
                refine ⟨12789554014261970503052237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526369342841313668701491 12789554014261970503052237)
                ·
                  refine ⟨4796082755348238938644589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12789554014261970503052237 4796082755348238938644589)
                  ·
                    refine ⟨1798531033255589601991721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4796082755348238938644589 1798531033255589601991721)
                    ·
                      refine ⟨1348898274941692201493791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798531033255589601991721 1348898274941692201493791)
                      ·
                        rfl

theorem cell23_2626970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2626970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2626970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2626970 prefixEnd_2626970 := by exact prefixLift 2626970
  have htrace : WordTrace (prefixWord ++ tailWord_2626970) baseStart_2626970 baseEnd_2626970 := by
    simpa [prefixWord, tailWord_2626970, baseEnd_2626970] using wordTrace_append hprefix tailTrace_2626970
  have hstable : (prefixWord ++ tailWord_2626970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2626970).length < 2 ^ (prefixWord ++ tailWord_2626970).sum := by decide
  have hdescent : baseEnd_2626970 < baseStart_2626970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2626970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627000 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_2627000 : Nat := 118140960795 + 2627000 * 2 ^ 59
def prefixEnd_2627000 : Nat := 4983230072969 + 3 ^ 40 * 2627000 * 2
def baseEnd_2627000 : Nat := 1348913679361327084118653

theorem tailTrace_2627000 : CollatzResearch.WordTrace tailWord_2627000 prefixEnd_2627000 1348913679361327084118653 := by
  unfold tailWord_2627000
  simp only [CollatzResearch.WordTrace]
  refine ⟨47907280741417565362895227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63876374321890087150526969 47907280741417565362895227)
  ·
    refine ⟨71860921112126348044342841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47907280741417565362895227 71860921112126348044342841)
    ·
      refine ⟨53895690834094761033257131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71860921112126348044342841 53895690834094761033257131)
      ·
        refine ⟨80843536251142141549885697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53895690834094761033257131 80843536251142141549885697)
        ·
          refine ⟨60632652188356606162414273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80843536251142141549885697 60632652188356606162414273)
          ·
            refine ⟨45474489141267454621810705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60632652188356606162414273 45474489141267454621810705)
            ·
              refine ⟨34105866855950590966358029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45474489141267454621810705 34105866855950590966358029)
              ·
                refine ⟨12789700070981471612384261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34105866855950590966358029 12789700070981471612384261)
                ·
                  refine ⟨2398068763309025927322049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12789700070981471612384261 2398068763309025927322049)
                  ·
                    refine ⟨1798551572481769445491537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398068763309025927322049 1798551572481769445491537)
                    ·
                      refine ⟨1348913679361327084118653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798551572481769445491537 1348913679361327084118653)
                      ·
                        rfl

theorem cell23_2627000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_2627000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627000 prefixEnd_2627000 := by exact prefixLift 2627000
  have htrace : WordTrace (prefixWord ++ tailWord_2627000) baseStart_2627000 baseEnd_2627000 := by
    simpa [prefixWord, tailWord_2627000, baseEnd_2627000] using wordTrace_append hprefix tailTrace_2627000
  have hstable : (prefixWord ++ tailWord_2627000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627000).length < 2 ^ (prefixWord ++ tailWord_2627000).sum := by decide
  have hdescent : baseEnd_2627000 < baseStart_2627000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627180 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_2627180 : Nat := 118140960795 + 2627180 * 2 ^ 59
def prefixEnd_2627180 : Nat := 4983230072969 + 3 ^ 40 * 2627180 * 2
def baseEnd_2627180 : Nat := 1349006105879136379867825

theorem tailTrace_2627180 : CollatzResearch.WordTrace tailWord_2627180 prefixEnd_2627180 1349006105879136379867825 := by
  unfold tailWord_2627180
  simp only [CollatzResearch.WordTrace]
  refine ⟨47910563311091510733671497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63880751081455347644895329 47910563311091510733671497)
  ·
    refine ⟨35932922483318633050253623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47910563311091510733671497 35932922483318633050253623)
    ·
      refine ⟨53899383724977949575380435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35932922483318633050253623 53899383724977949575380435)
      ·
        refine ⟨80849075587466924363070653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53899383724977949575380435 80849075587466924363070653)
        ·
          refine ⟨30318403345300096636151495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80849075587466924363070653 30318403345300096636151495)
          ·
            refine ⟨45477605017950144954227243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30318403345300096636151495 45477605017950144954227243)
            ·
              refine ⟨68216407526925217431340865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45477605017950144954227243 68216407526925217431340865)
              ·
                refine ⟨51162305645193913073505649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68216407526925217431340865 51162305645193913073505649)
                ·
                  refine ⟨38371729233895434805129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51162305645193913073505649 38371729233895434805129237)
                  ·
                    refine ⟨1798674807838848506490433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38371729233895434805129237 1798674807838848506490433)
                    ·
                      refine ⟨1349006105879136379867825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798674807838848506490433 1349006105879136379867825)
                      ·
                        rfl

theorem cell23_2627180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_2627180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627180 prefixEnd_2627180 := by exact prefixLift 2627180
  have htrace : WordTrace (prefixWord ++ tailWord_2627180) baseStart_2627180 baseEnd_2627180 := by
    simpa [prefixWord, tailWord_2627180, baseEnd_2627180] using wordTrace_append hprefix tailTrace_2627180
  have hstable : (prefixWord ++ tailWord_2627180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627180).length < 2 ^ (prefixWord ++ tailWord_2627180).sum := by decide
  have hdescent : baseEnd_2627180 < baseStart_2627180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_2627183 : Nat := 118140960795 + 2627183 * 2 ^ 59
def prefixEnd_2627183 : Nat := 4983230072969 + 3 ^ 40 * 2627183 * 2
def baseEnd_2627183 : Nat := 1349007646321099868130311

theorem tailTrace_2627183 : CollatzResearch.WordTrace tailWord_2627183 prefixEnd_2627183 1349007646321099868130311 := by
  unfold tailWord_2627183
  simp only [CollatzResearch.WordTrace]
  refine ⟨95821236041172152979702203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63880824027448101986468135 95821236041172152979702203)
  ·
    refine ⟨143731854061758229469553305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95821236041172152979702203 143731854061758229469553305)
    ·
      refine ⟨107798890546318672102164979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143731854061758229469553305 107798890546318672102164979)
      ·
        refine ⟨161698335819478008153247469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107798890546318672102164979 161698335819478008153247469)
        ·
          refine ⟨60636875932304253057467801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161698335819478008153247469 60636875932304253057467801)
          ·
            refine ⟨45477656949228189793100851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60636875932304253057467801 45477656949228189793100851)
            ·
              refine ⟨68216485423842284689651277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45477656949228189793100851 68216485423842284689651277)
              ·
                refine ⟨25581182033940856758619229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68216485423842284689651277 25581182033940856758619229)
                ·
                  refine ⟨9592943262727821284482211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25581182033940856758619229 9592943262727821284482211)
                  ·
                    refine ⟨14389414894091731926723317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9592943262727821284482211 14389414894091731926723317)
                    ·
                      refine ⟨1349007646321099868130311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14389414894091731926723317 1349007646321099868130311)
                      ·
                        rfl

theorem cell23_2627183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_2627183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627183 prefixEnd_2627183 := by exact prefixLift 2627183
  have htrace : WordTrace (prefixWord ++ tailWord_2627183) baseStart_2627183 baseEnd_2627183 := by
    simpa [prefixWord, tailWord_2627183, baseEnd_2627183] using wordTrace_append hprefix tailTrace_2627183
  have hstable : (prefixWord ++ tailWord_2627183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627183).length < 2 ^ (prefixWord ++ tailWord_2627183).sum := by decide
  have hdescent : baseEnd_2627183 < baseStart_2627183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627200 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_2627200 : Nat := 118140960795 + 2627200 * 2 ^ 59
def prefixEnd_2627200 : Nat := 4983230072969 + 3 ^ 40 * 2627200 * 2
def baseEnd_2627200 : Nat := 1349016375492226301617733

theorem tailTrace_2627200 : CollatzResearch.WordTrace tailWord_2627200 prefixEnd_2627200 1349016375492226301617733 := by
  unfold tailWord_2627200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47910928041055282441535527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63881237388073709922047369 47910928041055282441535527)
  ·
    refine ⟨71866392061582923662303291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47910928041055282441535527 71866392061582923662303291)
    ·
      refine ⟨107799588092374385493454937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71866392061582923662303291 107799588092374385493454937)
      ·
        refine ⟨80849691069280789120091203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107799588092374385493454937 80849691069280789120091203)
        ·
          refine ⟨121274536603921183680136805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80849691069280789120091203 121274536603921183680136805)
          ·
            refine ⟨22738975613235221940025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121274536603921183680136805 22738975613235221940025651)
            ·
              refine ⟨34108463419852832910038477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22738975613235221940025651 34108463419852832910038477)
              ·
                refine ⟨12790673782444812341264429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34108463419852832910038477 12790673782444812341264429)
                ·
                  refine ⟨4796502668416804627974161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12790673782444812341264429 4796502668416804627974161)
                  ·
                    refine ⟨3597377001312603470980621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796502668416804627974161 3597377001312603470980621)
                    ·
                      refine ⟨1349016375492226301617733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3597377001312603470980621 1349016375492226301617733)
                      ·
                        rfl

theorem cell23_2627200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_2627200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627200 prefixEnd_2627200 := by exact prefixLift 2627200
  have htrace : WordTrace (prefixWord ++ tailWord_2627200) baseStart_2627200 baseEnd_2627200 := by
    simpa [prefixWord, tailWord_2627200, baseEnd_2627200] using wordTrace_append hprefix tailTrace_2627200
  have hstable : (prefixWord ++ tailWord_2627200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627200).length < 2 ^ (prefixWord ++ tailWord_2627200).sum := by decide
  have hdescent : baseEnd_2627200 < baseStart_2627200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627208 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2627208 : Nat := 118140960795 + 2627208 * 2 ^ 59
def prefixEnd_2627208 : Nat := 4983230072969 + 3 ^ 40 * 2627208 * 2
def baseEnd_2627208 : Nat := 1349020483337462270317697

theorem tailTrace_2627208 : CollatzResearch.WordTrace tailWord_2627208 prefixEnd_2627208 1349020483337462270317697 := by
  unfold tailWord_2627208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47911073933040791124681139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63881431910721054832908185 47911073933040791124681139)
  ·
    refine ⟨71866610899561186687021709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47911073933040791124681139 71866610899561186687021709)
    ·
      refine ⟨26949979087335445007633141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71866610899561186687021709 26949979087335445007633141)
      ·
        refine ⟨2526560539437697969465607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26949979087335445007633141 2526560539437697969465607)
        ·
          refine ⟨3789840809156546954198411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526560539437697969465607 3789840809156546954198411)
          ·
            refine ⟨5684761213734820431297617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789840809156546954198411 5684761213734820431297617)
            ·
              refine ⟨4263570910301115323473213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684761213734820431297617 4263570910301115323473213)
              ·
                refine ⟨1598839091362918246302455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263570910301115323473213 1598839091362918246302455)
                ·
                  refine ⟨2398258637044377369453683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598839091362918246302455 2398258637044377369453683)
                  ·
                    refine ⟨3597387955566566054180525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2398258637044377369453683 3597387955566566054180525)
                    ·
                      refine ⟨1349020483337462270317697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3597387955566566054180525 1349020483337462270317697)
                      ·
                        rfl

theorem cell23_2627208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2627208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627208 prefixEnd_2627208 := by exact prefixLift 2627208
  have htrace : WordTrace (prefixWord ++ tailWord_2627208) baseStart_2627208 baseEnd_2627208 := by
    simpa [prefixWord, tailWord_2627208, baseEnd_2627208] using wordTrace_append hprefix tailTrace_2627208
  have hstable : (prefixWord ++ tailWord_2627208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627208).length < 2 ^ (prefixWord ++ tailWord_2627208).sum := by decide
  have hdescent : baseEnd_2627208 < baseStart_2627208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627214 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2627214 : Nat := 118140960795 + 2627214 * 2 ^ 59
def prefixEnd_2627214 : Nat := 4983230072969 + 3 ^ 40 * 2627214 * 2
def baseEnd_2627214 : Nat := 1349023564221389246842669

theorem tailTrace_2627214 : CollatzResearch.WordTrace tailWord_2627214 prefixEnd_2627214 1349023564221389246842669 := by
  unfold tailWord_2627214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977795838007480659260087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63881577802706563516053797 11977795838007480659260087)
  ·
    refine ⟨17966693757011220988890131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11977795838007480659260087 17966693757011220988890131)
    ·
      refine ⟨26950040635516831483335197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17966693757011220988890131 26950040635516831483335197)
      ·
        refine ⟨10106265238318811806250699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26950040635516831483335197 10106265238318811806250699)
        ·
          refine ⟨15159397857478217709376049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106265238318811806250699 15159397857478217709376049)
          ·
            refine ⟨11369548393108663282032037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159397857478217709376049 11369548393108663282032037)
            ·
              refine ⟨2131790323707874365381007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11369548393108663282032037 2131790323707874365381007)
              ·
                refine ⟨3197685485561811548071511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131790323707874365381007 3197685485561811548071511)
                ·
                  refine ⟨4796528228342717322107267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197685485561811548071511 4796528228342717322107267)
                  ·
                    refine ⟨7194792342514075983160901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796528228342717322107267 7194792342514075983160901)
                    ·
                      refine ⟨1349023564221389246842669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7194792342514075983160901 1349023564221389246842669)
                      ·
                        rfl

theorem cell23_2627214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2627214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627214 prefixEnd_2627214 := by exact prefixLift 2627214
  have htrace : WordTrace (prefixWord ++ tailWord_2627214) baseStart_2627214 baseEnd_2627214 := by
    simpa [prefixWord, tailWord_2627214, baseEnd_2627214] using wordTrace_append hprefix tailTrace_2627214
  have hstable : (prefixWord ++ tailWord_2627214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627214).length < 2 ^ (prefixWord ++ tailWord_2627214).sum := by decide
  have hdescent : baseEnd_2627214 < baseStart_2627214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627224 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_2627224 : Nat := 118140960795 + 2627224 * 2 ^ 59
def prefixEnd_2627224 : Nat := 4983230072969 + 3 ^ 40 * 2627224 * 2
def baseEnd_2627224 : Nat := 449676233009311402572541

theorem tailTrace_2627224 : CollatzResearch.WordTrace tailWord_2627224 prefixEnd_2627224 449676233009311402572541 := by
  unfold tailWord_2627224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47911365717011808490972363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63881820956015744654629817 47911365717011808490972363)
  ·
    refine ⟨71867048575517712736458545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47911365717011808490972363 71867048575517712736458545)
    ·
      refine ⟨53900286431638284552343909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71867048575517712736458545 53900286431638284552343909)
      ·
        refine ⟨10106303705932178353564483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53900286431638284552343909 10106303705932178353564483)
        ·
          refine ⟨15159455558898267530346725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106303705932178353564483 15159455558898267530346725)
          ·
            refine ⟨2842397917293425161940011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15159455558898267530346725 2842397917293425161940011)
            ·
              refine ⟨4263596875940137742910017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842397917293425161940011 4263596875940137742910017)
              ·
                refine ⟨3197697656955103307182513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4263596875940137742910017 3197697656955103307182513)
                ·
                  refine ⟨2398273242716327480386885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197697656955103307182513 2398273242716327480386885)
                  ·
                    refine ⟨449676233009311402572541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398273242716327480386885 449676233009311402572541)
                    ·
                      rfl

theorem cell23_2627224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_2627224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627224 prefixEnd_2627224 := by exact prefixLift 2627224
  have htrace : WordTrace (prefixWord ++ tailWord_2627224) baseStart_2627224 baseEnd_2627224 := by
    simpa [prefixWord, tailWord_2627224, baseEnd_2627224] using wordTrace_append hprefix tailTrace_2627224
  have hstable : (prefixWord ++ tailWord_2627224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627224).length < 2 ^ (prefixWord ++ tailWord_2627224).sum := by decide
  have hdescent : baseEnd_2627224 < baseStart_2627224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627234 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2627234 : Nat := 118140960795 + 2627234 * 2 ^ 59
def prefixEnd_2627234 : Nat := 4983230072969 + 3 ^ 40 * 2627234 * 2
def baseEnd_2627234 : Nat := 1349033833834479168592577

theorem tailTrace_2627234 : CollatzResearch.WordTrace tailWord_2627234 prefixEnd_2627234 1349033833834479168592577 := by
  unfold tailWord_2627234
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955774040996847172452189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63882064109324925793205837 23955774040996847172452189)
  ·
    refine ⟨8983415265373817689669571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23955774040996847172452189 8983415265373817689669571)
    ·
      refine ⟨13475122898060726534504357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8983415265373817689669571 13475122898060726534504357)
      ·
        refine ⟨2526585543386386225219567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13475122898060726534504357 2526585543386386225219567)
        ·
          refine ⟨3789878315079579337829351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526585543386386225219567 3789878315079579337829351)
          ·
            refine ⟨5684817472619369006744027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789878315079579337829351 5684817472619369006744027)
            ·
              refine ⟨8527226208929053510116041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684817472619369006744027 8527226208929053510116041)
              ·
                refine ⟨6395419656696790132587031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8527226208929053510116041 6395419656696790132587031)
                ·
                  refine ⟨9593129485045185198880547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395419656696790132587031 9593129485045185198880547)
                  ·
                    refine ⟨14389694227567777798320821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9593129485045185198880547 14389694227567777798320821)
                    ·
                      refine ⟨1349033833834479168592577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14389694227567777798320821 1349033833834479168592577)
                      ·
                        rfl

theorem cell23_2627234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2627234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627234 prefixEnd_2627234 := by exact prefixLift 2627234
  have htrace : WordTrace (prefixWord ++ tailWord_2627234) baseStart_2627234 baseEnd_2627234 := by
    simpa [prefixWord, tailWord_2627234, baseEnd_2627234] using wordTrace_append hprefix tailTrace_2627234
  have hstable : (prefixWord ++ tailWord_2627234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627234).length < 2 ^ (prefixWord ++ tailWord_2627234).sum := by decide
  have hdescent : baseEnd_2627234 < baseStart_2627234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627254 : List Nat := [5, 1, 3, 1, 1, 1, 4, 7]
def baseStart_2627254 : Nat := 118140960795 + 2627254 * 2 ^ 59
def prefixEnd_2627254 : Nat := 4983230072969 + 3 ^ 40 * 2627254 * 2
def baseEnd_2627254 : Nat := 49964596423984040383055

theorem tailTrace_2627254 : CollatzResearch.WordTrace tailWord_2627254 prefixEnd_2627254 49964596423984040383055 := by
  unfold tailWord_2627254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988989101494683256596051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63882550415943288070357877 5988989101494683256596051)
  ·
    refine ⟨8983483652242024884894077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988989101494683256596051 8983483652242024884894077)
    ·
      refine ⟨3368806369590759331835279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8983483652242024884894077 3368806369590759331835279)
      ·
        refine ⟨5053209554386138997752919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368806369590759331835279 5053209554386138997752919)
        ·
          refine ⟨7579814331579208496629379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053209554386138997752919 7579814331579208496629379)
          ·
            refine ⟨11369721497368812744944069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7579814331579208496629379 11369721497368812744944069)
            ·
              refine ⟨2131822780756652389677013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11369721497368812744944069 2131822780756652389677013)
              ·
                refine ⟨49964596423984040383055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2131822780756652389677013 49964596423984040383055)
                ·
                  rfl

theorem cell23_2627254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_2627254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627254 prefixEnd_2627254 := by exact prefixLift 2627254
  have htrace : WordTrace (prefixWord ++ tailWord_2627254) baseStart_2627254 baseEnd_2627254 := by
    simpa [prefixWord, tailWord_2627254, baseEnd_2627254] using wordTrace_append hprefix tailTrace_2627254
  have hstable : (prefixWord ++ tailWord_2627254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627254).length < 2 ^ (prefixWord ++ tailWord_2627254).sum := by decide
  have hdescent : baseEnd_2627254 < baseStart_2627254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627257 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2627257 : Nat := 118140960795 + 2627257 * 2 ^ 59
def prefixEnd_2627257 : Nat := 4983230072969 + 3 ^ 40 * 2627257 * 2
def baseEnd_2627257 : Nat := 1349045643889532578604971

theorem tailTrace_2627257 : CollatzResearch.WordTrace tailWord_2627257 prefixEnd_2627257 1349045643889532578604971 := by
  unfold tailWord_2627257
  simp only [CollatzResearch.WordTrace]
  refine ⟨95823935042904063617896025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63882623361936042411930683 95823935042904063617896025)
  ·
    refine ⟨71867951282178047713422019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95823935042904063617896025 71867951282178047713422019)
    ·
      refine ⟨107801926923267071570133029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71867951282178047713422019 107801926923267071570133029)
      ·
        refine ⟨20212861298112575919399943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107801926923267071570133029 20212861298112575919399943)
        ·
          refine ⟨30319291947168863879099915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20212861298112575919399943 30319291947168863879099915)
          ·
            refine ⟨45478937920753295818649873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30319291947168863879099915 45478937920753295818649873)
            ·
              refine ⟨34109203440564971863987405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45478937920753295818649873 34109203440564971863987405)
              ·
                refine ⟨12790951290211864448995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34109203440564971863987405 12790951290211864448995277)
                ·
                  refine ⟨4796606733829449168373229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12790951290211864448995277 4796606733829449168373229)
                  ·
                    refine ⟨1798727525186043438139961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4796606733829449168373229 1798727525186043438139961)
                    ·
                      refine ⟨1349045643889532578604971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1798727525186043438139961 1349045643889532578604971)
                      ·
                        rfl

theorem cell23_2627257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2627257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627257 prefixEnd_2627257 := by exact prefixLift 2627257
  have htrace : WordTrace (prefixWord ++ tailWord_2627257) baseStart_2627257 baseEnd_2627257 := by
    simpa [prefixWord, tailWord_2627257, baseEnd_2627257] using wordTrace_append hprefix tailTrace_2627257
  have hstable : (prefixWord ++ tailWord_2627257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627257).length < 2 ^ (prefixWord ++ tailWord_2627257).sum := by decide
  have hdescent : baseEnd_2627257 < baseStart_2627257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627260 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2627260 : Nat := 118140960795 + 2627260 * 2 ^ 59
def prefixEnd_2627260 : Nat := 4983230072969 + 3 ^ 40 * 2627260 * 2
def baseEnd_2627260 : Nat := 1349047184331496066867457

theorem tailTrace_2627260 : CollatzResearch.WordTrace tailWord_2627260 prefixEnd_2627260 1349047184331496066867457 := by
  unfold tailWord_2627260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47912022230946597565127617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63882696307928796753503489 47912022230946597565127617)
  ·
    refine ⟨35934016673209948173845713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47912022230946597565127617 35934016673209948173845713)
    ·
      refine ⟨26950512504907461130384285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35934016673209948173845713 26950512504907461130384285)
      ·
        refine ⟨10106442189340297923894107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26950512504907461130384285 10106442189340297923894107)
        ·
          refine ⟨15159663284010446885841161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106442189340297923894107 15159663284010446885841161)
          ·
            refine ⟨11369747463007835164380871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159663284010446885841161 11369747463007835164380871)
            ·
              refine ⟨17054621194511752746571307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369747463007835164380871 17054621194511752746571307)
              ·
                refine ⟨25581931791767629119856961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054621194511752746571307 25581931791767629119856961)
                ·
                  refine ⟨19186448843825721839892721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25581931791767629119856961 19186448843825721839892721)
                  ·
                    refine ⟨14389836632869291379919541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19186448843825721839892721 14389836632869291379919541)
                    ·
                      refine ⟨1349047184331496066867457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14389836632869291379919541 1349047184331496066867457)
                      ·
                        rfl

theorem cell23_2627260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2627260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627260 prefixEnd_2627260 := by exact prefixLift 2627260
  have htrace : WordTrace (prefixWord ++ tailWord_2627260) baseStart_2627260 baseEnd_2627260 := by
    simpa [prefixWord, tailWord_2627260, baseEnd_2627260] using wordTrace_append hprefix tailTrace_2627260
  have hstable : (prefixWord ++ tailWord_2627260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627260).length < 2 ^ (prefixWord ++ tailWord_2627260).sum := by decide
  have hdescent : baseEnd_2627260 < baseStart_2627260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627300 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_2627300 : Nat := 118140960795 + 2627300 * 2 ^ 59
def prefixEnd_2627300 : Nat := 4983230072969 + 3 ^ 40 * 2627300 * 2
def baseEnd_2627300 : Nat := 1349067723557675910367273

theorem tailTrace_2627300 : CollatzResearch.WordTrace tailWord_2627300 prefixEnd_2627300 1349067723557675910367273 := by
  unfold tailWord_2627300
  simp only [CollatzResearch.WordTrace]
  refine ⟨47912751690874140980855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63883668921165521307807569 47912751690874140980855677)
  ·
    refine ⟨17967281884077802867820879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47912751690874140980855677 17967281884077802867820879)
    ·
      refine ⟨26950922826116704301731319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17967281884077802867820879 26950922826116704301731319)
      ·
        refine ⟨40426384239175056452596979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26950922826116704301731319 40426384239175056452596979)
        ·
          refine ⟨60639576358762584678895469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40426384239175056452596979 60639576358762584678895469)
          ·
            refine ⟨22739841134535969254585801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60639576358762584678895469 22739841134535969254585801)
            ·
              refine ⟨17054880850901976940939351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22739841134535969254585801 17054880850901976940939351)
              ·
                refine ⟨25582321276352965411409027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054880850901976940939351 25582321276352965411409027)
                ·
                  refine ⟨38373481914529448117113541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25582321276352965411409027 38373481914529448117113541)
                  ·
                    refine ⟨7195027858974271521958789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38373481914529448117113541 7195027858974271521958789)
                    ·
                      refine ⟨1349067723557675910367273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7195027858974271521958789 1349067723557675910367273)
                      ·
                        rfl

theorem cell23_2627300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_2627300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627300 prefixEnd_2627300 := by exact prefixLift 2627300
  have htrace : WordTrace (prefixWord ++ tailWord_2627300) baseStart_2627300 baseEnd_2627300 := by
    simpa [prefixWord, tailWord_2627300, baseEnd_2627300] using wordTrace_append hprefix tailTrace_2627300
  have hstable : (prefixWord ++ tailWord_2627300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627300).length < 2 ^ (prefixWord ++ tailWord_2627300).sum := by decide
  have hdescent : baseEnd_2627300 < baseStart_2627300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627310 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_2627310 : Nat := 118140960795 + 2627310 * 2 ^ 59
def prefixEnd_2627310 : Nat := 4983230072969 + 3 ^ 40 * 2627310 * 2
def baseEnd_2627310 : Nat := 149896984262691207915803

theorem tailTrace_2627310 : CollatzResearch.WordTrace tailWord_2627310 prefixEnd_2627310 149896984262691207915803 := by
  unfold tailWord_2627310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978233513964006708696923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63883912074474702446383589 11978233513964006708696923)
  ·
    refine ⟨17967350270946010063045385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11978233513964006708696923 17967350270946010063045385)
    ·
      refine ⟨13475512703209507547284039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17967350270946010063045385 13475512703209507547284039)
      ·
        refine ⟨20213269054814261320926059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475512703209507547284039 20213269054814261320926059)
        ·
          refine ⟨30319903582221391981389089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20213269054814261320926059 30319903582221391981389089)
          ·
            refine ⟨22739927686666043986041817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30319903582221391981389089 22739927686666043986041817)
            ·
              refine ⟨17054945764999532989531363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22739927686666043986041817 17054945764999532989531363)
              ·
                refine ⟨25582418647499299484297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17054945764999532989531363 25582418647499299484297045)
                ·
                  refine ⟨149896984262691207915803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25582418647499299484297045 149896984262691207915803)
                  ·
                    rfl

theorem cell23_2627310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_2627310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627310 prefixEnd_2627310 := by exact prefixLift 2627310
  have htrace : WordTrace (prefixWord ++ tailWord_2627310) baseStart_2627310 baseEnd_2627310 := by
    simpa [prefixWord, tailWord_2627310, baseEnd_2627310] using wordTrace_append hprefix tailTrace_2627310
  have hstable : (prefixWord ++ tailWord_2627310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627310).length < 2 ^ (prefixWord ++ tailWord_2627310).sum := by decide
  have hdescent : baseEnd_2627310 < baseStart_2627310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627320 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_2627320 : Nat := 118140960795 + 2627320 * 2 ^ 59
def prefixEnd_2627320 : Nat := 4983230072969 + 3 ^ 40 * 2627320 * 2
def baseEnd_2627320 : Nat := 1349077993170765832117181

theorem tailTrace_2627320 : CollatzResearch.WordTrace tailWord_2627320 prefixEnd_2627320 1349077993170765832117181 := by
  unfold tailWord_2627320
  simp only [CollatzResearch.WordTrace]
  refine ⟨47913116420837912688719707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63884155227783883584959609 47913116420837912688719707)
  ·
    refine ⟨71869674631256869033079561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47913116420837912688719707 71869674631256869033079561)
    ·
      refine ⟨53902255973442651774809671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71869674631256869033079561 53902255973442651774809671)
      ·
        refine ⟨80853383960163977662214507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53902255973442651774809671 80853383960163977662214507)
        ·
          refine ⟨121280075940245966493321761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80853383960163977662214507 121280075940245966493321761)
          ·
            refine ⟨90960056955184474869991321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121280075940245966493321761 90960056955184474869991321)
            ·
              refine ⟨68220042716388356152493491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90960056955184474869991321 68220042716388356152493491)
              ·
                refine ⟨102330064074582534228740237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68220042716388356152493491 102330064074582534228740237)
                ·
                  refine ⟨38373774027968450335777589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102330064074582534228740237 38373774027968450335777589)
                  ·
                    refine ⟨3597541315122042218979149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38373774027968450335777589 3597541315122042218979149)
                    ·
                      refine ⟨1349077993170765832117181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3597541315122042218979149 1349077993170765832117181)
                      ·
                        rfl

theorem cell23_2627320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_2627320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627320 prefixEnd_2627320 := by exact prefixLift 2627320
  have htrace : WordTrace (prefixWord ++ tailWord_2627320) baseStart_2627320 baseEnd_2627320 := by
    simpa [prefixWord, tailWord_2627320, baseEnd_2627320] using wordTrace_append hprefix tailTrace_2627320
  have hstable : (prefixWord ++ tailWord_2627320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627320).length < 2 ^ (prefixWord ++ tailWord_2627320).sum := by decide
  have hdescent : baseEnd_2627320 < baseStart_2627320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627374 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2627374 : Nat := 118140960795 + 2627374 * 2 ^ 59
def prefixEnd_2627374 : Nat := 4983230072969 + 3 ^ 40 * 2627374 * 2
def baseEnd_2627374 : Nat := 449701907042036206947311

theorem tailTrace_2627374 : CollatzResearch.WordTrace tailWord_2627374 prefixEnd_2627374 449701907042036206947311 := by
  unfold tailWord_2627374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978525297935024074988147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63885468255653461733270117 11978525297935024074988147)
  ·
    refine ⟨17967787946902536112482221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11978525297935024074988147 17967787946902536112482221)
    ·
      refine ⟨6737920480088451042180833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17967787946902536112482221 6737920480088451042180833)
      ·
        refine ⟨5053440360066338281635625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6737920480088451042180833 5053440360066338281635625)
        ·
          refine ⟨3790080270049753711226719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5053440360066338281635625 3790080270049753711226719)
          ·
            refine ⟨5685120405074630566840079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790080270049753711226719 5685120405074630566840079)
            ·
              refine ⟨8527680607611945850260119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685120405074630566840079 8527680607611945850260119)
              ·
                refine ⟨12791520911417918775390179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8527680607611945850260119 12791520911417918775390179)
                ·
                  refine ⟨19187281367126878163085269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12791520911417918775390179 19187281367126878163085269)
                  ·
                    refine ⟨449701907042036206947311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19187281367126878163085269 449701907042036206947311)
                    ·
                      rfl

theorem cell23_2627374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2627374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627374 prefixEnd_2627374 := by exact prefixLift 2627374
  have htrace : WordTrace (prefixWord ++ tailWord_2627374) baseStart_2627374 baseEnd_2627374 := by
    simpa [prefixWord, tailWord_2627374, baseEnd_2627374] using wordTrace_append hprefix tailTrace_2627374
  have hstable : (prefixWord ++ tailWord_2627374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627374).length < 2 ^ (prefixWord ++ tailWord_2627374).sum := by decide
  have hdescent : baseEnd_2627374 < baseStart_2627374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627377 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2627377 : Nat := 118140960795 + 2627377 * 2 ^ 59
def prefixEnd_2627377 : Nat := 4983230072969 + 3 ^ 40 * 2627377 * 2
def baseEnd_2627377 : Nat := 1349107261568072109104419

theorem tailTrace_2627377 : CollatzResearch.WordTrace tailWord_2627377 prefixEnd_2627377 1349107261568072109104419 := by
  unfold tailWord_2627377
  simp only [CollatzResearch.WordTrace]
  refine ⟨95828311802469324112264385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63885541201646216074842923 95828311802469324112264385)
  ·
    refine ⟨71871233851851993084198289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95828311802469324112264385 71871233851851993084198289)
    ·
      refine ⟨53903425388888994813148717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71871233851851993084198289 53903425388888994813148717)
      ·
        refine ⟨20213784520833373054930769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53903425388888994813148717 20213784520833373054930769)
        ·
          refine ⟨15160338390625029791198077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20213784520833373054930769 15160338390625029791198077)
          ·
            refine ⟨5685126896484386171699279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15160338390625029791198077 5685126896484386171699279)
            ·
              refine ⟨8527690344726579257548919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685126896484386171699279 8527690344726579257548919)
              ·
                refine ⟨12791535517089868886323379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8527690344726579257548919 12791535517089868886323379)
                ·
                  refine ⟨19187303275634803329485069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12791535517089868886323379 19187303275634803329485069)
                  ·
                    refine ⟨7195238728363051248556901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19187303275634803329485069 7195238728363051248556901)
                    ·
                      refine ⟨1349107261568072109104419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7195238728363051248556901 1349107261568072109104419)
                      ·
                        rfl

theorem cell23_2627377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2627377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627377 prefixEnd_2627377 := by exact prefixLift 2627377
  have htrace : WordTrace (prefixWord ++ tailWord_2627377) baseStart_2627377 baseEnd_2627377 := by
    simpa [prefixWord, tailWord_2627377, baseEnd_2627377] using wordTrace_append hprefix tailTrace_2627377
  have hstable : (prefixWord ++ tailWord_2627377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627377).length < 2 ^ (prefixWord ++ tailWord_2627377).sum := by decide
  have hdescent : baseEnd_2627377 < baseStart_2627377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627397 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_2627397 : Nat := 118140960795 + 2627397 * 2 ^ 59
def prefixEnd_2627397 : Nat := 4983230072969 + 3 ^ 40 * 2627397 * 2
def baseEnd_2627397 : Nat := 1349117531181162030854327

theorem tailTrace_2627397 : CollatzResearch.WordTrace tailWord_2627397 prefixEnd_2627397 1349117531181162030854327 := by
  unfold tailWord_2627397
  simp only [CollatzResearch.WordTrace]
  refine ⟨95829041262396867527992445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63886027508264578351994963 95829041262396867527992445)
  ·
    refine ⟨35935890473398825322997167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95829041262396867527992445 35935890473398825322997167)
    ·
      refine ⟨53903835710098237984495751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35935890473398825322997167 53903835710098237984495751)
      ·
        refine ⟨80855753565147356976743627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53903835710098237984495751 80855753565147356976743627)
        ·
          refine ⟨121283630347721035465115441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80855753565147356976743627 121283630347721035465115441)
          ·
            refine ⟨90962722760790776598836581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121283630347721035465115441 90962722760790776598836581)
            ·
              refine ⟨17055510517648270612281859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90962722760790776598836581 17055510517648270612281859)
              ·
                refine ⟨25583265776472405918422789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17055510517648270612281859 25583265776472405918422789)
                ·
                  refine ⟨4796862333088576109704273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25583265776472405918422789 4796862333088576109704273)
                  ·
                    refine ⟨3597646749816432082278205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796862333088576109704273 3597646749816432082278205)
                    ·
                      refine ⟨1349117531181162030854327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3597646749816432082278205 1349117531181162030854327)
                      ·
                        rfl

theorem cell23_2627397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_2627397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627397 prefixEnd_2627397 := by exact prefixLift 2627397
  have htrace : WordTrace (prefixWord ++ tailWord_2627397) baseStart_2627397 baseEnd_2627397 := by
    simpa [prefixWord, tailWord_2627397, baseEnd_2627397] using wordTrace_append hprefix tailTrace_2627397
  have hstable : (prefixWord ++ tailWord_2627397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627397).length < 2 ^ (prefixWord ++ tailWord_2627397).sum := by decide
  have hdescent : baseEnd_2627397 < baseStart_2627397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627438 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2627438 : Nat := 118140960795 + 2627438 * 2 ^ 59
def prefixEnd_2627438 : Nat := 4983230072969 + 3 ^ 40 * 2627438 * 2
def baseEnd_2627438 : Nat := 449712861295998790147213

theorem tailTrace_2627438 : CollatzResearch.WordTrace tailWord_2627438 prefixEnd_2627438 449712861295998790147213 := by
  unfold tailWord_2627438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978817081906041441279371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63887024436832221020156645 11978817081906041441279371)
  ·
    refine ⟨17968225622859062161919057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11978817081906041441279371 17968225622859062161919057)
    ·
      refine ⟨13476169217144296621439293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17968225622859062161919057 13476169217144296621439293)
      ·
        refine ⟨5053563456429111233039735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13476169217144296621439293 5053563456429111233039735)
        ·
          refine ⟨7580345184643666849559603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053563456429111233039735 7580345184643666849559603)
          ·
            refine ⟨11370517776965500274339405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7580345184643666849559603 11370517776965500274339405)
            ·
              refine ⟨4263944166362062602877277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11370517776965500274339405 4263944166362062602877277)
              ·
                refine ⟨1598979062385773476078979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263944166362062602877277 1598979062385773476078979)
                ·
                  refine ⟨2398468593578660214118469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598979062385773476078979 2398468593578660214118469)
                  ·
                    refine ⟨449712861295998790147213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398468593578660214118469 449712861295998790147213)
                    ·
                      rfl

theorem cell23_2627438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2627438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627438 prefixEnd_2627438 := by exact prefixLift 2627438
  have htrace : WordTrace (prefixWord ++ tailWord_2627438) baseStart_2627438 baseEnd_2627438 := by
    simpa [prefixWord, tailWord_2627438, baseEnd_2627438] using wordTrace_append hprefix tailTrace_2627438
  have hstable : (prefixWord ++ tailWord_2627438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627438).length < 2 ^ (prefixWord ++ tailWord_2627438).sum := by decide
  have hdescent : baseEnd_2627438 < baseStart_2627438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627467 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4]
def baseStart_2627467 : Nat := 118140960795 + 2627467 * 2 ^ 59
def prefixEnd_2627467 : Nat := 4983230072969 + 3 ^ 40 * 2627467 * 2
def baseEnd_2627467 : Nat := 1349153474826976756979005

theorem tailTrace_2627467 : CollatzResearch.WordTrace tailWord_2627467 prefixEnd_2627467 1349153474826976756979005 := by
  unfold tailWord_2627467
  simp only [CollatzResearch.WordTrace]
  refine ⟨95831594372143269483040655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63887729581428846322027103 95831594372143269483040655)
  ·
    refine ⟨143747391558214904224560983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95831594372143269483040655 143747391558214904224560983)
    ·
      refine ⟨215621087337322356336841475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143747391558214904224560983 215621087337322356336841475)
      ·
        refine ⟨323431631005983534505262213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215621087337322356336841475 323431631005983534505262213)
        ·
          refine ⟨60643430813621912719736665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323431631005983534505262213 60643430813621912719736665)
          ·
            refine ⟨45482573110216434539802499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60643430813621912719736665 45482573110216434539802499)
            ·
              refine ⟨68223859665324651809703749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45482573110216434539802499 68223859665324651809703749)
              ·
                refine ⟨12791973687248372214319453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68223859665324651809703749 12791973687248372214319453)
                ·
                  refine ⟨4796990132718139580369795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12791973687248372214319453 4796990132718139580369795)
                  ·
                    refine ⟨7195485199077209370554693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4796990132718139580369795 7195485199077209370554693)
                    ·
                      refine ⟨1349153474826976756979005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7195485199077209370554693 1349153474826976756979005)
                      ·
                        rfl

theorem cell23_2627467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_2627467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627467 prefixEnd_2627467 := by exact prefixLift 2627467
  have htrace : WordTrace (prefixWord ++ tailWord_2627467) baseStart_2627467 baseEnd_2627467 := by
    simpa [prefixWord, tailWord_2627467, baseEnd_2627467] using wordTrace_append hprefix tailTrace_2627467
  have hstable : (prefixWord ++ tailWord_2627467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627467).length < 2 ^ (prefixWord ++ tailWord_2627467).sum := by decide
  have hdescent : baseEnd_2627467 < baseStart_2627467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627477 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2627477 : Nat := 118140960795 + 2627477 * 2 ^ 59
def prefixEnd_2627477 : Nat := 4983230072969 + 3 ^ 40 * 2627477 * 2
def baseEnd_2627477 : Nat := 449719536544507239284653

theorem tailTrace_2627477 : CollatzResearch.WordTrace tailWord_2627477 prefixEnd_2627477 449719536544507239284653 := by
  unfold tailWord_2627477
  simp only [CollatzResearch.WordTrace]
  refine ⟨95831959102107041190904685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63887972734738027460603123 95831959102107041190904685)
  ·
    refine ⟨35936984663290140446589257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95831959102107041190904685 35936984663290140446589257)
    ·
      refine ⟨26952738497467605334941943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35936984663290140446589257 26952738497467605334941943)
      ·
        refine ⟨40429107746201408002412915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26952738497467605334941943 40429107746201408002412915)
        ·
          refine ⟨60643661619302112003619373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40429107746201408002412915 60643661619302112003619373)
          ·
            refine ⟨22741373107238292001357265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60643661619302112003619373 22741373107238292001357265)
            ·
              refine ⟨17056029830428719001017949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22741373107238292001357265 17056029830428719001017949)
              ·
                refine ⟨6396011186410769625381731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17056029830428719001017949 6396011186410769625381731)
                ·
                  refine ⟨9594016779616154438072597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396011186410769625381731 9594016779616154438072597)
                  ·
                    refine ⟨449719536544507239284653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9594016779616154438072597 449719536544507239284653)
                    ·
                      rfl

theorem cell23_2627477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2627477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627477 prefixEnd_2627477 := by exact prefixLift 2627477
  have htrace : WordTrace (prefixWord ++ tailWord_2627477) baseStart_2627477 baseEnd_2627477 := by
    simpa [prefixWord, tailWord_2627477, baseEnd_2627477] using wordTrace_append hprefix tailTrace_2627477
  have hstable : (prefixWord ++ tailWord_2627477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627477).length < 2 ^ (prefixWord ++ tailWord_2627477).sum := by decide
  have hdescent : baseEnd_2627477 < baseStart_2627477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627567 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 6]
def baseStart_2627567 : Nat := 118140960795 + 2627567 * 2 ^ 59
def prefixEnd_2627567 : Nat := 4983230072969 + 3 ^ 40 * 2627567 * 2
def baseEnd_2627567 : Nat := 449734940964142121909515

theorem tailTrace_2627567 : CollatzResearch.WordTrace tailWord_2627567 prefixEnd_2627567 449734940964142121909515 := by
  unfold tailWord_2627567
  simp only [CollatzResearch.WordTrace]
  refine ⟨95835241671780986561680955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63890161114520657707787303 95835241671780986561680955)
  ·
    refine ⟨143752862507671479842521433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95835241671780986561680955 143752862507671479842521433)
    ·
      refine ⟨107814646880753609881891075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143752862507671479842521433 107814646880753609881891075)
      ·
        refine ⟨161721970321130414822836613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107814646880753609881891075 161721970321130414822836613)
        ·
          refine ⟨30322869435211952779281865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161721970321130414822836613 30322869435211952779281865)
          ·
            refine ⟨22742152076408964584461399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30322869435211952779281865 22742152076408964584461399)
            ·
              refine ⟨34113228114613446876692099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22742152076408964584461399 34113228114613446876692099)
              ·
                refine ⟨51169842171920170315038149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34113228114613446876692099 51169842171920170315038149)
                ·
                  refine ⟨9594345407235031934069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51169842171920170315038149 9594345407235031934069653)
                  ·
                    refine ⟨449734940964142121909515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9594345407235031934069653 449734940964142121909515)
                    ·
                      rfl

theorem cell23_2627567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_2627567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627567 prefixEnd_2627567 := by exact prefixLift 2627567
  have htrace : WordTrace (prefixWord ++ tailWord_2627567) baseStart_2627567 baseEnd_2627567 := by
    simpa [prefixWord, tailWord_2627567, baseEnd_2627567] using wordTrace_append hprefix tailTrace_2627567
  have hstable : (prefixWord ++ tailWord_2627567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627567).length < 2 ^ (prefixWord ++ tailWord_2627567).sum := by decide
  have hdescent : baseEnd_2627567 < baseStart_2627567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627627 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 7]
def baseStart_2627627 : Nat := 118140960795 + 2627627 * 2 ^ 59
def prefixEnd_2627627 : Nat := 4983230072969 + 3 ^ 40 * 2627627 * 2
def baseEnd_2627627 : Nat := 449745210577232043659423

theorem tailTrace_2627627 : CollatzResearch.WordTrace tailWord_2627627 prefixEnd_2627627 449745210577232043659423 := by
  unfold tailWord_2627627
  simp only [CollatzResearch.WordTrace]
  refine ⟨95837430051563616808865135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63891620034375744539243423 95837430051563616808865135)
  ·
    refine ⟨143756145077345425213297703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95837430051563616808865135 143756145077345425213297703)
    ·
      refine ⟨215634217616018137819946555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143756145077345425213297703 215634217616018137819946555)
      ·
        refine ⟨323451326424027206729919833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215634217616018137819946555 323451326424027206729919833)
        ·
          refine ⟨242588494818020405047439875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323451326424027206729919833 242588494818020405047439875)
          ·
            refine ⟨363882742227030607571159813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242588494818020405047439875 363882742227030607571159813)
            ·
              refine ⟨68228014167568238919592465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 363882742227030607571159813 68228014167568238919592465)
              ·
                refine ⟨51171010625676179189694349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68228014167568238919592465 51171010625676179189694349)
                ·
                  refine ⟨19189128984628567196135381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51171010625676179189694349 19189128984628567196135381)
                  ·
                    refine ⟨449745210577232043659423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19189128984628567196135381 449745210577232043659423)
                    ·
                      rfl

theorem cell23_2627627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_2627627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627627 prefixEnd_2627627 := by exact prefixLift 2627627
  have htrace : WordTrace (prefixWord ++ tailWord_2627627) baseStart_2627627 baseEnd_2627627 := by
    simpa [prefixWord, tailWord_2627627, baseEnd_2627627] using wordTrace_append hprefix tailTrace_2627627
  have hstable : (prefixWord ++ tailWord_2627627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627627).length < 2 ^ (prefixWord ++ tailWord_2627627).sum := by decide
  have hdescent : baseEnd_2627627 < baseStart_2627627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627644 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_2627644 : Nat := 118140960795 + 2627644 * 2 ^ 59
def prefixEnd_2627644 : Nat := 4983230072969 + 3 ^ 40 * 2627644 * 2
def baseEnd_2627644 : Nat := 449748120300940854821897

theorem tailTrace_2627644 : CollatzResearch.WordTrace tailWord_2627644 prefixEnd_2627644 449748120300940854821897 := by
  unfold tailWord_2627644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47919025046251014356116993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63892033395001352474822657 47919025046251014356116993)
  ·
    refine ⟨35939268784688260767087745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47919025046251014356116993 35939268784688260767087745)
    ·
      refine ⟨26954451588516195575315809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35939268784688260767087745 26954451588516195575315809)
      ·
        refine ⟨20215838691387146681486857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26954451588516195575315809 20215838691387146681486857)
        ·
          refine ⟨15161879018540360011115143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20215838691387146681486857 15161879018540360011115143)
          ·
            refine ⟨22742818527810540016672715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15161879018540360011115143 22742818527810540016672715)
            ·
              refine ⟨34114227791715810025009073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22742818527810540016672715 34114227791715810025009073)
              ·
                refine ⟨25585670843786857518756805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34114227791715810025009073 25585670843786857518756805)
                ·
                  refine ⟨4797313283210035784766901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25585670843786857518756805 4797313283210035784766901)
                  ·
                    refine ⟨449748120300940854821897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4797313283210035784766901 449748120300940854821897)
                    ·
                      rfl

theorem cell23_2627644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_2627644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627644 prefixEnd_2627644 := by exact prefixLift 2627644
  have htrace : WordTrace (prefixWord ++ tailWord_2627644) baseStart_2627644 baseEnd_2627644 := by
    simpa [prefixWord, tailWord_2627644, baseEnd_2627644] using wordTrace_append hprefix tailTrace_2627644
  have hstable : (prefixWord ++ tailWord_2627644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627644).length < 2 ^ (prefixWord ++ tailWord_2627644).sum := by decide
  have hdescent : baseEnd_2627644 < baseStart_2627644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627681 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_2627681 : Nat := 118140960795 + 2627681 * 2 ^ 59
def prefixEnd_2627681 : Nat := 4983230072969 + 3 ^ 40 * 2627681 * 2
def baseEnd_2627681 : Nat := 1349263359687038919703021

theorem tailTrace_2627681 : CollatzResearch.WordTrace tailWord_2627681 prefixEnd_2627681 1349263359687038919703021 := by
  unfold tailWord_2627681
  simp only [CollatzResearch.WordTrace]
  refine ⟨95839399593367984031330897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63892933062245322687553931 95839399593367984031330897)
  ·
    refine ⟨71879549695025988023498173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95839399593367984031330897 71879549695025988023498173)
    ·
      refine ⟨26954831135634745508811815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71879549695025988023498173 26954831135634745508811815)
      ·
        refine ⟨40432246703452118263217723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26954831135634745508811815 40432246703452118263217723)
        ·
          refine ⟨60648370055178177394826585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40432246703452118263217723 60648370055178177394826585)
          ·
            refine ⟨45486277541383633046119939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60648370055178177394826585 45486277541383633046119939)
            ·
              refine ⟨68229416312075449569179909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45486277541383633046119939 68229416312075449569179909)
              ·
                refine ⟨12793015558514146794221233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68229416312075449569179909 12793015558514146794221233)
                ·
                  refine ⟨9594761668885610095665925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12793015558514146794221233 9594761668885610095665925)
                  ·
                    refine ⟨1799017812916051892937361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9594761668885610095665925 1799017812916051892937361)
                    ·
                      refine ⟨1349263359687038919703021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799017812916051892937361 1349263359687038919703021)
                      ·
                        rfl

theorem cell23_2627681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_2627681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627681 prefixEnd_2627681 := by exact prefixLift 2627681
  have htrace : WordTrace (prefixWord ++ tailWord_2627681) baseStart_2627681 baseEnd_2627681 := by
    simpa [prefixWord, tailWord_2627681, baseEnd_2627681] using wordTrace_append hprefix tailTrace_2627681
  have hstable : (prefixWord ++ tailWord_2627681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627681).length < 2 ^ (prefixWord ++ tailWord_2627681).sum := by decide
  have hdescent : baseEnd_2627681 < baseStart_2627681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627682 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_2627682 : Nat := 118140960795 + 2627682 * 2 ^ 59
def prefixEnd_2627682 : Nat := 4983230072969 + 3 ^ 40 * 2627682 * 2
def baseEnd_2627682 : Nat := 149918208129743712865613

theorem tailTrace_2627682 : CollatzResearch.WordTrace tailWord_2627682 prefixEnd_2627682 149918208129743712865613 := by
  unfold tailWord_2627682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23959859016591090300529325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63892957377576240801411533 23959859016591090300529325)
  ·
    refine ⟨8984947131221658862698497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23959859016591090300529325 8984947131221658862698497)
    ·
      refine ⟨6738710348416244147023873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8984947131221658862698497 6738710348416244147023873)
      ·
        refine ⟨5054032761312183110267905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6738710348416244147023873 5054032761312183110267905)
        ·
          refine ⟨3790524570984137332700929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054032761312183110267905 3790524570984137332700929)
          ·
            refine ⟨2842893428238102999525697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790524570984137332700929 2842893428238102999525697)
            ·
              refine ⟨2132170071178577249644273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842893428238102999525697 2132170071178577249644273)
              ·
                refine ⟨1599127553383932937233205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132170071178577249644273 1599127553383932937233205)
                ·
                  refine ⟨149918208129743712865613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599127553383932937233205 149918208129743712865613)
                  ·
                    rfl

theorem cell23_2627682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_2627682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627682 prefixEnd_2627682 := by exact prefixLift 2627682
  have htrace : WordTrace (prefixWord ++ tailWord_2627682) baseStart_2627682 baseEnd_2627682 := by
    simpa [prefixWord, tailWord_2627682, baseEnd_2627682] using wordTrace_append hprefix tailTrace_2627682
  have hstable : (prefixWord ++ tailWord_2627682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627682).length < 2 ^ (prefixWord ++ tailWord_2627682).sum := by decide
  have hdescent : baseEnd_2627682 < baseStart_2627682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627698 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2627698 : Nat := 118140960795 + 2627698 * 2 ^ 59
def prefixEnd_2627698 : Nat := 4983230072969 + 3 ^ 40 * 2627698 * 2
def baseEnd_2627698 : Nat := 1349272088858165353190443

theorem tailTrace_2627698 : CollatzResearch.WordTrace tailWord_2627698 prefixEnd_2627698 1349272088858165353190443 := by
  unfold tailWord_2627698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23960004908576598983674937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63893346422870930623133165 23960004908576598983674937)
  ·
    refine ⟨17970003681432449237756203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23960004908576598983674937 17970003681432449237756203)
    ·
      refine ⟨26955005522148673856634305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970003681432449237756203 26955005522148673856634305)
      ·
        refine ⟨20216254141611505392475729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26955005522148673856634305 20216254141611505392475729)
        ·
          refine ⟨15162190606208629044356797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20216254141611505392475729 15162190606208629044356797)
          ·
            refine ⟨5685821477328235891633799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15162190606208629044356797 5685821477328235891633799)
            ·
              refine ⟨8528732215992353837450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685821477328235891633799 8528732215992353837450699)
              ·
                refine ⟨12793098323988530756176049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8528732215992353837450699 12793098323988530756176049)
                ·
                  refine ⟨9594823742991398067132037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12793098323988530756176049 9594823742991398067132037)
                  ·
                    refine ⟨1799029451810887137587257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9594823742991398067132037 1799029451810887137587257)
                    ·
                      refine ⟨1349272088858165353190443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799029451810887137587257 1349272088858165353190443)
                      ·
                        rfl

theorem cell23_2627698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2627698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627698 prefixEnd_2627698 := by exact prefixLift 2627698
  have htrace : WordTrace (prefixWord ++ tailWord_2627698) baseStart_2627698 baseEnd_2627698 := by
    simpa [prefixWord, tailWord_2627698, baseEnd_2627698] using wordTrace_append hprefix tailTrace_2627698
  have hstable : (prefixWord ++ tailWord_2627698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627698).length < 2 ^ (prefixWord ++ tailWord_2627698).sum := by decide
  have hdescent : baseEnd_2627698 < baseStart_2627698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627731 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 3]
def baseStart_2627731 : Nat := 118140960795 + 2627731 * 2 ^ 59
def prefixEnd_2627731 : Nat := 4983230072969 + 3 ^ 40 * 2627731 * 2
def baseEnd_2627731 : Nat := 1349289033719763724077791

theorem tailTrace_2627731 : CollatzResearch.WordTrace tailWord_2627731 prefixEnd_2627731 1349289033719763724077791 := by
  unfold tailWord_2627731
  simp only [CollatzResearch.WordTrace]
  refine ⟨95841223243186842570651047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63894148828791228380434031 95841223243186842570651047)
  ·
    refine ⟨143761834864780263855976571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95841223243186842570651047 143761834864780263855976571)
    ·
      refine ⟨215642752297170395783964857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143761834864780263855976571 215642752297170395783964857)
      ·
        refine ⟨161732064222877796837973643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215642752297170395783964857 161732064222877796837973643)
        ·
          refine ⟨242598096334316695256960465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161732064222877796837973643 242598096334316695256960465)
          ·
            refine ⟨181948572250737521442720349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242598096334316695256960465 181948572250737521442720349)
            ·
              refine ⟨68230714594026570541020131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181948572250737521442720349 68230714594026570541020131)
              ·
                refine ⟨102346071891039855811530197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68230714594026570541020131 102346071891039855811530197)
                ·
                  refine ⟨2398736059946246620582739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102346071891039855811530197 2398736059946246620582739)
                  ·
                    refine ⟨3598104089919369930874109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2398736059946246620582739 3598104089919369930874109)
                    ·
                      refine ⟨1349289033719763724077791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3598104089919369930874109 1349289033719763724077791)
                      ·
                        rfl

theorem cell23_2627731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_2627731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627731 prefixEnd_2627731 := by exact prefixLift 2627731
  have htrace : WordTrace (prefixWord ++ tailWord_2627731) baseStart_2627731 baseEnd_2627731 := by
    simpa [prefixWord, tailWord_2627731, baseEnd_2627731] using wordTrace_append hprefix tailTrace_2627731
  have hstable : (prefixWord ++ tailWord_2627731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627731).length < 2 ^ (prefixWord ++ tailWord_2627731).sum := by decide
  have hdescent : baseEnd_2627731 < baseStart_2627731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627771 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 6, 2]
def baseStart_2627771 : Nat := 118140960795 + 2627771 * 2 ^ 59
def prefixEnd_2627771 : Nat := 4983230072969 + 3 ^ 40 * 2627771 * 2
def baseEnd_2627771 : Nat := 1349309572945943567577607

theorem tailTrace_2627771 : CollatzResearch.WordTrace tailWord_2627771 prefixEnd_2627771 1349309572945943567577607 := by
  unfold tailWord_2627771
  simp only [CollatzResearch.WordTrace]
  refine ⟨95842682163041929402107167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63895121442027952934738111 95842682163041929402107167)
  ·
    refine ⟨143764023244562894103160751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95842682163041929402107167 143764023244562894103160751)
    ·
      refine ⟨215646034866844341154741127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143764023244562894103160751 215646034866844341154741127)
      ·
        refine ⟨323469052300266511732111691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215646034866844341154741127 323469052300266511732111691)
        ·
          refine ⟨485203578450399767598167537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323469052300266511732111691 485203578450399767598167537)
          ·
            refine ⟨363902683837799825698625653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485203578450399767598167537 363902683837799825698625653)
            ·
              refine ⟨34115876609793733659246155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363902683837799825698625653 34115876609793733659246155)
              ·
                refine ⟨51173814914690600488869233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34115876609793733659246155 51173814914690600488869233)
                ·
                  refine ⟨38380361186017950366651925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51173814914690600488869233 38380361186017950366651925)
                  ·
                    refine ⟨1799079430594591423436809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38380361186017950366651925 1799079430594591423436809)
                    ·
                      refine ⟨1349309572945943567577607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799079430594591423436809 1349309572945943567577607)
                      ·
                        rfl

theorem cell23_2627771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 6, 2].length) (baseStart_2627771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627771 prefixEnd_2627771 := by exact prefixLift 2627771
  have htrace : WordTrace (prefixWord ++ tailWord_2627771) baseStart_2627771 baseEnd_2627771 := by
    simpa [prefixWord, tailWord_2627771, baseEnd_2627771] using wordTrace_append hprefix tailTrace_2627771
  have hstable : (prefixWord ++ tailWord_2627771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627771).length < 2 ^ (prefixWord ++ tailWord_2627771).sum := by decide
  have hdescent : baseEnd_2627771 < baseStart_2627771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627781 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_2627781 : Nat := 118140960795 + 2627781 * 2 ^ 59
def prefixEnd_2627781 : Nat := 4983230072969 + 3 ^ 40 * 2627781 * 2
def baseEnd_2627781 : Nat := 449771569250829509484187

theorem tailTrace_2627781 : CollatzResearch.WordTrace tailWord_2627781 prefixEnd_2627781 449771569250829509484187 := by
  unfold tailWord_2627781
  simp only [CollatzResearch.WordTrace]
  refine ⟨95843046893005701109971197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63895364595337134073314131 95843046893005701109971197)
  ·
    refine ⟨35941142584877137916239199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95843046893005701109971197 35941142584877137916239199)
    ·
      refine ⟨53911713877315706874358799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35941142584877137916239199 53911713877315706874358799)
      ·
        refine ⟨80867570815973560311538199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53911713877315706874358799 80867570815973560311538199)
        ·
          refine ⟨121301356223960340467307299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80867570815973560311538199 121301356223960340467307299)
          ·
            refine ⟨181952034335940510700960949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121301356223960340467307299 181952034335940510700960949)
            ·
              refine ⟨17058003218994422878215089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181952034335940510700960949 17058003218994422878215089)
              ·
                refine ⟨12793502414245817158661317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17058003218994422878215089 12793502414245817158661317)
                ·
                  refine ⟨2398781702671090717248997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12793502414245817158661317 2398781702671090717248997)
                  ·
                    refine ⟨449771569250829509484187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398781702671090717248997 449771569250829509484187)
                    ·
                      rfl

theorem cell23_2627781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_2627781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627781 prefixEnd_2627781 := by exact prefixLift 2627781
  have htrace : WordTrace (prefixWord ++ tailWord_2627781) baseStart_2627781 baseEnd_2627781 := by
    simpa [prefixWord, tailWord_2627781, baseEnd_2627781] using wordTrace_append hprefix tailTrace_2627781
  have hstable : (prefixWord ++ tailWord_2627781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627781).length < 2 ^ (prefixWord ++ tailWord_2627781).sum := by decide
  have hdescent : baseEnd_2627781 < baseStart_2627781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627791 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_2627791 : Nat := 118140960795 + 2627791 * 2 ^ 59
def prefixEnd_2627791 : Nat := 4983230072969 + 3 ^ 40 * 2627791 * 2
def baseEnd_2627791 : Nat := 1349319842559033489327515

theorem tailTrace_2627791 : CollatzResearch.WordTrace tailWord_2627791 prefixEnd_2627791 1349319842559033489327515 := by
  unfold tailWord_2627791
  simp only [CollatzResearch.WordTrace]
  refine ⟨95843411622969472817835227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63895607748646315211890151 95843411622969472817835227)
  ·
    refine ⟨143765117434454209226752841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95843411622969472817835227 143765117434454209226752841)
    ·
      refine ⟨107823838075840656920064631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143765117434454209226752841 107823838075840656920064631)
      ·
        refine ⟨161735757113760985380096947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107823838075840656920064631 161735757113760985380096947)
        ·
          refine ⟨242603635670641478070145421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161735757113760985380096947 242603635670641478070145421)
          ·
            refine ⟨90976363376490554276304533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242603635670641478070145421 90976363376490554276304533)
            ·
              refine ⟨4264517033272994731701775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90976363376490554276304533 4264517033272994731701775)
              ·
                refine ⟨6396775549909492097552663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264517033272994731701775 6396775549909492097552663)
                ·
                  refine ⟨9595163324864238146328995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6396775549909492097552663 9595163324864238146328995)
                  ·
                    refine ⟨14392744987296357219493493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9595163324864238146328995 14392744987296357219493493)
                    ·
                      refine ⟨1349319842559033489327515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14392744987296357219493493 1349319842559033489327515)
                      ·
                        rfl

theorem cell23_2627791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_2627791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627791 prefixEnd_2627791 := by exact prefixLift 2627791
  have htrace : WordTrace (prefixWord ++ tailWord_2627791) baseStart_2627791 baseEnd_2627791 := by
    simpa [prefixWord, tailWord_2627791, baseEnd_2627791] using wordTrace_append hprefix tailTrace_2627791
  have hstable : (prefixWord ++ tailWord_2627791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627791).length < 2 ^ (prefixWord ++ tailWord_2627791).sum := by decide
  have hdescent : baseEnd_2627791 < baseStart_2627791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627815 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2627815 : Nat := 118140960795 + 2627815 * 2 ^ 59
def prefixEnd_2627815 : Nat := 4983230072969 + 3 ^ 40 * 2627815 * 2
def baseEnd_2627815 : Nat := 449777388698247131809135

theorem tailTrace_2627815 : CollatzResearch.WordTrace tailWord_2627815 prefixEnd_2627815 449777388698247131809135 := by
  unfold tailWord_2627815
  simp only [CollatzResearch.WordTrace]
  refine ⟨95844286974882524916708899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63896191316588349944472599 95844286974882524916708899)
  ·
    refine ⟨143766430462323787375063349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95844286974882524916708899 143766430462323787375063349)
    ·
      refine ⟨13478102855842855066412189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143766430462323787375063349 13478102855842855066412189)
      ·
        refine ⟨5054288570941070649904571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13478102855842855066412189 5054288570941070649904571)
        ·
          refine ⟨7581432856411605974856857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054288570941070649904571 7581432856411605974856857)
          ·
            refine ⟨5686074642308704481142643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7581432856411605974856857 5686074642308704481142643)
            ·
              refine ⟨8529111963463056721713965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686074642308704481142643 8529111963463056721713965)
              ·
                refine ⟨3198416986298646270642737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8529111963463056721713965 3198416986298646270642737)
                ·
                  refine ⟨2398812739723984702982053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3198416986298646270642737 2398812739723984702982053)
                  ·
                    refine ⟨449777388698247131809135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398812739723984702982053 449777388698247131809135)
                    ·
                      rfl

theorem cell23_2627815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2627815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627815 prefixEnd_2627815 := by exact prefixLift 2627815
  have htrace : WordTrace (prefixWord ++ tailWord_2627815) baseStart_2627815 baseEnd_2627815 := by
    simpa [prefixWord, tailWord_2627815, baseEnd_2627815] using wordTrace_append hprefix tailTrace_2627815
  have hstable : (prefixWord ++ tailWord_2627815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627815).length < 2 ^ (prefixWord ++ tailWord_2627815).sum := by decide
  have hdescent : baseEnd_2627815 < baseStart_2627815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627861 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2627861 : Nat := 118140960795 + 2627861 * 2 ^ 59
def prefixEnd_2627861 : Nat := 4983230072969 + 3 ^ 40 * 2627861 * 2
def baseEnd_2627861 : Nat := 1349355786204848215452193

theorem tailTrace_2627861 : CollatzResearch.WordTrace tailWord_2627861 prefixEnd_2627861 1349355786204848215452193 := by
  unfold tailWord_2627861
  simp only [CollatzResearch.WordTrace]
  refine ⟨95845964732715874772883437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63897309821810583181922291 95845964732715874772883437)
  ·
    refine ⟨35942236774768453039831289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95845964732715874772883437 35942236774768453039831289)
    ·
      refine ⟨26956677581076339779873467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35942236774768453039831289 26956677581076339779873467)
      ·
        refine ⟨40435016371614509669810201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26956677581076339779873467 40435016371614509669810201)
        ·
          refine ⟨30326262278710882252357651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40435016371614509669810201 30326262278710882252357651)
          ·
            refine ⟨45489393418066323378536477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30326262278710882252357651 45489393418066323378536477)
            ·
              refine ⟨17058522531774871266951179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45489393418066323378536477 17058522531774871266951179)
              ·
                refine ⟨25587783797662306900426769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17058522531774871266951179 25587783797662306900426769)
                ·
                  refine ⟨19190837848246730175320077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25587783797662306900426769 19190837848246730175320077)
                  ·
                    refine ⟨7196564193092523815745029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19190837848246730175320077 7196564193092523815745029)
                    ·
                      refine ⟨1349355786204848215452193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7196564193092523815745029 1349355786204848215452193)
                      ·
                        rfl

theorem cell23_2627861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2627861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627861 prefixEnd_2627861 := by exact prefixLift 2627861
  have htrace : WordTrace (prefixWord ++ tailWord_2627861) baseStart_2627861 baseEnd_2627861 := by
    simpa [prefixWord, tailWord_2627861, baseEnd_2627861] using wordTrace_append hprefix tailTrace_2627861
  have hstable : (prefixWord ++ tailWord_2627861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627861).length < 2 ^ (prefixWord ++ tailWord_2627861).sum := by decide
  have hdescent : baseEnd_2627861 < baseStart_2627861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627871 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 8]
def baseStart_2627871 : Nat := 118140960795 + 2627871 * 2 ^ 59
def prefixEnd_2627871 : Nat := 4983230072969 + 3 ^ 40 * 2627871 * 2
def baseEnd_2627871 : Nat := 449786973670464392109049

theorem tailTrace_2627871 : CollatzResearch.WordTrace tailWord_2627871 prefixEnd_2627871 449786973670464392109049 := by
  unfold tailWord_2627871
  simp only [CollatzResearch.WordTrace]
  refine ⟨95846329462679646480747467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63897552975119764320498311 95846329462679646480747467)
  ·
    refine ⟨143769494194019469721121201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95846329462679646480747467 143769494194019469721121201)
    ·
      refine ⟨107827120645514602290840901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143769494194019469721121201 107827120645514602290840901)
      ·
        refine ⟨20217585121033987929532669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107827120645514602290840901 20217585121033987929532669)
        ·
          refine ⟨7581594420387745473574751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20217585121033987929532669 7581594420387745473574751)
          ·
            refine ⟨11372391630581618210362127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581594420387745473574751 11372391630581618210362127)
            ·
              refine ⟨17058587445872427315543191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11372391630581618210362127 17058587445872427315543191)
              ·
                refine ⟨25587881168808640973314787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17058587445872427315543191 25587881168808640973314787)
                ·
                  refine ⟨38381821753212961459972181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25587881168808640973314787 38381821753212961459972181)
                  ·
                    refine ⟨449786973670464392109049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38381821753212961459972181 449786973670464392109049)
                    ·
                      rfl

theorem cell23_2627871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_2627871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627871 prefixEnd_2627871 := by exact prefixLift 2627871
  have htrace : WordTrace (prefixWord ++ tailWord_2627871) baseStart_2627871 baseEnd_2627871 := by
    simpa [prefixWord, tailWord_2627871, baseEnd_2627871] using wordTrace_append hprefix tailTrace_2627871
  have hstable : (prefixWord ++ tailWord_2627871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627871).length < 2 ^ (prefixWord ++ tailWord_2627871).sum := by decide
  have hdescent : baseEnd_2627871 < baseStart_2627871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627891 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_2627891 : Nat := 118140960795 + 2627891 * 2 ^ 59
def prefixEnd_2627891 : Nat := 4983230072969 + 3 ^ 40 * 2627891 * 2
def baseEnd_2627891 : Nat := 1349371190624483098077055

theorem tailTrace_2627891 : CollatzResearch.WordTrace tailWord_2627891 prefixEnd_2627891 1349371190624483098077055 := by
  unfold tailWord_2627891
  simp only [CollatzResearch.WordTrace]
  refine ⟨95847058922607189896475527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63898039281738126597650351 95847058922607189896475527)
  ·
    refine ⟨143770588383910784844713291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95847058922607189896475527 143770588383910784844713291)
    ·
      refine ⟨215655882575866177267069937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143770588383910784844713291 215655882575866177267069937)
      ·
        refine ⟨161741911931899632950302453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215655882575866177267069937 161741911931899632950302453)
        ·
          refine ⟨15163304243615590589090855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161741911931899632950302453 15163304243615590589090855)
          ·
            refine ⟨22744956365423385883636283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15163304243615590589090855 22744956365423385883636283)
            ·
              refine ⟨34117434548135078825454425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22744956365423385883636283 34117434548135078825454425)
              ·
                refine ⟨25588075911101309119090819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34117434548135078825454425 25588075911101309119090819)
                ·
                  refine ⟨38382113866651963678636229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25588075911101309119090819 38382113866651963678636229)
                  ·
                    refine ⟨7196646349997243189744293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38382113866651963678636229 7196646349997243189744293)
                    ·
                      refine ⟨1349371190624483098077055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7196646349997243189744293 1349371190624483098077055)
                      ·
                        rfl

theorem cell23_2627891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_2627891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627891 prefixEnd_2627891 := by exact prefixLift 2627891
  have htrace : WordTrace (prefixWord ++ tailWord_2627891) baseStart_2627891 baseEnd_2627891 := by
    simpa [prefixWord, tailWord_2627891, baseEnd_2627891] using wordTrace_append hprefix tailTrace_2627891
  have hstable : (prefixWord ++ tailWord_2627891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627891).length < 2 ^ (prefixWord ++ tailWord_2627891).sum := by decide
  have hdescent : baseEnd_2627891 < baseStart_2627891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2627912 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_2627912 : Nat := 118140960795 + 2627912 * 2 ^ 59
def prefixEnd_2627912 : Nat := 4983230072969 + 3 ^ 40 * 2627912 * 2
def baseEnd_2627912 : Nat := 1349381973718227515914459

theorem tailTrace_2627912 : CollatzResearch.WordTrace tailWord_2627912 prefixEnd_2627912 1349381973718227515914459 := by
  unfold tailWord_2627912
  simp only [CollatzResearch.WordTrace]
  refine ⟨47923912427765555241494995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63898549903687406988659993 47923912427765555241494995)
  ·
    refine ⟨71885868641648332862242493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47923912427765555241494995 71885868641648332862242493)
    ·
      refine ⟨26957200740618124823340935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71885868641648332862242493 26957200740618124823340935)
      ·
        refine ⟨40435801110927187235011403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26957200740618124823340935 40435801110927187235011403)
        ·
          refine ⟨60653701666390780852517105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40435801110927187235011403 60653701666390780852517105)
          ·
            refine ⟨45490276249793085639387829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60653701666390780852517105 45490276249793085639387829)
            ·
              refine ⟨4264713398418101778692609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45490276249793085639387829 4264713398418101778692609)
              ·
                refine ⟨3198535048813576334019457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264713398418101778692609 3198535048813576334019457)
                ·
                  refine ⟨2398901286610182250514593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3198535048813576334019457 2398901286610182250514593)
                  ·
                    refine ⟨1799175964957636687885945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398901286610182250514593 1799175964957636687885945)
                    ·
                      refine ⟨1349381973718227515914459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799175964957636687885945 1349381973718227515914459)
                      ·
                        rfl

theorem cell23_2627912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_2627912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2627912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2627912 prefixEnd_2627912 := by exact prefixLift 2627912
  have htrace : WordTrace (prefixWord ++ tailWord_2627912) baseStart_2627912 baseEnd_2627912 := by
    simpa [prefixWord, tailWord_2627912, baseEnd_2627912] using wordTrace_append hprefix tailTrace_2627912
  have hstable : (prefixWord ++ tailWord_2627912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2627912).length < 2 ^ (prefixWord ++ tailWord_2627912).sum := by decide
  have hdescent : baseEnd_2627912 < baseStart_2627912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2627912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628005 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_2628005 : Nat := 118140960795 + 2628005 * 2 ^ 59
def prefixEnd_2628005 : Nat := 4983230072969 + 3 ^ 40 * 2628005 * 2
def baseEnd_2628005 : Nat := 1349429727419095652051531

theorem tailTrace_2628005 : CollatzResearch.WordTrace tailWord_2628005 prefixEnd_2628005 1349429727419095652051531 := by
  unfold tailWord_2628005
  simp only [CollatzResearch.WordTrace]
  refine ⟨95851216844194187366125469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63900811229462791577416979 95851216844194187366125469)
  ·
    refine ⟨35944206316572820262297051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95851216844194187366125469 35944206316572820262297051)
    ·
      refine ⟨53916309474859230393445577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35944206316572820262297051 53916309474859230393445577)
      ·
        refine ⟨40437232106144422795084183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53916309474859230393445577 40437232106144422795084183)
        ·
          refine ⟨60655848159216634192626275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40437232106144422795084183 60655848159216634192626275)
          ·
            refine ⟨90983772238824951288939413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60655848159216634192626275 90983772238824951288939413)
            ·
              refine ⟨4264864323694919591669035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90983772238824951288939413 4264864323694919591669035)
              ·
                refine ⟨6397296485542379387503553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4264864323694919591669035 6397296485542379387503553)
                ·
                  refine ⟨4797972364156784540627665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6397296485542379387503553 4797972364156784540627665)
                  ·
                    refine ⟨3598479273117588405470749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4797972364156784540627665 3598479273117588405470749)
                    ·
                      refine ⟨1349429727419095652051531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3598479273117588405470749 1349429727419095652051531)
                      ·
                        rfl

theorem cell23_2628005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_2628005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628005 prefixEnd_2628005 := by exact prefixLift 2628005
  have htrace : WordTrace (prefixWord ++ tailWord_2628005) baseStart_2628005 baseEnd_2628005 := by
    simpa [prefixWord, tailWord_2628005, baseEnd_2628005] using wordTrace_append hprefix tailTrace_2628005
  have hstable : (prefixWord ++ tailWord_2628005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628005).length < 2 ^ (prefixWord ++ tailWord_2628005).sum := by decide
  have hdescent : baseEnd_2628005 < baseStart_2628005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628025 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 6]
def baseStart_2628025 : Nat := 118140960795 + 2628025 * 2 ^ 59
def prefixEnd_2628025 : Nat := 4983230072969 + 3 ^ 40 * 2628025 * 2
def baseEnd_2628025 : Nat := 149937777448020619311271

theorem tailTrace_2628025 : CollatzResearch.WordTrace tailWord_2628025 prefixEnd_2628025 149937777448020619311271 := by
  unfold tailWord_2628025
  simp only [CollatzResearch.WordTrace]
  refine ⟨95851946304121730781853529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63901297536081153854569019 95851946304121730781853529)
  ·
    refine ⟨71888959728091298086390147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95851946304121730781853529 71888959728091298086390147)
    ·
      refine ⟨107833439592136947129585221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71888959728091298086390147 107833439592136947129585221)
      ·
        refine ⟨20218769923525677586797229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107833439592136947129585221 20218769923525677586797229)
        ·
          refine ⟨7582038721322129095048961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20218769923525677586797229 7582038721322129095048961)
          ·
            refine ⟨5686529040991596821286721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7582038721322129095048961 5686529040991596821286721)
            ·
              refine ⟨4264896780743697615965041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686529040991596821286721 4264896780743697615965041)
              ·
                refine ⟨3198672585557773211973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264896780743697615965041 3198672585557773211973781)
                ·
                  refine ⟨149937777448020619311271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3198672585557773211973781 149937777448020619311271)
                  ·
                    rfl

theorem cell23_2628025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_2628025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628025 prefixEnd_2628025 := by exact prefixLift 2628025
  have htrace : WordTrace (prefixWord ++ tailWord_2628025) baseStart_2628025 baseEnd_2628025 := by
    simpa [prefixWord, tailWord_2628025, baseEnd_2628025] using wordTrace_append hprefix tailTrace_2628025
  have hstable : (prefixWord ++ tailWord_2628025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628025).length < 2 ^ (prefixWord ++ tailWord_2628025).sum := by decide
  have hdescent : baseEnd_2628025 < baseStart_2628025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628029 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2628029 : Nat := 118140960795 + 2628029 * 2 ^ 59
def prefixEnd_2628029 : Nat := 4983230072969 + 3 ^ 40 * 2628029 * 2
def baseEnd_2628029 : Nat := 449814016984934519383807

theorem tailTrace_2628029 : CollatzResearch.WordTrace tailWord_2628029 prefixEnd_2628029 449814016984934519383807 := by
  unfold tailWord_2628029
  simp only [CollatzResearch.WordTrace]
  refine ⟨95852092196107239464999141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63901394797404826309999427 95852092196107239464999141)
  ·
    refine ⟨17972267286770107399687339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95852092196107239464999141 17972267286770107399687339)
    ·
      refine ⟨26958400930155161099531009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17972267286770107399687339 26958400930155161099531009)
      ·
        refine ⟨20218800697616370824648257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26958400930155161099531009 20218800697616370824648257)
        ·
          refine ⟨15164100523212278118486193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20218800697616370824648257 15164100523212278118486193)
          ·
            refine ⟨11373075392409208588864645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15164100523212278118486193 11373075392409208588864645)
            ·
              refine ⟨2132451636076726610412121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11373075392409208588864645 2132451636076726610412121)
              ·
                refine ⟨1599338727057544957809091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132451636076726610412121 1599338727057544957809091)
                ·
                  refine ⟨2399008090586317436713637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599338727057544957809091 2399008090586317436713637)
                  ·
                    refine ⟨449814016984934519383807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399008090586317436713637 449814016984934519383807)
                    ·
                      rfl

theorem cell23_2628029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2628029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628029 prefixEnd_2628029 := by exact prefixLift 2628029
  have htrace : WordTrace (prefixWord ++ tailWord_2628029) baseStart_2628029 baseEnd_2628029 := by
    simpa [prefixWord, tailWord_2628029, baseEnd_2628029] using wordTrace_append hprefix tailTrace_2628029
  have hstable : (prefixWord ++ tailWord_2628029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628029).length < 2 ^ (prefixWord ++ tailWord_2628029).sum := by decide
  have hdescent : baseEnd_2628029 < baseStart_2628029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628035 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 3]
def baseStart_2628035 : Nat := 118140960795 + 2628035 * 2 ^ 59
def prefixEnd_2628035 : Nat := 4983230072969 + 3 ^ 40 * 2628035 * 2
def baseEnd_2628035 : Nat := 1349445131838730534676393

theorem tailTrace_2628035 : CollatzResearch.WordTrace tailWord_2628035 prefixEnd_2628035 1349445131838730534676393 := by
  unfold tailWord_2628035
  simp only [CollatzResearch.WordTrace]
  refine ⟨95852311034085502489717559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63901540689390334993145039 95852311034085502489717559)
  ·
    refine ⟨143778466551128253734576339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95852311034085502489717559 143778466551128253734576339)
    ·
      refine ⟨215667699826692380601864509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143778466551128253734576339 215667699826692380601864509)
      ·
        refine ⟨80875387435009642725699191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215667699826692380601864509 80875387435009642725699191)
        ·
          refine ⟨121313081152514464088548787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80875387435009642725699191 121313081152514464088548787)
          ·
            refine ⟨181969621728771696132823181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121313081152514464088548787 181969621728771696132823181)
            ·
              refine ⟨68238608148289386049808693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181969621728771696132823181 68238608148289386049808693)
              ·
                refine ⟨6397369513902129942169565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68238608148289386049808693 6397369513902129942169565)
                ·
                  refine ⟨2399013567713298728313587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6397369513902129942169565 2399013567713298728313587)
                  ·
                    refine ⟨3598520351569948092470381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2399013567713298728313587 3598520351569948092470381)
                    ·
                      refine ⟨1349445131838730534676393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3598520351569948092470381 1349445131838730534676393)
                      ·
                        rfl

theorem cell23_2628035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_2628035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628035 prefixEnd_2628035 := by exact prefixLift 2628035
  have htrace : WordTrace (prefixWord ++ tailWord_2628035) baseStart_2628035 baseEnd_2628035 := by
    simpa [prefixWord, tailWord_2628035, baseEnd_2628035] using wordTrace_append hprefix tailTrace_2628035
  have hstable : (prefixWord ++ tailWord_2628035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628035).length < 2 ^ (prefixWord ++ tailWord_2628035).sum := by decide
  have hdescent : baseEnd_2628035 < baseStart_2628035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628052 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2628052 : Nat := 118140960795 + 2628052 * 2 ^ 59
def prefixEnd_2628052 : Nat := 4983230072969 + 3 ^ 40 * 2628052 * 2
def baseEnd_2628052 : Nat := 1349453861009856968163815

theorem tailTrace_2628052 : CollatzResearch.WordTrace tailWord_2628052 prefixEnd_2628052 1349453861009856968163815 := by
  unfold tailWord_2628052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47926465537511957196543205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63901954050015942928724273 47926465537511957196543205)
  ·
    refine ⟨8986212288283491974351851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47926465537511957196543205 8986212288283491974351851)
    ·
      refine ⟨13479318432425237961527777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986212288283491974351851 13479318432425237961527777)
      ·
        refine ⟨10109488824318928471145833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13479318432425237961527777 10109488824318928471145833)
        ·
          refine ⟨7582116618239196353359375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10109488824318928471145833 7582116618239196353359375)
          ·
            refine ⟨11373174927358794530039063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582116618239196353359375 11373174927358794530039063)
            ·
              refine ⟨17059762391038191795058595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11373174927358794530039063 17059762391038191795058595)
              ·
                refine ⟨25589643586557287692587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17059762391038191795058595 25589643586557287692587893)
                ·
                  refine ⟨2399029086239745721180115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25589643586557287692587893 2399029086239745721180115)
                  ·
                    refine ⟨3598543629359618581770173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2399029086239745721180115 3598543629359618581770173)
                    ·
                      refine ⟨1349453861009856968163815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3598543629359618581770173 1349453861009856968163815)
                      ·
                        rfl

theorem cell23_2628052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2628052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628052 prefixEnd_2628052 := by exact prefixLift 2628052
  have htrace : WordTrace (prefixWord ++ tailWord_2628052) baseStart_2628052 baseEnd_2628052 := by
    simpa [prefixWord, tailWord_2628052, baseEnd_2628052] using wordTrace_append hprefix tailTrace_2628052
  have hstable : (prefixWord ++ tailWord_2628052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628052).length < 2 ^ (prefixWord ++ tailWord_2628052).sum := by decide
  have hdescent : baseEnd_2628052 < baseStart_2628052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628072 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2628072 : Nat := 118140960795 + 2628072 * 2 ^ 59
def prefixEnd_2628072 : Nat := 4983230072969 + 3 ^ 40 * 2628072 * 2
def baseEnd_2628072 : Nat := 449821376874315629971241

theorem tailTrace_2628072 : CollatzResearch.WordTrace tailWord_2628072 prefixEnd_2628072 449821376874315629971241 := by
  unfold tailWord_2628072
  simp only [CollatzResearch.WordTrace]
  refine ⟨47926830267475728904407235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63902440356634305205876313 47926830267475728904407235)
  ·
    refine ⟨71890245401213593356610853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47926830267475728904407235 71890245401213593356610853)
    ·
      refine ⟨13479421012727548754364535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71890245401213593356610853 13479421012727548754364535)
      ·
        refine ⟨20219131519091323131546803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13479421012727548754364535 20219131519091323131546803)
        ·
          refine ⟨30328697278636984697320205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20219131519091323131546803 30328697278636984697320205)
          ·
            refine ⟨11373261479488869261495077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30328697278636984697320205 11373261479488869261495077)
            ·
              refine ⟨2132486527404162986530327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11373261479488869261495077 2132486527404162986530327)
              ·
                refine ⟨3198729791106244479795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132486527404162986530327 3198729791106244479795491)
                ·
                  refine ⟨4798094686659366719693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198729791106244479795491 4798094686659366719693237)
                  ·
                    refine ⟨449821376874315629971241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4798094686659366719693237 449821376874315629971241)
                    ·
                      rfl

theorem cell23_2628072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2628072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628072 prefixEnd_2628072 := by exact prefixLift 2628072
  have htrace : WordTrace (prefixWord ++ tailWord_2628072) baseStart_2628072 baseEnd_2628072 := by
    simpa [prefixWord, tailWord_2628072, baseEnd_2628072] using wordTrace_append hprefix tailTrace_2628072
  have hstable : (prefixWord ++ tailWord_2628072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628072).length < 2 ^ (prefixWord ++ tailWord_2628072).sum := by decide
  have hdescent : baseEnd_2628072 < baseStart_2628072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628075 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 4]
def baseStart_2628075 : Nat := 118140960795 + 2628075 * 2 ^ 59
def prefixEnd_2628075 : Nat := 4983230072969 + 3 ^ 40 * 2628075 * 2
def baseEnd_2628075 : Nat := 1349465671064910378176209

theorem tailTrace_2628075 : CollatzResearch.WordTrace tailWord_2628075 prefixEnd_2628075 1349465671064910378176209 := by
  unfold tailWord_2628075
  simp only [CollatzResearch.WordTrace]
  refine ⟨95853769953940589321173679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63902513302627059547449119 95853769953940589321173679)
  ·
    refine ⟨143780654930910883981760519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95853769953940589321173679 143780654930910883981760519)
    ·
      refine ⟨215670982396366325972640779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143780654930910883981760519 215670982396366325972640779)
      ·
        refine ⟨323506473594549488958961169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215670982396366325972640779 323506473594549488958961169)
        ·
          refine ⟨242629855195912116719220877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323506473594549488958961169 242629855195912116719220877)
          ·
            refine ⟨90986195698467043769707829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242629855195912116719220877 90986195698467043769707829)
            ·
              refine ⟨8529955846731285353410109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90986195698467043769707829 8529955846731285353410109)
              ·
                refine ⟨3198733442524232007528791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8529955846731285353410109 3198733442524232007528791)
                ·
                  refine ⟨4798100163786348011293187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198733442524232007528791 4798100163786348011293187)
                  ·
                    refine ⟨7197150245679522016939781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4798100163786348011293187 7197150245679522016939781)
                    ·
                      refine ⟨1349465671064910378176209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7197150245679522016939781 1349465671064910378176209)
                      ·
                        rfl

theorem cell23_2628075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 4].length) (baseStart_2628075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628075 prefixEnd_2628075 := by exact prefixLift 2628075
  have htrace : WordTrace (prefixWord ++ tailWord_2628075) baseStart_2628075 baseEnd_2628075 := by
    simpa [prefixWord, tailWord_2628075, baseEnd_2628075] using wordTrace_append hprefix tailTrace_2628075
  have hstable : (prefixWord ++ tailWord_2628075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628075).length < 2 ^ (prefixWord ++ tailWord_2628075).sum := by decide
  have hdescent : baseEnd_2628075 < baseStart_2628075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628088 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2628088 : Nat := 118140960795 + 2628088 * 2 ^ 59
def prefixEnd_2628088 : Nat := 4983230072969 + 3 ^ 40 * 2628088 * 2
def baseEnd_2628088 : Nat := 1349472346313418827313649

theorem tailTrace_2628088 : CollatzResearch.WordTrace tailWord_2628088 prefixEnd_2628088 1349472346313418827313649 := by
  unfold tailWord_2628088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47927122051446746270698459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63902829401928995027597945 47927122051446746270698459)
  ·
    refine ⟨71890683077170119406047689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47927122051446746270698459 71890683077170119406047689)
    ·
      refine ⟨53918012307877589554535767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71890683077170119406047689 53918012307877589554535767)
      ·
        refine ⟨80877018461816384331803651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53918012307877589554535767 80877018461816384331803651)
        ·
          refine ⟨121315527692724576497705477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80877018461816384331803651 121315527692724576497705477)
          ·
            refine ⟨22746661442385858093319777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121315527692724576497705477 22746661442385858093319777)
            ·
              refine ⟨17059996081789393569989833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22746661442385858093319777 17059996081789393569989833)
              ·
                refine ⟨12794997061342045177492375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17059996081789393569989833 12794997061342045177492375)
                ·
                  refine ⟨19192495592013067766238563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12794997061342045177492375 19192495592013067766238563)
                  ·
                    refine ⟨28788743388019601649357845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19192495592013067766238563 28788743388019601649357845)
                    ·
                      refine ⟨1349472346313418827313649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28788743388019601649357845 1349472346313418827313649)
                      ·
                        rfl

theorem cell23_2628088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2628088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628088 prefixEnd_2628088 := by exact prefixLift 2628088
  have htrace : WordTrace (prefixWord ++ tailWord_2628088) baseStart_2628088 baseEnd_2628088 := by
    simpa [prefixWord, tailWord_2628088, baseEnd_2628088] using wordTrace_append hprefix tailTrace_2628088
  have hstable : (prefixWord ++ tailWord_2628088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628088).length < 2 ^ (prefixWord ++ tailWord_2628088).sum := by decide
  have hdescent : baseEnd_2628088 < baseStart_2628088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628132 : List Nat := [2, 3, 1, 5, 1, 2, 9]
def baseStart_2628132 : Nat := 118140960795 + 2628132 * 2 ^ 59
def prefixEnd_2628132 : Nat := 4983230072969 + 3 ^ 40 * 2628132 * 2
def baseEnd_2628132 : Nat := 16660431351385390804487

theorem tailTrace_2628132 : CollatzResearch.WordTrace tailWord_2628132 prefixEnd_2628132 16660431351385390804487 := by
  unfold tailWord_2628132
  simp only [CollatzResearch.WordTrace]
  refine ⟨47927924457367044027999325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63903899276489392037332433 47927924457367044027999325)
  ·
    refine ⟨17972971671512641510499747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47927924457367044027999325 17972971671512641510499747)
    ·
      refine ⟨26959457507268962265749621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17972971671512641510499747 26959457507268962265749621)
      ·
        refine ⟨2527449141306465212414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26959457507268962265749621 2527449141306465212414027)
        ·
          refine ⟨3791173711959697818621041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527449141306465212414027 3791173711959697818621041)
          ·
            refine ⟨2843380283969773363965781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791173711959697818621041 2843380283969773363965781)
            ·
              refine ⟨16660431351385390804487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2843380283969773363965781 16660431351385390804487)
              ·
                rfl

theorem cell23_2628132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 9].length) (baseStart_2628132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628132 prefixEnd_2628132 := by exact prefixLift 2628132
  have htrace : WordTrace (prefixWord ++ tailWord_2628132) baseStart_2628132 baseEnd_2628132 := by
    simpa [prefixWord, tailWord_2628132, baseEnd_2628132] using wordTrace_append hprefix tailTrace_2628132
  have hstable : (prefixWord ++ tailWord_2628132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628132).length < 2 ^ (prefixWord ++ tailWord_2628132).sum := by decide
  have hdescent : baseEnd_2628132 < baseStart_2628132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628152 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_2628152 : Nat := 118140960795 + 2628152 * 2 ^ 59
def prefixEnd_2628152 : Nat := 4983230072969 + 3 ^ 40 * 2628152 * 2
def baseEnd_2628152 : Nat := 1349505209075306576913355

theorem tailTrace_2628152 : CollatzResearch.WordTrace tailWord_2628152 prefixEnd_2628152 1349505209075306576913355 := by
  unfold tailWord_2628152
  simp only [CollatzResearch.WordTrace]
  refine ⟨47928289187330815735863355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63904385583107754314484473 47928289187330815735863355)
  ·
    refine ⟨71892433780996223603795033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47928289187330815735863355 71892433780996223603795033)
    ·
      refine ⟨53919325335747167702846275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71892433780996223603795033 53919325335747167702846275)
      ·
        refine ⟨80878988003620751554269413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53919325335747167702846275 80878988003620751554269413)
        ·
          refine ⟨15164810250678890916425515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80878988003620751554269413 15164810250678890916425515)
          ·
            refine ⟨22747215376018336374638273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15164810250678890916425515 22747215376018336374638273)
            ·
              refine ⟨17060411532013752280978705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22747215376018336374638273 17060411532013752280978705)
              ·
                refine ⟨12795308649010314210734029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17060411532013752280978705 12795308649010314210734029)
                ·
                  refine ⟨4798240743378867829025261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12795308649010314210734029 4798240743378867829025261)
                  ·
                    refine ⟨1799340278767075435884473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4798240743378867829025261 1799340278767075435884473)
                    ·
                      refine ⟨1349505209075306576913355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799340278767075435884473 1349505209075306576913355)
                      ·
                        rfl

theorem cell23_2628152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_2628152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628152 prefixEnd_2628152 := by exact prefixLift 2628152
  have htrace : WordTrace (prefixWord ++ tailWord_2628152) baseStart_2628152 baseEnd_2628152 := by
    simpa [prefixWord, tailWord_2628152, baseEnd_2628152] using wordTrace_append hprefix tailTrace_2628152
  have hstable : (prefixWord ++ tailWord_2628152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628152).length < 2 ^ (prefixWord ++ tailWord_2628152).sum := by decide
  have hdescent : baseEnd_2628152 < baseStart_2628152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628194 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2628194 : Nat := 118140960795 + 2628194 * 2 ^ 59
def prefixEnd_2628194 : Nat := 4983230072969 + 3 ^ 40 * 2628194 * 2
def baseEnd_2628194 : Nat := 1349526775262795412588163

theorem tailTrace_2628194 : CollatzResearch.WordTrace tailWord_2628194 prefixEnd_2628194 1349526775262795412588163 := by
  unfold tailWord_2628194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23964527560127368161188909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63905406827006315096503757 23964527560127368161188909)
  ·
    refine ⟨8986697835047763060445841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23964527560127368161188909 8986697835047763060445841)
    ·
      refine ⟨6740023376285822295334381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8986697835047763060445841 6740023376285822295334381)
      ·
        refine ⟨2527508766107183360750393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6740023376285822295334381 2527508766107183360750393)
        ·
          refine ⟨1895631574580387520562795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527508766107183360750393 1895631574580387520562795)
          ·
            refine ⟨2843447361870581280844193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895631574580387520562795 2843447361870581280844193)
            ·
              refine ⟨2132585521402935960633145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843447361870581280844193 2132585521402935960633145)
              ·
                refine ⟨1599439141052201970474859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132585521402935960633145 1599439141052201970474859)
                ·
                  refine ⟨2399158711578302955712289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599439141052201970474859 2399158711578302955712289)
                  ·
                    refine ⟨1799369033683727216784217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2399158711578302955712289 1799369033683727216784217)
                    ·
                      refine ⟨1349526775262795412588163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799369033683727216784217 1349526775262795412588163)
                      ·
                        rfl

theorem cell23_2628194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2628194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628194 prefixEnd_2628194 := by exact prefixLift 2628194
  have htrace : WordTrace (prefixWord ++ tailWord_2628194) baseStart_2628194 baseEnd_2628194 := by
    simpa [prefixWord, tailWord_2628194, baseEnd_2628194] using wordTrace_append hprefix tailTrace_2628194
  have hstable : (prefixWord ++ tailWord_2628194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628194).length < 2 ^ (prefixWord ++ tailWord_2628194).sum := by decide
  have hdescent : baseEnd_2628194 < baseStart_2628194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628195 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2628195 : Nat := 118140960795 + 2628195 * 2 ^ 59
def prefixEnd_2628195 : Nat := 4983230072969 + 3 ^ 40 * 2628195 * 2
def baseEnd_2628195 : Nat := 1349527288743449908675657

theorem tailTrace_2628195 : CollatzResearch.WordTrace tailWord_2628195 prefixEnd_2628195 1349527288743449908675657 := by
  unfold tailWord_2628195
  simp only [CollatzResearch.WordTrace]
  refine ⟨95858146713505849815542039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63905431142337233210361359 95858146713505849815542039)
  ·
    refine ⟨143787220070258774723313059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95858146713505849815542039 143787220070258774723313059)
    ·
      refine ⟨215680830105388162084969589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143787220070258774723313059 215680830105388162084969589)
      ·
        refine ⟨20220077822380140195465899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215680830105388162084969589 20220077822380140195465899)
        ·
          refine ⟨30330116733570210293198849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20220077822380140195465899 30330116733570210293198849)
          ·
            refine ⟨22747587550177657719899137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30330116733570210293198849 22747587550177657719899137)
            ·
              refine ⟨17060690662633243289924353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22747587550177657719899137 17060690662633243289924353)
              ·
                refine ⟨12795517996974932467443265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17060690662633243289924353 12795517996974932467443265)
                ·
                  refine ⟨9596638497731199350582449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12795517996974932467443265 9596638497731199350582449)
                  ·
                    refine ⟨7197478873298399512936837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9596638497731199350582449 7197478873298399512936837)
                    ·
                      refine ⟨1349527288743449908675657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7197478873298399512936837 1349527288743449908675657)
                      ·
                        rfl

theorem cell23_2628195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2628195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628195 prefixEnd_2628195 := by exact prefixLift 2628195
  have htrace : WordTrace (prefixWord ++ tailWord_2628195) baseStart_2628195 baseEnd_2628195 := by
    simpa [prefixWord, tailWord_2628195, baseEnd_2628195] using wordTrace_append hprefix tailTrace_2628195
  have hstable : (prefixWord ++ tailWord_2628195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628195).length < 2 ^ (prefixWord ++ tailWord_2628195).sum := by decide
  have hdescent : baseEnd_2628195 < baseStart_2628195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628215 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_2628215 : Nat := 118140960795 + 2628215 * 2 ^ 59
def prefixEnd_2628215 : Nat := 4983230072969 + 3 ^ 40 * 2628215 * 2
def baseEnd_2628215 : Nat := 1349537558356539830425565

theorem tailTrace_2628215 : CollatzResearch.WordTrace tailWord_2628215 prefixEnd_2628215 1349537558356539830425565 := by
  unfold tailWord_2628215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95858876173433393231270099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63905917448955595487513399 95858876173433393231270099)
  ·
    refine ⟨143788314260150089846905149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95858876173433393231270099 143788314260150089846905149)
    ·
      refine ⟨53920617847556283692589431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143788314260150089846905149 53920617847556283692589431)
      ·
        refine ⟨80880926771334425538884147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53920617847556283692589431 80880926771334425538884147)
        ·
          refine ⟨121321390157001638308326221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80880926771334425538884147 121321390157001638308326221)
          ·
            refine ⟨45495521308875614365622333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121321390157001638308326221 45495521308875614365622333)
            ·
              refine ⟨17060820490828355387108375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45495521308875614365622333 17060820490828355387108375)
              ·
                refine ⟨25591230736242533080662563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17060820490828355387108375 25591230736242533080662563)
                ·
                  refine ⟨38386846104363799620993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25591230736242533080662563 38386846104363799620993845)
                  ·
                    refine ⟨3598766822284106214468173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38386846104363799620993845 3598766822284106214468173)
                    ·
                      refine ⟨1349537558356539830425565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3598766822284106214468173 1349537558356539830425565)
                      ·
                        rfl

theorem cell23_2628215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_2628215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628215 prefixEnd_2628215 := by exact prefixLift 2628215
  have htrace : WordTrace (prefixWord ++ tailWord_2628215) baseStart_2628215 baseEnd_2628215 := by
    simpa [prefixWord, tailWord_2628215, baseEnd_2628215] using wordTrace_append hprefix tailTrace_2628215
  have hstable : (prefixWord ++ tailWord_2628215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628215).length < 2 ^ (prefixWord ++ tailWord_2628215).sum := by decide
  have hdescent : baseEnd_2628215 < baseStart_2628215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628235 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 2, 5]
def baseStart_2628235 : Nat := 118140960795 + 2628235 * 2 ^ 59
def prefixEnd_2628235 : Nat := 4983230072969 + 3 ^ 40 * 2628235 * 2
def baseEnd_2628235 : Nat := 449849275989876584058491

theorem tailTrace_2628235 : CollatzResearch.WordTrace tailWord_2628235 prefixEnd_2628235 449849275989876584058491 := by
  unfold tailWord_2628235
  simp only [CollatzResearch.WordTrace]
  refine ⟨95859605633360936646998159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63906403755573957764665439 95859605633360936646998159)
  ·
    refine ⟨143789408450041404970497239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95859605633360936646998159 143789408450041404970497239)
    ·
      refine ⟨215684112675062107455745859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143789408450041404970497239 215684112675062107455745859)
      ·
        refine ⟨323526169012593161183618789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215684112675062107455745859 323526169012593161183618789)
        ·
          refine ⟨60661156689861217721928523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323526169012593161183618789 60661156689861217721928523)
          ·
            refine ⟨90991735034791826582892785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60661156689861217721928523 90991735034791826582892785)
            ·
              refine ⟨68243801276093869937169589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90991735034791826582892785 68243801276093869937169589)
              ·
                refine ⟨6397856369633800306609649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68243801276093869937169589 6397856369633800306609649)
                ·
                  refine ⟨4798392277225350229957237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6397856369633800306609649 4798392277225350229957237)
                  ·
                    refine ⟨449849275989876584058491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4798392277225350229957237 449849275989876584058491)
                    ·
                      rfl

theorem cell23_2628235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].length) (baseStart_2628235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628235 prefixEnd_2628235 := by exact prefixLift 2628235
  have htrace : WordTrace (prefixWord ++ tailWord_2628235) baseStart_2628235 baseEnd_2628235 := by
    simpa [prefixWord, tailWord_2628235, baseEnd_2628235] using wordTrace_append hprefix tailTrace_2628235
  have hstable : (prefixWord ++ tailWord_2628235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628235).length < 2 ^ (prefixWord ++ tailWord_2628235).sum := by decide
  have hdescent : baseEnd_2628235 < baseStart_2628235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628250 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2628250 : Nat := 118140960795 + 2628250 * 2 ^ 59
def prefixEnd_2628250 : Nat := 4983230072969 + 3 ^ 40 * 2628250 * 2
def baseEnd_2628250 : Nat := 1349555530179447193487905

theorem tailTrace_2628250 : CollatzResearch.WordTrace tailWord_2628250 prefixEnd_2628250 1349555530179447193487905 := by
  unfold tailWord_2628250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965038182076648552198551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63906768485537729472529469 23965038182076648552198551)
  ·
    refine ⟨35947557273114972828297827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965038182076648552198551 35947557273114972828297827)
    ·
      refine ⟨53921335909672459242446741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35947557273114972828297827 53921335909672459242446741)
      ·
        refine ⟨2527562620765896526989691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53921335909672459242446741 2527562620765896526989691)
        ·
          refine ⟨3791343931148844790484537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527562620765896526989691 3791343931148844790484537)
          ·
            refine ⟨2843507948361633592863403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791343931148844790484537 2843507948361633592863403)
            ·
              refine ⟨4265261922542450389295105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843507948361633592863403 4265261922542450389295105)
              ·
                refine ⟨3198946441906837791971329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4265261922542450389295105 3198946441906837791971329)
                ·
                  refine ⟨2399209831430128343978497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3198946441906837791971329 2399209831430128343978497)
                  ·
                    refine ⟨1799407373572596257983873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2399209831430128343978497 1799407373572596257983873)
                    ·
                      refine ⟨1349555530179447193487905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799407373572596257983873 1349555530179447193487905)
                      ·
                        rfl

theorem cell23_2628250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2628250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628250 prefixEnd_2628250 := by exact prefixLift 2628250
  have htrace : WordTrace (prefixWord ++ tailWord_2628250) baseStart_2628250 baseEnd_2628250 := by
    simpa [prefixWord, tailWord_2628250, baseEnd_2628250] using wordTrace_append hprefix tailTrace_2628250
  have hstable : (prefixWord ++ tailWord_2628250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628250).length < 2 ^ (prefixWord ++ tailWord_2628250).sum := by decide
  have hdescent : baseEnd_2628250 < baseStart_2628250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628282 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_2628282 : Nat := 118140960795 + 2628282 * 2 ^ 59
def prefixEnd_2628282 : Nat := 4983230072969 + 3 ^ 40 * 2628282 * 2
def baseEnd_2628282 : Nat := 449857320520130356095919

theorem tailTrace_2628282 : CollatzResearch.WordTrace tailWord_2628282 prefixEnd_2628282 449857320520130356095919 := by
  unfold tailWord_2628282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965329966047665918489775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63907546576127109115972733 23965329966047665918489775)
  ·
    refine ⟨35947994949071498877734663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965329966047665918489775 35947994949071498877734663)
    ·
      refine ⟨53921992423607248316601995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35947994949071498877734663 53921992423607248316601995)
      ·
        refine ⟨80882988635410872474902993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53921992423607248316601995 80882988635410872474902993)
        ·
          refine ⟨60662241476558154356177245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80882988635410872474902993 60662241476558154356177245)
          ·
            refine ⟨22748340553709307883566467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60662241476558154356177245 22748340553709307883566467)
            ·
              refine ⟨34122510830563961825349701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22748340553709307883566467 34122510830563961825349701)
              ·
                refine ⟨6397970780730742842253069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34122510830563961825349701 6397970780730742842253069)
                ·
                  refine ⟨2399239042774028565844901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6397970780730742842253069 2399239042774028565844901)
                  ·
                    refine ⟨449857320520130356095919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399239042774028565844901 449857320520130356095919)
                    ·
                      rfl

theorem cell23_2628282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_2628282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628282 prefixEnd_2628282 := by exact prefixLift 2628282
  have htrace : WordTrace (prefixWord ++ tailWord_2628282) baseStart_2628282 baseEnd_2628282 := by
    simpa [prefixWord, tailWord_2628282, baseEnd_2628282] using wordTrace_append hprefix tailTrace_2628282
  have hstable : (prefixWord ++ tailWord_2628282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628282).length < 2 ^ (prefixWord ++ tailWord_2628282).sum := by decide
  have hdescent : baseEnd_2628282 < baseStart_2628282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628316 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2628316 : Nat := 118140960795 + 2628316 * 2 ^ 59
def prefixEnd_2628316 : Nat := 4983230072969 + 3 ^ 40 * 2628316 * 2
def baseEnd_2628316 : Nat := 449863139967547978420867

theorem tailTrace_2628316 : CollatzResearch.WordTrace tailWord_2628316 prefixEnd_2628316 449863139967547978420867 := by
  unfold tailWord_2628316
  simp only [CollatzResearch.WordTrace]
  refine ⟨47931279973033743740348401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63908373297378324987131201 47931279973033743740348401)
  ·
    refine ⟨35948459979775307805261301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47931279973033743740348401 35948459979775307805261301)
    ·
      refine ⟨3370168123103935106743247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35948459979775307805261301 3370168123103935106743247)
      ·
        refine ⟨5055252184655902660114871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370168123103935106743247 5055252184655902660114871)
        ·
          refine ⟨7582878276983853990172307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055252184655902660114871 7582878276983853990172307)
          ·
            refine ⟨11374317415475780985258461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582878276983853990172307 11374317415475780985258461)
            ·
              refine ⟨4265369030803417869471923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11374317415475780985258461 4265369030803417869471923)
              ·
                refine ⟨6398053546205126804207885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265369030803417869471923 6398053546205126804207885)
                ·
                  refine ⟨2399270079826922551577957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6398053546205126804207885 2399270079826922551577957)
                  ·
                    refine ⟨449863139967547978420867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399270079826922551577957 449863139967547978420867)
                    ·
                      rfl

theorem cell23_2628316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2628316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628316 prefixEnd_2628316 := by exact prefixLift 2628316
  have htrace : WordTrace (prefixWord ++ tailWord_2628316) baseStart_2628316 baseEnd_2628316 := by
    simpa [prefixWord, tailWord_2628316, baseEnd_2628316] using wordTrace_append hprefix tailTrace_2628316
  have hstable : (prefixWord ++ tailWord_2628316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628316).length < 2 ^ (prefixWord ++ tailWord_2628316).sum := by decide
  have hdescent : baseEnd_2628316 < baseStart_2628316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628389 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_2628389 : Nat := 118140960795 + 2628389 * 2 ^ 59
def prefixEnd_2628389 : Nat := 4983230072969 + 3 ^ 40 * 2628389 * 2
def baseEnd_2628389 : Nat := 449875634663474049883255

theorem tailTrace_2628389 : CollatzResearch.WordTrace tailWord_2628389 prefixEnd_2628389 449875634663474049883255 := by
  unfold tailWord_2628389
  simp only [CollatzResearch.WordTrace]
  refine ⟨95865222474803020948104221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63910148316535347298736147 95865222474803020948104221)
  ·
    refine ⟨35949458428051132855539083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95865222474803020948104221 35949458428051132855539083)
    ·
      refine ⟨53924187642076699283308625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35949458428051132855539083 53924187642076699283308625)
      ·
        refine ⟨40443140731557524462481469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53924187642076699283308625 40443140731557524462481469)
        ·
          refine ⟨15166177774334071673430551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40443140731557524462481469 15166177774334071673430551)
          ·
            refine ⟨22749266661501107510145827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15166177774334071673430551 22749266661501107510145827)
            ·
              refine ⟨34123899992251661265218741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22749266661501107510145827 34123899992251661265218741)
              ·
                refine ⟨3199115624273593243614257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34123899992251661265218741 3199115624273593243614257)
                ·
                  refine ⟨2399336718205194932710693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199115624273593243614257 2399336718205194932710693)
                  ·
                    refine ⟨449875634663474049883255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399336718205194932710693 449875634663474049883255)
                    ·
                      rfl

theorem cell23_2628389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_2628389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628389 prefixEnd_2628389 := by exact prefixLift 2628389
  have htrace : WordTrace (prefixWord ++ tailWord_2628389) baseStart_2628389 baseEnd_2628389 := by
    simpa [prefixWord, tailWord_2628389, baseEnd_2628389] using wordTrace_append hprefix tailTrace_2628389
  have hstable : (prefixWord ++ tailWord_2628389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628389).length < 2 ^ (prefixWord ++ tailWord_2628389).sum := by decide
  have hdescent : baseEnd_2628389 < baseStart_2628389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628396 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_2628396 : Nat := 118140960795 + 2628396 * 2 ^ 59
def prefixEnd_2628396 : Nat := 4983230072969 + 3 ^ 40 * 2628396 * 2
def baseEnd_2628396 : Nat := 1349630498355003622262233

theorem tailTrace_2628396 : CollatzResearch.WordTrace tailWord_2628396 prefixEnd_2628396 1349630498355003622262233 := by
  unfold tailWord_2628396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47932738892888830571804521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63910318523851774095739361 47932738892888830571804521)
  ·
    refine ⟨35949554169666622928853391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47932738892888830571804521 35949554169666622928853391)
    ·
      refine ⟨53924331254499934393280087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35949554169666622928853391 53924331254499934393280087)
      ·
        refine ⟨80886496881749901589920131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53924331254499934393280087 80886496881749901589920131)
        ·
          refine ⟨121329745322624852384880197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80886496881749901589920131 121329745322624852384880197)
          ·
            refine ⟨22749327247992159822165037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121329745322624852384880197 22749327247992159822165037)
            ·
              refine ⟨8530997717997059933311889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22749327247992159822165037 8530997717997059933311889)
              ·
                refine ⟨6398248288497794949983917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8530997717997059933311889 6398248288497794949983917)
                ·
                  refine ⟨2399343108186673106243969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6398248288497794949983917 2399343108186673106243969)
                  ·
                    refine ⟨1799507331140004829682977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2399343108186673106243969 1799507331140004829682977)
                    ·
                      refine ⟨1349630498355003622262233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799507331140004829682977 1349630498355003622262233)
                      ·
                        rfl

theorem cell23_2628396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_2628396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628396 prefixEnd_2628396 := by exact prefixLift 2628396
  have htrace : WordTrace (prefixWord ++ tailWord_2628396) baseStart_2628396 baseEnd_2628396 := by
    simpa [prefixWord, tailWord_2628396, baseEnd_2628396] using wordTrace_append hprefix tailTrace_2628396
  have hstable : (prefixWord ++ tailWord_2628396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628396).length < 2 ^ (prefixWord ++ tailWord_2628396).sum := by decide
  have hdescent : baseEnd_2628396 < baseStart_2628396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628503 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_2628503 : Nat := 118140960795 + 2628503 * 2 ^ 59
def prefixEnd_2628503 : Nat := 4983230072969 + 3 ^ 40 * 2628503 * 2
def baseEnd_2628503 : Nat := 1349685440785034703624241

theorem tailTrace_2628503 : CollatzResearch.WordTrace tailWord_2628503 prefixEnd_2628503 1349685440785034703624241 := by
  unfold tailWord_2628503
  simp only [CollatzResearch.WordTrace]
  refine ⟨95869380396390018417754163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63912920264260012278502775 95869380396390018417754163)
  ·
    refine ⟨143804070594585027626631245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95869380396390018417754163 143804070594585027626631245)
    ·
      refine ⟨53926526472969385359986717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143804070594585027626631245 53926526472969385359986717)
      ·
        refine ⟨20222447427363519509995019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53926526472969385359986717 20222447427363519509995019)
        ·
          refine ⟨30333671141045279264992529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222447427363519509995019 30333671141045279264992529)
          ·
            refine ⟨22750253355783959448744397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30333671141045279264992529 22750253355783959448744397)
            ·
              refine ⟨8531345008418984793279149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22750253355783959448744397 8531345008418984793279149)
              ·
                refine ⟨3199254378157119297479681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8531345008418984793279149 3199254378157119297479681)
                ·
                  refine ⟨2399440783617839473109761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199254378157119297479681 2399440783617839473109761)
                  ·
                    refine ⟨1799580587713379604832321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2399440783617839473109761 1799580587713379604832321)
                    ·
                      refine ⟨1349685440785034703624241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799580587713379604832321 1349685440785034703624241)
                      ·
                        rfl

theorem cell23_2628503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_2628503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628503 prefixEnd_2628503 := by exact prefixLift 2628503
  have htrace : WordTrace (prefixWord ++ tailWord_2628503) baseStart_2628503 baseEnd_2628503 := by
    simpa [prefixWord, tailWord_2628503, baseEnd_2628503] using wordTrace_append hprefix tailTrace_2628503
  have hstable : (prefixWord ++ tailWord_2628503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628503).length < 2 ^ (prefixWord ++ tailWord_2628503).sum := by decide
  have hdescent : baseEnd_2628503 < baseStart_2628503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628573 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2628573 : Nat := 118140960795 + 2628573 * 2 ^ 59
def prefixEnd_2628573 : Nat := 4983230072969 + 3 ^ 40 * 2628573 * 2
def baseEnd_2628573 : Nat := 449907128143616476582973

theorem tailTrace_2628573 : CollatzResearch.WordTrace tailWord_2628573 prefixEnd_2628573 449907128143616476582973 := by
  unfold tailWord_2628573
  simp only [CollatzResearch.WordTrace]
  refine ⟨95871933506136420372802373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63914622337424280248534915 95871933506136420372802373)
  ·
    refine ⟨17975987532400578819900445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95871933506136420372802373 17975987532400578819900445)
    ·
      refine ⟨6740995324650217057462667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17975987532400578819900445 6740995324650217057462667)
      ·
        refine ⟨10111492986975325586194001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740995324650217057462667 10111492986975325586194001)
        ·
          refine ⟨7583619740231494189645501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10111492986975325586194001 7583619740231494189645501)
          ·
            refine ⟨2843857402586810321117063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7583619740231494189645501 2843857402586810321117063)
            ·
              refine ⟨4265786103880215481675595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843857402586810321117063 4265786103880215481675595)
              ·
                refine ⟨6398679155820323222513393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265786103880215481675595 6398679155820323222513393)
                ·
                  refine ⟨4799009366865242416885045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6398679155820323222513393 4799009366865242416885045)
                  ·
                    refine ⟨449907128143616476582973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4799009366865242416885045 449907128143616476582973)
                    ·
                      rfl

theorem cell23_2628573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2628573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628573 prefixEnd_2628573 := by exact prefixLift 2628573
  have htrace : WordTrace (prefixWord ++ tailWord_2628573) baseStart_2628573 baseEnd_2628573 := by
    simpa [prefixWord, tailWord_2628573, baseEnd_2628573] using wordTrace_append hprefix tailTrace_2628573
  have hstable : (prefixWord ++ tailWord_2628573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628573).length < 2 ^ (prefixWord ++ tailWord_2628573).sum := by decide
  have hdescent : baseEnd_2628573 < baseStart_2628573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628637 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2628637 : Nat := 118140960795 + 2628637 * 2 ^ 59
def prefixEnd_2628637 : Nat := 4983230072969 + 3 ^ 40 * 2628637 * 2
def baseEnd_2628637 : Nat := 449918082397579059782875

theorem tailTrace_2628637 : CollatzResearch.WordTrace tailWord_2628637 prefixEnd_2628637 449918082397579059782875 := by
  unfold tailWord_2628637
  simp only [CollatzResearch.WordTrace]
  refine ⟨95874267777904559303132165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63916178518603039535421443 95874267777904559303132165)
  ·
    refine ⟨17976425208357104869337281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95874267777904559303132165 17976425208357104869337281)
    ·
      refine ⟨13482318906267828652002961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17976425208357104869337281 13482318906267828652002961)
      ·
        refine ⟨10111739179700871489002221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13482318906267828652002961 10111739179700871489002221)
        ·
          refine ⟨3791902192387826808375833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10111739179700871489002221 3791902192387826808375833)
          ·
            refine ⟨2843926644290870106281875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791902192387826808375833 2843926644290870106281875)
            ·
              refine ⟨4265889966436305159422813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843926644290870106281875 4265889966436305159422813)
              ·
                refine ⟨1599708737413614434783555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4265889966436305159422813 1599708737413614434783555)
                ·
                  refine ⟨2399563106120421652175333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599708737413614434783555 2399563106120421652175333)
                  ·
                    refine ⟨449918082397579059782875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399563106120421652175333 449918082397579059782875)
                    ·
                      rfl

theorem cell23_2628637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2628637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628637 prefixEnd_2628637 := by exact prefixLift 2628637
  have htrace : WordTrace (prefixWord ++ tailWord_2628637) baseStart_2628637 baseEnd_2628637 := by
    simpa [prefixWord, tailWord_2628637, baseEnd_2628637] using wordTrace_append hprefix tailTrace_2628637
  have hstable : (prefixWord ++ tailWord_2628637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628637).length < 2 ^ (prefixWord ++ tailWord_2628637).sum := by decide
  have hdescent : baseEnd_2628637 < baseStart_2628637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628689 : List Nat := [1, 2, 2, 1, 3, 1, 4, 9]
def baseStart_2628689 : Nat := 118140960795 + 2628689 * 2 ^ 59
def prefixEnd_2628689 : Nat := 4983230072969 + 3 ^ 40 * 2628689 * 2
def baseEnd_2628689 : Nat := 49991886969880406514755

theorem tailTrace_2628689 : CollatzResearch.WordTrace tailWord_2628689 prefixEnd_2628689 49991886969880406514755 := by
  unfold tailWord_2628689
  simp only [CollatzResearch.WordTrace]
  refine ⟨95876164373716172184025121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63917442915810781456016747 95876164373716172184025121)
  ·
    refine ⟨71907123280287129138018841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95876164373716172184025121 71907123280287129138018841)
    ·
      refine ⟨53930342460215346853514131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71907123280287129138018841 53930342460215346853514131)
      ·
        refine ⟨80895513690323020280271197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53930342460215346853514131 80895513690323020280271197)
        ·
          refine ⟨30335817633871132605101699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80895513690323020280271197 30335817633871132605101699)
          ·
            refine ⟨45503726450806698907652549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30335817633871132605101699 45503726450806698907652549)
            ·
              refine ⟨8531948709526256045184853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45503726450806698907652549 8531948709526256045184853)
              ·
                refine ⟨49991886969880406514755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8531948709526256045184853 49991886969880406514755)
                ·
                  rfl

theorem cell23_2628689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 9].length) (baseStart_2628689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628689 prefixEnd_2628689 := by exact prefixLift 2628689
  have htrace : WordTrace (prefixWord ++ tailWord_2628689) baseStart_2628689 baseEnd_2628689 := by
    simpa [prefixWord, tailWord_2628689, baseEnd_2628689] using wordTrace_append hprefix tailTrace_2628689
  have hstable : (prefixWord ++ tailWord_2628689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628689).length < 2 ^ (prefixWord ++ tailWord_2628689).sum := by decide
  have hdescent : baseEnd_2628689 < baseStart_2628689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628696 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2628696 : Nat := 118140960795 + 2628696 * 2 ^ 59
def prefixEnd_2628696 : Nat := 4983230072969 + 3 ^ 40 * 2628696 * 2
def baseEnd_2628696 : Nat := 1349784542551352448510853

theorem tailTrace_2628696 : CollatzResearch.WordTrace tailWord_2628696 prefixEnd_2628696 1349784542551352448510853 := by
  unfold tailWord_2628696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938209842345406189764971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63917613123127208253019961 47938209842345406189764971)
  ·
    refine ⟨71907314763518109284647457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47938209842345406189764971 71907314763518109284647457)
    ·
      refine ⟨53930486072638581963485593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71907314763518109284647457 53930486072638581963485593)
      ·
        refine ⟨40447864554478936472614195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53930486072638581963485593 40447864554478936472614195)
        ·
          refine ⟨60671796831718404708921293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40447864554478936472614195 60671796831718404708921293)
          ·
            refine ⟨22751923811894401765845485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60671796831718404708921293 22751923811894401765845485)
            ·
              refine ⟨8531971429460400662192057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22751923811894401765845485 8531971429460400662192057)
              ·
                refine ⟨6398978572095300496644043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8531971429460400662192057 6398978572095300496644043)
                ·
                  refine ⟨9598467858142950744966065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398978572095300496644043 9598467858142950744966065)
                  ·
                    refine ⟨7198850893607213058724549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9598467858142950744966065 7198850893607213058724549)
                    ·
                      refine ⟨1349784542551352448510853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7198850893607213058724549 1349784542551352448510853)
                      ·
                        rfl

theorem cell23_2628696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2628696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628696 prefixEnd_2628696 := by exact prefixLift 2628696
  have htrace : WordTrace (prefixWord ++ tailWord_2628696) baseStart_2628696 baseEnd_2628696 := by
    simpa [prefixWord, tailWord_2628696, baseEnd_2628696] using wordTrace_append hprefix tailTrace_2628696
  have hstable : (prefixWord ++ tailWord_2628696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628696).length < 2 ^ (prefixWord ++ tailWord_2628696).sum := by decide
  have hdescent : baseEnd_2628696 < baseStart_2628696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628700 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2628700 : Nat := 118140960795 + 2628700 * 2 ^ 59
def prefixEnd_2628700 : Nat := 4983230072969 + 3 ^ 40 * 2628700 * 2
def baseEnd_2628700 : Nat := 1349786596473970432860835

theorem tailTrace_2628700 : CollatzResearch.WordTrace tailWord_2628700 prefixEnd_2628700 1349786596473970432860835 := by
  unfold tailWord_2628700
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938282788338160531337777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63917710384450880708450369 47938282788338160531337777)
  ·
    refine ⟨35953712091253620398503333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47938282788338160531337777 35953712091253620398503333)
    ·
      refine ⟨6741321017110053824719375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35953712091253620398503333 6741321017110053824719375)
      ·
        refine ⟨10111981525665080737079063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6741321017110053824719375 10111981525665080737079063)
        ·
          refine ⟨15167972288497621105618595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10111981525665080737079063 15167972288497621105618595)
          ·
            refine ⟨22751958432746431658427893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15167972288497621105618595 22751958432746431658427893)
            ·
              refine ⟨2132996103069977967977615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22751958432746431658427893 2132996103069977967977615)
              ·
                refine ⟨3199494154604966951966423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132996103069977967977615 3199494154604966951966423)
                ·
                  refine ⟨4799241231907450427949635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199494154604966951966423 4799241231907450427949635)
                  ·
                    refine ⟨7198861847861175641924453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799241231907450427949635 7198861847861175641924453)
                    ·
                      refine ⟨1349786596473970432860835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7198861847861175641924453 1349786596473970432860835)
                      ·
                        rfl

theorem cell23_2628700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2628700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628700 prefixEnd_2628700 := by exact prefixLift 2628700
  have htrace : WordTrace (prefixWord ++ tailWord_2628700) baseStart_2628700 baseEnd_2628700 := by
    simpa [prefixWord, tailWord_2628700, baseEnd_2628700] using wordTrace_append hprefix tailTrace_2628700
  have hstable : (prefixWord ++ tailWord_2628700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628700).length < 2 ^ (prefixWord ++ tailWord_2628700).sum := by decide
  have hdescent : baseEnd_2628700 < baseStart_2628700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628706 : List Nat := [3, 3, 2, 2, 1, 12]
def baseStart_2628706 : Nat := 118140960795 + 2628706 * 2 ^ 59
def prefixEnd_2628706 : Nat := 4983230072969 + 3 ^ 40 * 2628706 * 2
def baseEnd_2628706 : Nat := 5554690030279413207349

theorem tailTrace_2628706 : CollatzResearch.WordTrace tailWord_2628706 prefixEnd_2628706 5554690030279413207349 := by
  unfold tailWord_2628706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969196103663646021848493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63917856276436389391595981 23969196103663646021848493)
  ·
    refine ⟨8988448538873867258193185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23969196103663646021848493 8988448538873867258193185)
    ·
      refine ⟨6741336404155400443644889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8988448538873867258193185 6741336404155400443644889)
      ·
        refine ⟨5056002303116550332733667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6741336404155400443644889 5056002303116550332733667)
        ·
          refine ⟨7584003454674825499100501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056002303116550332733667 7584003454674825499100501)
          ·
            refine ⟨5554690030279413207349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7584003454674825499100501 5554690030279413207349)
            ·
              rfl

theorem cell23_2628706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 12].length) (baseStart_2628706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628706 prefixEnd_2628706 := by exact prefixLift 2628706
  have htrace : WordTrace (prefixWord ++ tailWord_2628706) baseStart_2628706 baseEnd_2628706 := by
    simpa [prefixWord, tailWord_2628706, baseEnd_2628706] using wordTrace_append hprefix tailTrace_2628706
  have hstable : (prefixWord ++ tailWord_2628706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628706).length < 2 ^ (prefixWord ++ tailWord_2628706).sum := by decide
  have hdescent : baseEnd_2628706 < baseStart_2628706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628716 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2628716 : Nat := 118140960795 + 2628716 * 2 ^ 59
def prefixEnd_2628716 : Nat := 4983230072969 + 3 ^ 40 * 2628716 * 2
def baseEnd_2628716 : Nat := 1349794812164442370260761

theorem tailTrace_2628716 : CollatzResearch.WordTrace tailWord_2628716 prefixEnd_2628716 1349794812164442370260761 := by
  unfold tailWord_2628716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938574572309177897629001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63918099429745570530172001 47938574572309177897629001)
  ·
    refine ⟨35953930929231883423221751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47938574572309177897629001 35953930929231883423221751)
    ·
      refine ⟨53930896393847825134832627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35953930929231883423221751 53930896393847825134832627)
      ·
        refine ⟨80896344590771737702248941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53930896393847825134832627 80896344590771737702248941)
        ·
          refine ⟨30336129221539401638343353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80896344590771737702248941 30336129221539401638343353)
          ·
            refine ⟨22752096916154551228757515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30336129221539401638343353 22752096916154551228757515)
            ·
              refine ⟨34128145374231826843136273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752096916154551228757515 34128145374231826843136273)
              ·
                refine ⟨25596109030673870132352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34128145374231826843136273 25596109030673870132352205)
                ·
                  refine ⟨9598540886502701299632077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25596109030673870132352205 9598540886502701299632077)
                  ·
                    refine ⟨3599452832438512987362029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9598540886502701299632077 3599452832438512987362029)
                    ·
                      refine ⟨1349794812164442370260761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3599452832438512987362029 1349794812164442370260761)
                      ·
                        rfl

theorem cell23_2628716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2628716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628716 prefixEnd_2628716 := by exact prefixLift 2628716
  have htrace : WordTrace (prefixWord ++ tailWord_2628716) baseStart_2628716 baseEnd_2628716 := by
    simpa [prefixWord, tailWord_2628716, baseEnd_2628716] using wordTrace_append hprefix tailTrace_2628716
  have hstable : (prefixWord ++ tailWord_2628716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628716).length < 2 ^ (prefixWord ++ tailWord_2628716).sum := by decide
  have hdescent : baseEnd_2628716 < baseStart_2628716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628719 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 9]
def baseStart_2628719 : Nat := 118140960795 + 2628719 * 2 ^ 59
def prefixEnd_2628719 : Nat := 4983230072969 + 3 ^ 40 * 2628719 * 2
def baseEnd_2628719 : Nat := 449932117535468619507749

theorem tailTrace_2628719 : CollatzResearch.WordTrace tailWord_2628719 prefixEnd_2628719 449932117535468619507749 := by
  unfold tailWord_2628719
  simp only [CollatzResearch.WordTrace]
  refine ⟨95877258563607487307617211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63918172375738324871744807 95877258563607487307617211)
  ·
    refine ⟨143815887845411230961425817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95877258563607487307617211 143815887845411230961425817)
    ·
      refine ⟨107861915884058423221069363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143815887845411230961425817 107861915884058423221069363)
      ·
        refine ⟨161792873826087634831604045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107861915884058423221069363 161792873826087634831604045)
        ·
          refine ⟨60672327684782863061851517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161792873826087634831604045 60672327684782863061851517)
          ·
            refine ⟨22752122881793573648194319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60672327684782863061851517 22752122881793573648194319)
            ·
              refine ⟨34128184322690360472291479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752122881793573648194319 34128184322690360472291479)
              ·
                refine ⟨51192276484035540708437219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34128184322690360472291479 51192276484035540708437219)
                ·
                  refine ⟨76788414726053311062655829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51192276484035540708437219 76788414726053311062655829)
                  ·
                    refine ⟨449932117535468619507749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76788414726053311062655829 449932117535468619507749)
                    ·
                      rfl

theorem cell23_2628719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_2628719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628719 prefixEnd_2628719 := by exact prefixLift 2628719
  have htrace : WordTrace (prefixWord ++ tailWord_2628719) baseStart_2628719 baseEnd_2628719 := by
    simpa [prefixWord, tailWord_2628719, baseEnd_2628719] using wordTrace_append hprefix tailTrace_2628719
  have hstable : (prefixWord ++ tailWord_2628719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628719).length < 2 ^ (prefixWord ++ tailWord_2628719).sum := by decide
  have hdescent : baseEnd_2628719 < baseStart_2628719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628733 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_2628733 : Nat := 118140960795 + 2628733 * 2 ^ 59
def prefixEnd_2628733 : Nat := 4983230072969 + 3 ^ 40 * 2628733 * 2
def baseEnd_2628733 : Nat := 1349803541335568803748183

theorem tailTrace_2628733 : CollatzResearch.WordTrace tailWord_2628733 prefixEnd_2628733 1349803541335568803748183 := by
  unfold tailWord_2628733
  simp only [CollatzResearch.WordTrace]
  refine ⟨95877769185556767698626853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63918512790371178465751235 95877769185556767698626853)
  ·
    refine ⟨17977081722291893943492535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95877769185556767698626853 17977081722291893943492535)
    ·
      refine ⟨26965622583437840915238803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17977081722291893943492535 26965622583437840915238803)
      ·
        refine ⟨40448433875156761372858205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26965622583437840915238803 40448433875156761372858205)
        ·
          refine ⟨15168162703183785514821827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40448433875156761372858205 15168162703183785514821827)
          ·
            refine ⟨22752244054775678272232741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15168162703183785514821827 22752244054775678272232741)
            ·
              refine ⟨4266045760270439676043639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22752244054775678272232741 4266045760270439676043639)
              ·
                refine ⟨6399068640405659514065459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266045760270439676043639 6399068640405659514065459)
                ·
                  refine ⟨9598602960608489271098189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6399068640405659514065459 9598602960608489271098189)
                  ·
                    refine ⟨3599476110228183476661821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9598602960608489271098189 3599476110228183476661821)
                    ·
                      refine ⟨1349803541335568803748183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3599476110228183476661821 1349803541335568803748183)
                      ·
                        rfl

theorem cell23_2628733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_2628733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628733 prefixEnd_2628733 := by exact prefixLift 2628733
  have htrace : WordTrace (prefixWord ++ tailWord_2628733) baseStart_2628733 baseEnd_2628733 := by
    simpa [prefixWord, tailWord_2628733, baseEnd_2628733] using wordTrace_append hprefix tailTrace_2628733
  have hstable : (prefixWord ++ tailWord_2628733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628733).length < 2 ^ (prefixWord ++ tailWord_2628733).sum := by decide
  have hdescent : baseEnd_2628733 < baseStart_2628733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628746 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2628746 : Nat := 118140960795 + 2628746 * 2 ^ 59
def prefixEnd_2628746 : Nat := 4983230072969 + 3 ^ 40 * 2628746 * 2
def baseEnd_2628746 : Nat := 1349810216584077252885623

theorem tailTrace_2628746 : CollatzResearch.WordTrace tailWord_2628746 prefixEnd_2628746 1349810216584077252885623 := by
  unfold tailWord_2628746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969560833627417729712523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63918828889673113945900061 23969560833627417729712523)
  ·
    refine ⟨35954341250441126594568785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23969560833627417729712523 35954341250441126594568785)
    ·
      refine ⟨26965755937830844945926589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35954341250441126594568785 26965755937830844945926589)
      ·
        refine ⟨10112158476686566854722471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26965755937830844945926589 10112158476686566854722471)
        ·
          refine ⟨15168237715029850282083707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10112158476686566854722471 15168237715029850282083707)
          ·
            refine ⟨22752356572544775423125561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15168237715029850282083707 22752356572544775423125561)
            ·
              refine ⟨17064267429408581567344171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22752356572544775423125561 17064267429408581567344171)
              ·
                refine ⟨25596401144112872351016257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17064267429408581567344171 25596401144112872351016257)
                ·
                  refine ⟨19197300858084654263262193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25596401144112872351016257 19197300858084654263262193)
                  ·
                    refine ⟨14397975643563490697446645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19197300858084654263262193 14397975643563490697446645)
                    ·
                      refine ⟨1349810216584077252885623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14397975643563490697446645 1349810216584077252885623)
                      ·
                        rfl

theorem cell23_2628746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2628746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628746 prefixEnd_2628746 := by exact prefixLift 2628746
  have htrace : WordTrace (prefixWord ++ tailWord_2628746) baseStart_2628746 baseEnd_2628746 := by
    simpa [prefixWord, tailWord_2628746, baseEnd_2628746] using wordTrace_append hprefix tailTrace_2628746
  have hstable : (prefixWord ++ tailWord_2628746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628746).length < 2 ^ (prefixWord ++ tailWord_2628746).sum := by decide
  have hdescent : baseEnd_2628746 < baseStart_2628746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628836 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2628836 : Nat := 118140960795 + 2628836 * 2 ^ 59
def prefixEnd_2628836 : Nat := 4983230072969 + 3 ^ 40 * 2628836 * 2
def baseEnd_2628836 : Nat := 1349856429842981900760209

theorem tailTrace_2628836 : CollatzResearch.WordTrace tailWord_2628836 prefixEnd_2628836 1349856429842981900760209 := by
  unfold tailWord_2628836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47940762952091808144813181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63921017269455744193084241 47940762952091808144813181)
  ·
    refine ⟨17977786107034428054304943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47940762952091808144813181 17977786107034428054304943)
    ·
      refine ⟨26966679160551642081457415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17977786107034428054304943 26966679160551642081457415)
      ·
        refine ⟨40450018740827463122186123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26966679160551642081457415 40450018740827463122186123)
        ·
          refine ⟨60675028111241194683279185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40450018740827463122186123 60675028111241194683279185)
          ·
            refine ⟨45506271083430896012459389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60675028111241194683279185 45506271083430896012459389)
            ·
              refine ⟨17064851656286586004672271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45506271083430896012459389 17064851656286586004672271)
              ·
                refine ⟨25597277484429879007008407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17064851656286586004672271 25597277484429879007008407)
                ·
                  refine ⟨38395916226644818510512611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25597277484429879007008407 38395916226644818510512611)
                  ·
                    refine ⟨57593874339967227765768917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38395916226644818510512611 57593874339967227765768917)
                    ·
                      refine ⟨1349856429842981900760209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57593874339967227765768917 1349856429842981900760209)
                      ·
                        rfl

theorem cell23_2628836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2628836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628836 prefixEnd_2628836 := by exact prefixLift 2628836
  have htrace : WordTrace (prefixWord ++ tailWord_2628836) baseStart_2628836 baseEnd_2628836 := by
    simpa [prefixWord, tailWord_2628836, baseEnd_2628836] using wordTrace_append hprefix tailTrace_2628836
  have hstable : (prefixWord ++ tailWord_2628836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628836).length < 2 ^ (prefixWord ++ tailWord_2628836).sum := by decide
  have hdescent : baseEnd_2628836 < baseStart_2628836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628860 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_2628860 : Nat := 118140960795 + 2628860 * 2 ^ 59
def prefixEnd_2628860 : Nat := 4983230072969 + 3 ^ 40 * 2628860 * 2
def baseEnd_2628860 : Nat := 449956251126229935620033

theorem tailTrace_2628860 : CollatzResearch.WordTrace tailWord_2628860 prefixEnd_2628860 449956251126229935620033 := by
  unfold tailWord_2628860
  simp only [CollatzResearch.WordTrace]
  refine ⟨47941200628048334194250017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63921600837397778925666689 47941200628048334194250017)
  ·
    refine ⟨35955900471036250645687513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47941200628048334194250017 35955900471036250645687513)
    ·
      refine ⟨26966925353277187984265635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35955900471036250645687513 26966925353277187984265635)
      ·
        refine ⟨40450388029915781976398453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26966925353277187984265635 40450388029915781976398453)
        ·
          refine ⟨3792223877804604560287355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40450388029915781976398453 3792223877804604560287355)
          ·
            refine ⟨5688335816706906840431033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792223877804604560287355 5688335816706906840431033)
            ·
              refine ⟨4266251862530180130323275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5688335816706906840431033 4266251862530180130323275)
              ·
                refine ⟨6399377793795270195484913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266251862530180130323275 6399377793795270195484913)
                ·
                  refine ⟨4799533345346452646613685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399377793795270195484913 4799533345346452646613685)
                  ·
                    refine ⟨449956251126229935620033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4799533345346452646613685 449956251126229935620033)
                    ·
                      rfl

theorem cell23_2628860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_2628860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628860 prefixEnd_2628860 := by exact prefixLift 2628860
  have htrace : WordTrace (prefixWord ++ tailWord_2628860) baseStart_2628860 baseEnd_2628860 := by
    simpa [prefixWord, tailWord_2628860, baseEnd_2628860] using wordTrace_append hprefix tailTrace_2628860
  have hstable : (prefixWord ++ tailWord_2628860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628860).length < 2 ^ (prefixWord ++ tailWord_2628860).sum := by decide
  have hdescent : baseEnd_2628860 < baseStart_2628860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628863 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_2628863 : Nat := 118140960795 + 2628863 * 2 ^ 59
def prefixEnd_2628863 : Nat := 4983230072969 + 3 ^ 40 * 2628863 * 2
def baseEnd_2628863 : Nat := 1349870293820653295122585

theorem tailTrace_2628863 : CollatzResearch.WordTrace tailWord_2628863 prefixEnd_2628863 1349870293820653295122585 := by
  unfold tailWord_2628863
  simp only [CollatzResearch.WordTrace]
  refine ⟨95882510675085799900859243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63921673783390533267239495 95882510675085799900859243)
  ·
    refine ⟨143823766012628699851288865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95882510675085799900859243 143823766012628699851288865)
    ·
      refine ⟨107867824509471524888466649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143823766012628699851288865 107867824509471524888466649)
      ·
        refine ⟨80900868382103643666349987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107867824509471524888466649 80900868382103643666349987)
        ·
          refine ⟨121351302573155465499524981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80900868382103643666349987 121351302573155465499524981)
          ·
            refine ⟨11376684616233324890580467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121351302573155465499524981 11376684616233324890580467)
            ·
              refine ⟨17065026924349987335870701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11376684616233324890580467 17065026924349987335870701)
              ·
                refine ⟨6399385096631245250951513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17065026924349987335870701 6399385096631245250951513)
                ·
                  refine ⟨4799538822473433938213635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399385096631245250951513 4799538822473433938213635)
                  ·
                    refine ⟨7199308233710150907320453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799538822473433938213635 7199308233710150907320453)
                    ·
                      refine ⟨1349870293820653295122585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7199308233710150907320453 1349870293820653295122585)
                      ·
                        rfl

theorem cell23_2628863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_2628863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628863 prefixEnd_2628863 := by exact prefixLift 2628863
  have htrace : WordTrace (prefixWord ++ tailWord_2628863) baseStart_2628863 baseEnd_2628863 := by
    simpa [prefixWord, tailWord_2628863, baseEnd_2628863] using wordTrace_append hprefix tailTrace_2628863
  have hstable : (prefixWord ++ tailWord_2628863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628863).length < 2 ^ (prefixWord ++ tailWord_2628863).sum := by decide
  have hdescent : baseEnd_2628863 < baseStart_2628863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628917 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2628917 : Nat := 118140960795 + 2628917 * 2 ^ 59
def prefixEnd_2628917 : Nat := 4983230072969 + 3 ^ 40 * 2628917 * 2
def baseEnd_2628917 : Nat := 1349898021775996083847337

theorem tailTrace_2628917 : CollatzResearch.WordTrace tailWord_2628917 prefixEnd_2628917 1349898021775996083847337 := by
  unfold tailWord_2628917
  simp only [CollatzResearch.WordTrace]
  refine ⟨95884480216890167123325005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63922986811260111415550003 95884480216890167123325005)
  ·
    refine ⟨35956680081333812671246877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95884480216890167123325005 35956680081333812671246877)
    ·
      refine ⟨13483755030500179751717579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35956680081333812671246877 13483755030500179751717579)
      ·
        refine ⟨20225632545750269627576369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13483755030500179751717579 20225632545750269627576369)
        ·
          refine ⟨15169224409312702220682277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20225632545750269627576369 15169224409312702220682277)
          ·
            refine ⟨2844229576746131666377927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15169224409312702220682277 2844229576746131666377927)
            ·
              refine ⟨4266344365119197499566891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844229576746131666377927 4266344365119197499566891)
              ·
                refine ⟨6399516547678796249350337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266344365119197499566891 6399516547678796249350337)
                ·
                  refine ⟨4799637410759097187012753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399516547678796249350337 4799637410759097187012753)
                  ·
                    refine ⟨3599728058069322890259565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4799637410759097187012753 3599728058069322890259565)
                    ·
                      refine ⟨1349898021775996083847337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3599728058069322890259565 1349898021775996083847337)
                      ·
                        rfl

theorem cell23_2628917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2628917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628917 prefixEnd_2628917 := by exact prefixLift 2628917
  have htrace : WordTrace (prefixWord ++ tailWord_2628917) baseStart_2628917 baseEnd_2628917 := by
    simpa [prefixWord, tailWord_2628917, baseEnd_2628917] using wordTrace_append hprefix tailTrace_2628917
  have hstable : (prefixWord ++ tailWord_2628917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628917).length < 2 ^ (prefixWord ++ tailWord_2628917).sum := by decide
  have hdescent : baseEnd_2628917 < baseStart_2628917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628947 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 1, 1, 3]
def baseStart_2628947 : Nat := 118140960795 + 2628947 * 2 ^ 59
def prefixEnd_2628947 : Nat := 4983230072969 + 3 ^ 40 * 2628947 * 2
def baseEnd_2628947 : Nat := 1349913426195630966472199

theorem tailTrace_2628947 : CollatzResearch.WordTrace tailWord_2628947 prefixEnd_2628947 1349913426195630966472199 := by
  unfold tailWord_2628947
  simp only [CollatzResearch.WordTrace]
  refine ⟨95885574406781482246917095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63923716271187654831278063 95885574406781482246917095)
  ·
    refine ⟨143828361610172223370375643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95885574406781482246917095 143828361610172223370375643)
    ·
      refine ⟨215742542415258335055563465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143828361610172223370375643 215742542415258335055563465)
      ·
        refine ⟨161806906811443751291672599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215742542415258335055563465 161806906811443751291672599)
        ·
          refine ⟨242710360217165626937508899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161806906811443751291672599 242710360217165626937508899)
          ·
            refine ⟨364065540325748440406263349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242710360217165626937508899 364065540325748440406263349)
            ·
              refine ⟨34131144405538916288087189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364065540325748440406263349 34131144405538916288087189)
              ·
                refine ⟨1599897394009636701004087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34131144405538916288087189 1599897394009636701004087)
                ·
                  refine ⟨2399846091014455051506131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599897394009636701004087 2399846091014455051506131)
                  ·
                    refine ⟨3599769136521682577259197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2399846091014455051506131 3599769136521682577259197)
                    ·
                      refine ⟨1349913426195630966472199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3599769136521682577259197 1349913426195630966472199)
                      ·
                        rfl

theorem cell23_2628947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 1, 3].length) (baseStart_2628947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628947 prefixEnd_2628947 := by exact prefixLift 2628947
  have htrace : WordTrace (prefixWord ++ tailWord_2628947) baseStart_2628947 baseEnd_2628947 := by
    simpa [prefixWord, tailWord_2628947, baseEnd_2628947] using wordTrace_append hprefix tailTrace_2628947
  have hstable : (prefixWord ++ tailWord_2628947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628947).length < 2 ^ (prefixWord ++ tailWord_2628947).sum := by decide
  have hdescent : baseEnd_2628947 < baseStart_2628947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628953 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_2628953 : Nat := 118140960795 + 2628953 * 2 ^ 59
def prefixEnd_2628953 : Nat := 4983230072969 + 3 ^ 40 * 2628953 * 2
def baseEnd_2628953 : Nat := 1349916507079557942997171

theorem tailTrace_2628953 : CollatzResearch.WordTrace tailWord_2628953 prefixEnd_2628953 1349916507079557942997171 := by
  unfold tailWord_2628953
  simp only [CollatzResearch.WordTrace]
  refine ⟨95885793244759745271635513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63923862163173163514423675 95885793244759745271635513)
  ·
    refine ⟨71914344933569808953726635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95885793244759745271635513 71914344933569808953726635)
    ·
      refine ⟨107871517400354713430589953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71914344933569808953726635 107871517400354713430589953)
      ·
        refine ⟨80903638050266035072942465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107871517400354713430589953 80903638050266035072942465)
        ·
          refine ⟨60677728537699526304706849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80903638050266035072942465 60677728537699526304706849)
          ·
            refine ⟨45508296403274644728530137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60677728537699526304706849 45508296403274644728530137)
            ·
              refine ⟨34131222302455983546397603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45508296403274644728530137 34131222302455983546397603)
              ·
                refine ⟨51196833453683975319596405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34131222302455983546397603 51196833453683975319596405)
                ·
                  refine ⟨4799703136282872686212163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51196833453683975319596405 4799703136282872686212163)
                  ·
                    refine ⟨7199554704424309029318245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799703136282872686212163 7199554704424309029318245)
                    ·
                      refine ⟨1349916507079557942997171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7199554704424309029318245 1349916507079557942997171)
                      ·
                        rfl

theorem cell23_2628953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_2628953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628953 prefixEnd_2628953 := by exact prefixLift 2628953
  have htrace : WordTrace (prefixWord ++ tailWord_2628953) baseStart_2628953 baseEnd_2628953 := by
    simpa [prefixWord, tailWord_2628953, baseEnd_2628953] using wordTrace_append hprefix tailTrace_2628953
  have hstable : (prefixWord ++ tailWord_2628953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628953).length < 2 ^ (prefixWord ++ tailWord_2628953).sum := by decide
  have hdescent : baseEnd_2628953 < baseStart_2628953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628967 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2628967 : Nat := 118140960795 + 2628967 * 2 ^ 59
def prefixEnd_2628967 : Nat := 4983230072969 + 3 ^ 40 * 2628967 * 2
def baseEnd_2628967 : Nat := 449974565269573629407369

theorem tailTrace_2628967 : CollatzResearch.WordTrace tailWord_2628967 prefixEnd_2628967 449974565269573629407369 := by
  unfold tailWord_2628967
  simp only [CollatzResearch.WordTrace]
  refine ⟨95886303866709025662645155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63924202577806017108430103 95886303866709025662645155)
  ·
    refine ⟨143829455800063538493967733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95886303866709025662645155 143829455800063538493967733)
    ·
      refine ⟨13484011481255956733809475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143829455800063538493967733 13484011481255956733809475)
      ·
        refine ⟨20226017221883935100714213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13484011481255956733809475 20226017221883935100714213)
        ·
          refine ⟨3792378229103237831383915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20226017221883935100714213 3792378229103237831383915)
          ·
            refine ⟨5688567343654856747075873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792378229103237831383915 5688567343654856747075873)
            ·
              refine ⟨4266425507741142560306905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5688567343654856747075873 4266425507741142560306905)
              ·
                refine ⟨3199819130805856920230179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266425507741142560306905 3199819130805856920230179)
                ·
                  refine ⟨4799728696208785380345269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199819130805856920230179 4799728696208785380345269)
                  ·
                    refine ⟨449974565269573629407369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4799728696208785380345269 449974565269573629407369)
                    ·
                      rfl

theorem cell23_2628967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2628967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628967 prefixEnd_2628967 := by exact prefixLift 2628967
  have htrace : WordTrace (prefixWord ++ tailWord_2628967) baseStart_2628967 baseEnd_2628967 := by
    simpa [prefixWord, tailWord_2628967, baseEnd_2628967] using wordTrace_append hprefix tailTrace_2628967
  have hstable : (prefixWord ++ tailWord_2628967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628967).length < 2 ^ (prefixWord ++ tailWord_2628967).sum := by decide
  have hdescent : baseEnd_2628967 < baseStart_2628967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2628983 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2628983 : Nat := 118140960795 + 2628983 * 2 ^ 59
def prefixEnd_2628983 : Nat := 4983230072969 + 3 ^ 40 * 2628983 * 2
def baseEnd_2628983 : Nat := 1349931911499192825622033

theorem tailTrace_2628983 : CollatzResearch.WordTrace tailWord_2628983 prefixEnd_2628983 1349931911499192825622033 := by
  unfold tailWord_2628983
  simp only [CollatzResearch.WordTrace]
  refine ⟨95886887434651060395227603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63924591623100706930151735 95886887434651060395227603)
  ·
    refine ⟨143830331151976590592841405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95886887434651060395227603 143830331151976590592841405)
    ·
      refine ⟨53936374181991221472315527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143830331151976590592841405 53936374181991221472315527)
      ·
        refine ⟨80904561272986832208473291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53936374181991221472315527 80904561272986832208473291)
        ·
          refine ⟨121356841909480248312709937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80904561272986832208473291 121356841909480248312709937)
          ·
            refine ⟨91017631432110186234532453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121356841909480248312709937 91017631432110186234532453)
            ·
              refine ⟨17065805893520659918974835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91017631432110186234532453 17065805893520659918974835)
              ·
                refine ⟨25598708840280989878462253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17065805893520659918974835 25598708840280989878462253)
                ·
                  refine ⟨9599515815105371204423345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25598708840280989878462253 9599515815105371204423345)
                  ·
                    refine ⟨7199636861329028403317509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9599515815105371204423345 7199636861329028403317509)
                    ·
                      refine ⟨1349931911499192825622033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7199636861329028403317509 1349931911499192825622033)
                      ·
                        rfl

theorem cell23_2628983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2628983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2628983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2628983 prefixEnd_2628983 := by exact prefixLift 2628983
  have htrace : WordTrace (prefixWord ++ tailWord_2628983) baseStart_2628983 baseEnd_2628983 := by
    simpa [prefixWord, tailWord_2628983, baseEnd_2628983] using wordTrace_append hprefix tailTrace_2628983
  have hstable : (prefixWord ++ tailWord_2628983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2628983).length < 2 ^ (prefixWord ++ tailWord_2628983).sum := by decide
  have hdescent : baseEnd_2628983 < baseStart_2628983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2628983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629037 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2629037 : Nat := 118140960795 + 2629037 * 2 ^ 59
def prefixEnd_2629037 : Nat := 4983230072969 + 3 ^ 40 * 2629037 * 2
def baseEnd_2629037 : Nat := 1349959639454535614346785

theorem tailTrace_2629037 : CollatzResearch.WordTrace tailWord_2629037 prefixEnd_2629037 1349959639454535614346785 := by
  unfold tailWord_2629037
  simp only [CollatzResearch.WordTrace]
  refine ⟨95888856976455427617693365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63925904650970285078462243 95888856976455427617693365)
  ·
    refine ⟨8989580341542696339158753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95888856976455427617693365 8989580341542696339158753)
    ·
      refine ⟨6742185256157022254369065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8989580341542696339158753 6742185256157022254369065)
      ·
        refine ⟨5056638942117766690776799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6742185256157022254369065 5056638942117766690776799)
        ·
          refine ⟨7584958413176650036165199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056638942117766690776799 7584958413176650036165199)
          ·
            refine ⟨11377437619764975054247799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584958413176650036165199 11377437619764975054247799)
            ·
              refine ⟨17066156429647462581371699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11377437619764975054247799 17066156429647462581371699)
              ·
                refine ⟨25599234644471193872057549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17066156429647462581371699 25599234644471193872057549)
                ·
                  refine ⟨9599712991676697702021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25599234644471193872057549 9599712991676697702021581)
                  ·
                    refine ⟨3599892371878761638258093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9599712991676697702021581 3599892371878761638258093)
                    ·
                      refine ⟨1349959639454535614346785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3599892371878761638258093 1349959639454535614346785)
                      ·
                        rfl

theorem cell23_2629037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2629037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629037 prefixEnd_2629037 := by exact prefixLift 2629037
  have htrace : WordTrace (prefixWord ++ tailWord_2629037) baseStart_2629037 baseEnd_2629037 := by
    simpa [prefixWord, tailWord_2629037, baseEnd_2629037] using wordTrace_append hprefix tailTrace_2629037
  have hstable : (prefixWord ++ tailWord_2629037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629037).length < 2 ^ (prefixWord ++ tailWord_2629037).sum := by decide
  have hdescent : baseEnd_2629037 < baseStart_2629037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629043 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_2629043 : Nat := 118140960795 + 2629043 * 2 ^ 59
def prefixEnd_2629043 : Nat := 4983230072969 + 3 ^ 40 * 2629043 * 2
def baseEnd_2629043 : Nat := 1349962720338462590871757

theorem tailTrace_2629043 : CollatzResearch.WordTrace tailWord_2629043 prefixEnd_2629043 1349962720338462590871757 := by
  unfold tailWord_2629043
  simp only [CollatzResearch.WordTrace]
  refine ⟨95889075814433690642411783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63926050542955793761607855 95889075814433690642411783)
  ·
    refine ⟨143833613721650535963617675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95889075814433690642411783 143833613721650535963617675)
    ·
      refine ⟨215750420582475803945426513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143833613721650535963617675 215750420582475803945426513)
      ·
        refine ⟨161812815436856852959069885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215750420582475803945426513 161812815436856852959069885)
        ·
          refine ⟨60679805788821319859651207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161812815436856852959069885 60679805788821319859651207)
          ·
            refine ⟨91019708683231979789476811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60679805788821319859651207 91019708683231979789476811)
            ·
              refine ⟨136529563024847969684215217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91019708683231979789476811 136529563024847969684215217)
              ·
                refine ⟨102397172268635977263161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136529563024847969684215217 102397172268635977263161413)
                ·
                  refine ⟨19199469800369245736842765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102397172268635977263161413 19199469800369245736842765)
                  ·
                    refine ⟨7199801175138467151316037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19199469800369245736842765 7199801175138467151316037)
                    ·
                      refine ⟨1349962720338462590871757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7199801175138467151316037 1349962720338462590871757)
                      ·
                        rfl

theorem cell23_2629043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_2629043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629043 prefixEnd_2629043 := by exact prefixLift 2629043
  have htrace : WordTrace (prefixWord ++ tailWord_2629043) baseStart_2629043 baseEnd_2629043 := by
    simpa [prefixWord, tailWord_2629043, baseEnd_2629043] using wordTrace_append hprefix tailTrace_2629043
  have hstable : (prefixWord ++ tailWord_2629043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629043).length < 2 ^ (prefixWord ++ tailWord_2629043).sum := by decide
  have hdescent : baseEnd_2629043 < baseStart_2629043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629098 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_2629098 : Nat := 118140960795 + 2629098 * 2 ^ 59
def prefixEnd_2629098 : Nat := 4983230072969 + 3 ^ 40 * 2629098 * 2
def baseEnd_2629098 : Nat := 1349990961774459875684005

theorem tailTrace_2629098 : CollatzResearch.WordTrace tailWord_2629098 prefixEnd_2629098 1349990961774459875684005 := by
  unfold tailWord_2629098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972770457308608758915987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63927387886156290023775965 23972770457308608758915987)
  ·
    refine ⟨35959155685962913138373981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23972770457308608758915987 35959155685962913138373981)
    ·
      refine ⟨13484683382236092426890243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35959155685962913138373981 13484683382236092426890243)
      ·
        refine ⟨20227025073354138640335365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13484683382236092426890243 20227025073354138640335365)
        ·
          refine ⟨3792567201253900995062881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20227025073354138640335365 3792567201253900995062881)
          ·
            refine ⟨2844425400940425746297161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792567201253900995062881 2844425400940425746297161)
            ·
              refine ⟨2133319050705319309722871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844425400940425746297161 2133319050705319309722871)
              ·
                refine ⟨3199978576057978964584307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133319050705319309722871 3199978576057978964584307)
                ·
                  refine ⟨4799967864086968446876461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199978576057978964584307 4799967864086968446876461)
                  ·
                    refine ⟨1799987949032613167578673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4799967864086968446876461 1799987949032613167578673)
                    ·
                      refine ⟨1349990961774459875684005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1799987949032613167578673 1349990961774459875684005)
                      ·
                        rfl

theorem cell23_2629098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_2629098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629098 prefixEnd_2629098 := by exact prefixLift 2629098
  have htrace : WordTrace (prefixWord ++ tailWord_2629098) baseStart_2629098 baseEnd_2629098 := by
    simpa [prefixWord, tailWord_2629098, baseEnd_2629098] using wordTrace_append hprefix tailTrace_2629098
  have hstable : (prefixWord ++ tailWord_2629098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629098).length < 2 ^ (prefixWord ++ tailWord_2629098).sum := by decide
  have hdescent : baseEnd_2629098 < baseStart_2629098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629117 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 5]
def baseStart_2629117 : Nat := 118140960795 + 2629117 * 2 ^ 59
def prefixEnd_2629117 : Nat := 4983230072969 + 3 ^ 40 * 2629117 * 2
def baseEnd_2629117 : Nat := 150000079767432811260713

theorem tailTrace_2629117 : CollatzResearch.WordTrace tailWord_2629117 prefixEnd_2629117 150000079767432811260713 := by
  unfold tailWord_2629117
  simp only [CollatzResearch.WordTrace]
  refine ⟨95891774816165601280605605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63927849877443734187070403 95891774816165601280605605)
  ·
    refine ⟨17979707778031050240113551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95891774816165601280605605 17979707778031050240113551)
    ·
      refine ⟨26969561667046575360170327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17979707778031050240113551 26969561667046575360170327)
      ·
        refine ⟨40454342500569863040255491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26969561667046575360170327 40454342500569863040255491)
        ·
          refine ⟨60681513750854794560383237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40454342500569863040255491 60681513750854794560383237)
          ·
            refine ⟨11377783828285273980071857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60681513750854794560383237 11377783828285273980071857)
            ·
              refine ⟨8533337871213955485053893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11377783828285273980071857 8533337871213955485053893)
              ·
                refine ⟨1600000850852616653447605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8533337871213955485053893 1600000850852616653447605)
                ·
                  refine ⟨150000079767432811260713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600000850852616653447605 150000079767432811260713)
                  ·
                    rfl

theorem cell23_2629117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_2629117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629117 prefixEnd_2629117 := by exact prefixLift 2629117
  have htrace : WordTrace (prefixWord ++ tailWord_2629117) baseStart_2629117 baseEnd_2629117 := by
    simpa [prefixWord, tailWord_2629117, baseEnd_2629117] using wordTrace_append hprefix tailTrace_2629117
  have hstable : (prefixWord ++ tailWord_2629117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629117).length < 2 ^ (prefixWord ++ tailWord_2629117).sum := by decide
  have hdescent : baseEnd_2629117 < baseStart_2629117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629127 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2629127 : Nat := 118140960795 + 2629127 * 2 ^ 59
def prefixEnd_2629127 : Nat := 4983230072969 + 3 ^ 40 * 2629127 * 2
def baseEnd_2629127 : Nat := 1350005852713440262221371

theorem tailTrace_2629127 : CollatzResearch.WordTrace tailWord_2629127 prefixEnd_2629127 1350005852713440262221371 := by
  unfold tailWord_2629127
  simp only [CollatzResearch.WordTrace]
  refine ⟨95892139546129372988469635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63928093030752915325646423 95892139546129372988469635)
  ·
    refine ⟨143838209319194059482704453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95892139546129372988469635 143838209319194059482704453)
    ·
      refine ⟨26969664247348886153007085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143838209319194059482704453 26969664247348886153007085)
      ·
        refine ⟨10113624092755832307377657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26969664247348886153007085 10113624092755832307377657)
        ·
          refine ⟨7585218069566874230533243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10113624092755832307377657 7585218069566874230533243)
          ·
            refine ⟨11377827104350311345799865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585218069566874230533243 11377827104350311345799865)
            ·
              refine ⟨8533370328262733509349899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11377827104350311345799865 8533370328262733509349899)
              ·
                refine ⟨12800055492394100264024849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533370328262733509349899 12800055492394100264024849)
                ·
                  refine ⟨9600041619295575198018637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12800055492394100264024849 9600041619295575198018637)
                  ·
                    refine ⟨3600015607235840699256989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9600041619295575198018637 3600015607235840699256989)
                    ·
                      refine ⟨1350005852713440262221371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3600015607235840699256989 1350005852713440262221371)
                      ·
                        rfl

theorem cell23_2629127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2629127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629127 prefixEnd_2629127 := by exact prefixLift 2629127
  have htrace : WordTrace (prefixWord ++ tailWord_2629127) baseStart_2629127 baseEnd_2629127 := by
    simpa [prefixWord, tailWord_2629127, baseEnd_2629127] using wordTrace_append hprefix tailTrace_2629127
  have hstable : (prefixWord ++ tailWord_2629127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629127).length < 2 ^ (prefixWord ++ tailWord_2629127).sum := by decide
  have hdescent : baseEnd_2629127 < baseStart_2629127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629130 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_2629130 : Nat := 118140960795 + 2629130 * 2 ^ 59
def prefixEnd_2629130 : Nat := 4983230072969 + 3 ^ 40 * 2629130 * 2
def baseEnd_2629130 : Nat := 450002464385134583494619

theorem tailTrace_2629130 : CollatzResearch.WordTrace tailWord_2629130 prefixEnd_2629130 450002464385134583494619 := by
  unfold tailWord_2629130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23973062241279626125207211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63928165976745669667219229 23973062241279626125207211)
  ·
    refine ⟨35959593361919439187810817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23973062241279626125207211 35959593361919439187810817)
    ·
      refine ⟨26969695021439579390858113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35959593361919439187810817 26969695021439579390858113)
      ·
        refine ⟨20227271266079684543143585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26969695021439579390858113 20227271266079684543143585)
        ·
          refine ⟨15170453449559763407357689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20227271266079684543143585 15170453449559763407357689)
          ·
            refine ⟨11377840087169822555518267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15170453449559763407357689 11377840087169822555518267)
            ·
              refine ⟨17066760130754733833277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11377840087169822555518267 17066760130754733833277401)
              ·
                refine ⟨12800070098066050374958051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17066760130754733833277401 12800070098066050374958051)
                ·
                  refine ⟨19200105147099075562437077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12800070098066050374958051 19200105147099075562437077)
                  ·
                    refine ⟨450002464385134583494619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19200105147099075562437077 450002464385134583494619)
                    ·
                      rfl

theorem cell23_2629130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_2629130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629130 prefixEnd_2629130 := by exact prefixLift 2629130
  have htrace : WordTrace (prefixWord ++ tailWord_2629130) baseStart_2629130 baseEnd_2629130 := by
    simpa [prefixWord, tailWord_2629130, baseEnd_2629130] using wordTrace_append hprefix tailTrace_2629130
  have hstable : (prefixWord ++ tailWord_2629130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629130).length < 2 ^ (prefixWord ++ tailWord_2629130).sum := by decide
  have hdescent : baseEnd_2629130 < baseStart_2629130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629174 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2629174 : Nat := 118140960795 + 2629174 * 2 ^ 59
def prefixEnd_2629174 : Nat := 4983230072969 + 3 ^ 40 * 2629174 * 2
def baseEnd_2629174 : Nat := 1350029986304201578333655

theorem tailTrace_2629174 : CollatzResearch.WordTrace tailWord_2629174 prefixEnd_2629174 1350029986304201578333655 := by
  unfold tailWord_2629174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5993365861059943750964411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63929235851306066676953717 5993365861059943750964411)
  ·
    refine ⟨8990048791589915626446617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5993365861059943750964411 8990048791589915626446617)
    ·
      refine ⟨6742536593692436719834963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8990048791589915626446617 6742536593692436719834963)
      ·
        refine ⟨10113804890538655079752445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742536593692436719834963 10113804890538655079752445)
        ·
          refine ⟨3792676833951995654907167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10113804890538655079752445 3792676833951995654907167)
          ·
            refine ⟨5689015250927993482360751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792676833951995654907167 5689015250927993482360751)
            ·
              refine ⟨8533522876391990223541127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689015250927993482360751 8533522876391990223541127)
              ·
                refine ⟨12800284314587985335311691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533522876391990223541127 12800284314587985335311691)
                ·
                  refine ⟨19200426471881978002967537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12800284314587985335311691 19200426471881978002967537)
                  ·
                    refine ⟨14400319853911483502225653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19200426471881978002967537 14400319853911483502225653)
                    ·
                      refine ⟨1350029986304201578333655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14400319853911483502225653 1350029986304201578333655)
                      ·
                        rfl

theorem cell23_2629174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2629174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629174 prefixEnd_2629174 := by exact prefixLift 2629174
  have htrace : WordTrace (prefixWord ++ tailWord_2629174) baseStart_2629174 baseEnd_2629174 := by
    simpa [prefixWord, tailWord_2629174, baseEnd_2629174] using wordTrace_append hprefix tailTrace_2629174
  have hstable : (prefixWord ++ tailWord_2629174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629174).length < 2 ^ (prefixWord ++ tailWord_2629174).sum := by decide
  have hdescent : baseEnd_2629174 < baseStart_2629174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629204 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2629204 : Nat := 118140960795 + 2629204 * 2 ^ 59
def prefixEnd_2629204 : Nat := 4983230072969 + 3 ^ 40 * 2629204 * 2
def baseEnd_2629204 : Nat := 1350045390723836460958517

theorem tailTrace_2629204 : CollatzResearch.WordTrace tailWord_2629204 prefixEnd_2629204 1350045390723836460958517 := by
  unfold tailWord_2629204
  simp only [CollatzResearch.WordTrace]
  refine ⟨47947473983425207569511333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63929965311233610092681777 47947473983425207569511333)
  ·
    refine ⟨8990151371892226419283375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47947473983425207569511333 8990151371892226419283375)
    ·
      refine ⟨13485227057838339628925063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8990151371892226419283375 13485227057838339628925063)
      ·
        refine ⟨20227840586757509443387595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485227057838339628925063 20227840586757509443387595)
        ·
          refine ⟨30341760880136264165081393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20227840586757509443387595 30341760880136264165081393)
          ·
            refine ⟨22756320660102198123811045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30341760880136264165081393 22756320660102198123811045)
            ·
              refine ⟨4266810123769162148214571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22756320660102198123811045 4266810123769162148214571)
              ·
                refine ⟨6400215185653743222321857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266810123769162148214571 6400215185653743222321857)
                ·
                  refine ⟨4800161389240307416741393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6400215185653743222321857 4800161389240307416741393)
                  ·
                    refine ⟨3600121041930230562556045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800161389240307416741393 3600121041930230562556045)
                    ·
                      refine ⟨1350045390723836460958517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3600121041930230562556045 1350045390723836460958517)
                      ·
                        rfl

theorem cell23_2629204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2629204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629204 prefixEnd_2629204 := by exact prefixLift 2629204
  have htrace : WordTrace (prefixWord ++ tailWord_2629204) baseStart_2629204 baseEnd_2629204 := by
    simpa [prefixWord, tailWord_2629204, baseEnd_2629204] using wordTrace_append hprefix tailTrace_2629204
  have hstable : (prefixWord ++ tailWord_2629204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629204).length < 2 ^ (prefixWord ++ tailWord_2629204).sum := by decide
  have hdescent : baseEnd_2629204 < baseStart_2629204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629224 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 6]
def baseStart_2629224 : Nat := 118140960795 + 2629224 * 2 ^ 59
def prefixEnd_2629224 : Nat := 4983230072969 + 3 ^ 40 * 2629224 * 2
def baseEnd_2629224 : Nat := 150006184481880709189825

theorem tailTrace_2629224 : CollatzResearch.WordTrace tailWord_2629224 prefixEnd_2629224 150006184481880709189825 := by
  unfold tailWord_2629224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47947838713388979277375363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63930451617851972369833817 47947838713388979277375363)
  ·
    refine ⟨71921758070083468916063045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47947838713388979277375363 71921758070083468916063045)
    ·
      refine ⟨13485329638140650421761821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71921758070083468916063045 13485329638140650421761821)
      ·
        refine ⟨5056998614302743908160683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13485329638140650421761821 5056998614302743908160683)
        ·
          refine ⟨7585497921454115862241025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056998614302743908160683 7585497921454115862241025)
          ·
            refine ⟨5689123441090586896680769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7585497921454115862241025 5689123441090586896680769)
            ·
              refine ⟨4266842580817940172510577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5689123441090586896680769 4266842580817940172510577)
              ·
                refine ⟨3200131935613455129382933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266842580817940172510577 3200131935613455129382933)
                ·
                  refine ⟨150006184481880709189825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3200131935613455129382933 150006184481880709189825)
                  ·
                    rfl

theorem cell23_2629224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_2629224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629224 prefixEnd_2629224 := by exact prefixLift 2629224
  have htrace : WordTrace (prefixWord ++ tailWord_2629224) baseStart_2629224 baseEnd_2629224 := by
    simpa [prefixWord, tailWord_2629224, baseEnd_2629224] using wordTrace_append hprefix tailTrace_2629224
  have hstable : (prefixWord ++ tailWord_2629224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629224).length < 2 ^ (prefixWord ++ tailWord_2629224).sum := by decide
  have hdescent : baseEnd_2629224 < baseStart_2629224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629240 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2629240 : Nat := 118140960795 + 2629240 * 2 ^ 59
def prefixEnd_2629240 : Nat := 4983230072969 + 3 ^ 40 * 2629240 * 2
def baseEnd_2629240 : Nat := 1350063876027398320108351

theorem tailTrace_2629240 : CollatzResearch.WordTrace tailWord_2629240 prefixEnd_2629240 1350063876027398320108351 := by
  unfold tailWord_2629240
  simp only [CollatzResearch.WordTrace]
  refine ⟨47948130497359996643666587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63930840663146662191555449 47948130497359996643666587)
  ·
    refine ⟨71922195746039994965499881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47948130497359996643666587 71922195746039994965499881)
    ·
      refine ⟨53941646809529996224124911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71922195746039994965499881 53941646809529996224124911)
      ·
        refine ⟨80912470214294994336187367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53941646809529996224124911 80912470214294994336187367)
        ·
          refine ⟨121368705321442491504281051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80912470214294994336187367 121368705321442491504281051)
          ·
            refine ⟨182053057982163737256421577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121368705321442491504281051 182053057982163737256421577)
            ·
              refine ⟨136539793486622802942316183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182053057982163737256421577 136539793486622802942316183)
              ·
                refine ⟨204809690229934204413474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136539793486622802942316183 204809690229934204413474275)
                ·
                  refine ⟨307214535344901306620211413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204809690229934204413474275 307214535344901306620211413)
                  ·
                    refine ⟨7200340672146124373911205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 307214535344901306620211413 7200340672146124373911205)
                    ·
                      refine ⟨1350063876027398320108351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7200340672146124373911205 1350063876027398320108351)
                      ·
                        rfl

theorem cell23_2629240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2629240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629240 prefixEnd_2629240 := by exact prefixLift 2629240
  have htrace : WordTrace (prefixWord ++ tailWord_2629240) baseStart_2629240 baseEnd_2629240 := by
    simpa [prefixWord, tailWord_2629240, baseEnd_2629240] using wordTrace_append hprefix tailTrace_2629240
  have hstable : (prefixWord ++ tailWord_2629240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629240).length < 2 ^ (prefixWord ++ tailWord_2629240).sum := by decide
  have hdescent : baseEnd_2629240 < baseStart_2629240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629257 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_2629257 : Nat := 118140960795 + 2629257 * 2 ^ 59
def prefixEnd_2629257 : Nat := 4983230072969 + 3 ^ 40 * 2629257 * 2
def baseEnd_2629257 : Nat := 1350072605198524753595773

theorem tailTrace_2629257 : CollatzResearch.WordTrace tailWord_2629257 prefixEnd_2629257 1350072605198524753595773 := by
  unfold tailWord_2629257
  simp only [CollatzResearch.WordTrace]
  refine ⟨95896881035658405190702025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63931254023772270127134683 95896881035658405190702025)
  ·
    refine ⟨71922660776743803893026519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95896881035658405190702025 71922660776743803893026519)
    ·
      refine ⟨107883991165115705839539779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71922660776743803893026519 107883991165115705839539779)
      ·
        refine ⟨161825986747673558759309669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107883991165115705839539779 161825986747673558759309669)
        ·
          refine ⟨30342372515188792267370563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161825986747673558759309669 30342372515188792267370563)
          ·
            refine ⟨45513558772783188401055845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30342372515188792267370563 45513558772783188401055845)
            ·
              refine ⟨8533792269896847825197971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45513558772783188401055845 8533792269896847825197971)
              ·
                refine ⟨12800688404845271737796957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533792269896847825197971 12800688404845271737796957)
                ·
                  refine ⟨4800258151816976901673859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12800688404845271737796957 4800258151816976901673859)
                  ·
                    refine ⟨7200387227725465352510789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4800258151816976901673859 7200387227725465352510789)
                    ·
                      refine ⟨1350072605198524753595773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7200387227725465352510789 1350072605198524753595773)
                      ·
                        rfl

theorem cell23_2629257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_2629257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629257 prefixEnd_2629257 := by exact prefixLift 2629257
  have htrace : WordTrace (prefixWord ++ tailWord_2629257) baseStart_2629257 baseEnd_2629257 := by
    simpa [prefixWord, tailWord_2629257, baseEnd_2629257] using wordTrace_append hprefix tailTrace_2629257
  have hstable : (prefixWord ++ tailWord_2629257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629257).length < 2 ^ (prefixWord ++ tailWord_2629257).sum := by decide
  have hdescent : baseEnd_2629257 < baseStart_2629257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629271 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 1, 5]
def baseStart_2629271 : Nat := 118140960795 + 2629271 * 2 ^ 59
def prefixEnd_2629271 : Nat := 4983230072969 + 3 ^ 40 * 2629271 * 2
def baseEnd_2629271 : Nat := 450026597975895899606903

theorem tailTrace_2629271 : CollatzResearch.WordTrace tailWord_2629271 prefixEnd_2629271 450026597975895899606903 := by
  unfold tailWord_2629271
  simp only [CollatzResearch.WordTrace]
  refine ⟨95897391657607685581711667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63931594438405123721141111 95897391657607685581711667)
  ·
    refine ⟨143846087486411528372567501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95897391657607685581711667 143846087486411528372567501)
    ·
      refine ⟨53942282807404323139712813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143846087486411528372567501 53942282807404323139712813)
      ·
        refine ⟨20228356052776621177392305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53942282807404323139712813 20228356052776621177392305)
        ·
          refine ⟨15171267039582465883044229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20228356052776621177392305 15171267039582465883044229)
          ·
            refine ⟨2844612569921712353070793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15171267039582465883044229 2844612569921712353070793)
            ·
              refine ⟨2133459427441284264803095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844612569921712353070793 2133459427441284264803095)
              ·
                refine ⟨3200189141161926397204643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133459427441284264803095 3200189141161926397204643)
                ·
                  refine ⟨4800283711742889595806965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200189141161926397204643 4800283711742889595806965)
                  ·
                    refine ⟨450026597975895899606903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4800283711742889595806965 450026597975895899606903)
                    ·
                      rfl

theorem cell23_2629271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_2629271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629271 prefixEnd_2629271 := by exact prefixLift 2629271
  have htrace : WordTrace (prefixWord ++ tailWord_2629271) baseStart_2629271 baseEnd_2629271 := by
    simpa [prefixWord, tailWord_2629271, baseEnd_2629271] using wordTrace_append hprefix tailTrace_2629271
  have hstable : (prefixWord ++ tailWord_2629271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629271).length < 2 ^ (prefixWord ++ tailWord_2629271).sum := by decide
  have hdescent : baseEnd_2629271 < baseStart_2629271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629277 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2629277 : Nat := 118140960795 + 2629277 * 2 ^ 59
def prefixEnd_2629277 : Nat := 4983230072969 + 3 ^ 40 * 2629277 * 2
def baseEnd_2629277 : Nat := 1350082874811614675345681

theorem tailTrace_2629277 : CollatzResearch.WordTrace tailWord_2629277 prefixEnd_2629277 1350082874811614675345681 := by
  unfold tailWord_2629277
  simp only [CollatzResearch.WordTrace]
  refine ⟨95897610495585948606430085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63931740330390632404286723 95897610495585948606430085)
  ·
    refine ⟨17980801967922365363705641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95897610495585948606430085 17980801967922365363705641)
    ·
      refine ⟨13485601475941774022779231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17980801967922365363705641 13485601475941774022779231)
      ·
        refine ⟨20228402213912661034168847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485601475941774022779231 20228402213912661034168847)
        ·
          refine ⟨30342603320868991551253271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20228402213912661034168847 30342603320868991551253271)
          ·
            refine ⟨45513904981303487326879907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30342603320868991551253271 45513904981303487326879907)
            ·
              refine ⟨68270857471955230990319861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45513904981303487326879907 68270857471955230990319861)
              ·
                refine ⟨6400392887995802905342487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68270857471955230990319861 6400392887995802905342487)
                ·
                  refine ⟨9600589331993704358013731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6400392887995802905342487 9600589331993704358013731)
                  ·
                    refine ⟨14400883997990556537020597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9600589331993704358013731 14400883997990556537020597)
                    ·
                      refine ⟨1350082874811614675345681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14400883997990556537020597 1350082874811614675345681)
                      ·
                        rfl

theorem cell23_2629277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2629277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629277 prefixEnd_2629277 := by exact prefixLift 2629277
  have htrace : WordTrace (prefixWord ++ tailWord_2629277) baseStart_2629277 baseEnd_2629277 := by
    simpa [prefixWord, tailWord_2629277, baseEnd_2629277] using wordTrace_append hprefix tailTrace_2629277
  have hstable : (prefixWord ++ tailWord_2629277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629277).length < 2 ^ (prefixWord ++ tailWord_2629277).sum := by decide
  have hdescent : baseEnd_2629277 < baseStart_2629277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629284 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_2629284 : Nat := 118140960795 + 2629284 * 2 ^ 59
def prefixEnd_2629284 : Nat := 4983230072969 + 3 ^ 40 * 2629284 * 2
def baseEnd_2629284 : Nat := 450028823058732049319383

theorem tailTrace_2629284 : CollatzResearch.WordTrace tailWord_2629284 prefixEnd_2629284 450028823058732049319383 := by
  unfold tailWord_2629284
  simp only [CollatzResearch.WordTrace]
  refine ⟨47948932903280294400967453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63931910537707059201289937 47948932903280294400967453)
  ·
    refine ⟨17980849838730110400362795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47948932903280294400967453 17980849838730110400362795)
    ·
      refine ⟨26971274758095165600544193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17980849838730110400362795 26971274758095165600544193)
      ·
        refine ⟨20228456068571374200408145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26971274758095165600544193 20228456068571374200408145)
        ·
          refine ⟨15171342051428530650306109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20228456068571374200408145 15171342051428530650306109)
          ·
            refine ⟨5689253269285698993864791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15171342051428530650306109 5689253269285698993864791)
            ·
              refine ⟨8533879903928548490797187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689253269285698993864791 8533879903928548490797187)
              ·
                refine ⟨12800819855892822736195781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533879903928548490797187 12800819855892822736195781)
                ·
                  refine ⟨2400153722979904263036709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12800819855892822736195781 2400153722979904263036709)
                  ·
                    refine ⟨450028823058732049319383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400153722979904263036709 450028823058732049319383)
                    ·
                      rfl

theorem cell23_2629284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_2629284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629284 prefixEnd_2629284 := by exact prefixLift 2629284
  have htrace : WordTrace (prefixWord ++ tailWord_2629284) baseStart_2629284 baseEnd_2629284 := by
    simpa [prefixWord, tailWord_2629284, baseEnd_2629284] using wordTrace_append hprefix tailTrace_2629284
  have hstable : (prefixWord ++ tailWord_2629284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629284).length < 2 ^ (prefixWord ++ tailWord_2629284).sum := by decide
  have hdescent : baseEnd_2629284 < baseStart_2629284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629301 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2629301 : Nat := 118140960795 + 2629301 * 2 ^ 59
def prefixEnd_2629301 : Nat := 4983230072969 + 3 ^ 40 * 2629301 * 2
def baseEnd_2629301 : Nat := 450031732782440860481857

theorem tailTrace_2629301 : CollatzResearch.WordTrace tailWord_2629301 prefixEnd_2629301 450031732782440860481857 := by
  unfold tailWord_2629301
  simp only [CollatzResearch.WordTrace]
  refine ⟨95898485847499000705303757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63932323898332667136869171 95898485847499000705303757)
  ·
    refine ⟨35961932192812125264488909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95898485847499000705303757 35961932192812125264488909)
    ·
      refine ⟨13485724572304546974183341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35961932192812125264488909 13485724572304546974183341)
      ·
        refine ⟨5057146714614205115318753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13485724572304546974183341 5057146714614205115318753)
        ·
          refine ⟨3792860035960653836489065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057146714614205115318753 3792860035960653836489065)
          ·
            refine ⟨2844645026970490377366799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792860035960653836489065 2844645026970490377366799)
            ·
              refine ⟨4266967540455735566050199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844645026970490377366799 4266967540455735566050199)
              ·
                refine ⟨6400451310683603349075299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4266967540455735566050199 6400451310683603349075299)
                ·
                  refine ⟨9600676966025405023612949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6400451310683603349075299 9600676966025405023612949)
                  ·
                    refine ⟨450031732782440860481857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9600676966025405023612949 450031732782440860481857)
                    ·
                      rfl

theorem cell23_2629301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2629301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629301 prefixEnd_2629301 := by exact prefixLift 2629301
  have htrace : WordTrace (prefixWord ++ tailWord_2629301) baseStart_2629301 baseEnd_2629301 := by
    simpa [prefixWord, tailWord_2629301, baseEnd_2629301] using wordTrace_append hprefix tailTrace_2629301
  have hstable : (prefixWord ++ tailWord_2629301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629301).length < 2 ^ (prefixWord ++ tailWord_2629301).sum := by decide
  have hdescent : baseEnd_2629301 < baseStart_2629301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629318 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2629318 : Nat := 118140960795 + 2629318 * 2 ^ 59
def prefixEnd_2629318 : Nat := 4983230072969 + 3 ^ 40 * 2629318 * 2
def baseEnd_2629318 : Nat := 450034642506149671644331

theorem tailTrace_2629318 : CollatzResearch.WordTrace tailWord_2629318 prefixEnd_2629318 450034642506149671644331 := by
  unfold tailWord_2629318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996847059013669144021019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63932737258958275072448405 2996847059013669144021019)
  ·
    refine ⟨4495270588520503716031529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2996847059013669144021019 4495270588520503716031529)
    ·
      refine ⟨3371452941390377787023647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4495270588520503716031529 3371452941390377787023647)
      ·
        refine ⟨5057179412085566680535471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371452941390377787023647 5057179412085566680535471)
        ·
          refine ⟨7585769118128350020803207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5057179412085566680535471 7585769118128350020803207)
          ·
            refine ⟨11378653677192525031204811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585769118128350020803207 11378653677192525031204811)
            ·
              refine ⟨17067980515788787546807217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11378653677192525031204811 17067980515788787546807217)
              ·
                refine ⟨12800985386841590660105413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17067980515788787546807217 12800985386841590660105413)
                ·
                  refine ⟨2400184760032798248769765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12800985386841590660105413 2400184760032798248769765)
                  ·
                    refine ⟨450034642506149671644331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400184760032798248769765 450034642506149671644331)
                    ·
                      rfl

theorem cell23_2629318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2629318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629318 prefixEnd_2629318 := by exact prefixLift 2629318
  have htrace : WordTrace (prefixWord ++ tailWord_2629318) baseStart_2629318 baseEnd_2629318 := by
    simpa [prefixWord, tailWord_2629318, baseEnd_2629318] using wordTrace_append hprefix tailTrace_2629318
  have hstable : (prefixWord ++ tailWord_2629318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629318).length < 2 ^ (prefixWord ++ tailWord_2629318).sum := by decide
  have hdescent : baseEnd_2629318 < baseStart_2629318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629367 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2629367 : Nat := 118140960795 + 2629367 * 2 ^ 59
def prefixEnd_2629367 : Nat := 4983230072969 + 3 ^ 40 * 2629367 * 2
def baseEnd_2629367 : Nat := 1350129088070519323220267

theorem tailTrace_2629367 : CollatzResearch.WordTrace tailWord_2629367 prefixEnd_2629367 1350129088070519323220267 := by
  unfold tailWord_2629367
  simp only [CollatzResearch.WordTrace]
  refine ⟨95900893065259893977206355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63933928710173262651470903 95900893065259893977206355)
  ·
    refine ⟨143851339597889840965809533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95900893065259893977206355 143851339597889840965809533)
    ·
      refine ⟨53944252349208690362178575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143851339597889840965809533 53944252349208690362178575)
      ·
        refine ⟨80916378523813035543267863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53944252349208690362178575 80916378523813035543267863)
        ·
          refine ⟨121374567785719553314901795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80916378523813035543267863 121374567785719553314901795)
          ·
            refine ⟨182061851678579329972352693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121374567785719553314901795 182061851678579329972352693)
            ·
              refine ⟨17068298594866812184908065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182061851678579329972352693 17068298594866812184908065)
              ·
                refine ⟨12801223946150109138681049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17068298594866812184908065 12801223946150109138681049)
                ·
                  refine ⟨9600917959612581854010787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12801223946150109138681049 9600917959612581854010787)
                  ·
                    refine ⟨14401376939418872781016181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9600917959612581854010787 14401376939418872781016181)
                    ·
                      refine ⟨1350129088070519323220267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14401376939418872781016181 1350129088070519323220267)
                      ·
                        rfl

theorem cell23_2629367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2629367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629367 prefixEnd_2629367 := by exact prefixLift 2629367
  have htrace : WordTrace (prefixWord ++ tailWord_2629367) baseStart_2629367 baseEnd_2629367 := by
    simpa [prefixWord, tailWord_2629367, baseEnd_2629367] using wordTrace_append hprefix tailTrace_2629367
  have hstable : (prefixWord ++ tailWord_2629367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629367).length < 2 ^ (prefixWord ++ tailWord_2629367).sum := by decide
  have hdescent : baseEnd_2629367 < baseStart_2629367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629434 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_2629434 : Nat := 118140960795 + 2629434 * 2 ^ 59
def prefixEnd_2629434 : Nat := 4983230072969 + 3 ^ 40 * 2629434 * 2
def baseEnd_2629434 : Nat := 450054497091456853694153

theorem tailTrace_2629434 : CollatzResearch.WordTrace tailWord_2629434 prefixEnd_2629434 450054497091456853694153 := by
  unfold tailWord_2629434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23975834189004291104973839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63935557837344776279930237 23975834189004291104973839)
  ·
    refine ⟨35963751283506436657460759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23975834189004291104973839 35963751283506436657460759)
    ·
      refine ⟨53945626925259654986191139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35963751283506436657460759 53945626925259654986191139)
      ·
        refine ⟨80918440387889482479286709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53945626925259654986191139 80918440387889482479286709)
        ·
          refine ⟨7586103786364638982433129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80918440387889482479286709 7586103786364638982433129)
          ·
            refine ⟨5689577839773479236824847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7586103786364638982433129 5689577839773479236824847)
            ·
              refine ⟨8534366759660218855237271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689577839773479236824847 8534366759660218855237271)
              ·
                refine ⟨12801550139490328282855907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534366759660218855237271 12801550139490328282855907)
                ·
                  refine ⟨19202325209235492424283861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12801550139490328282855907 19202325209235492424283861)
                  ·
                    refine ⟨450054497091456853694153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19202325209235492424283861 450054497091456853694153)
                    ·
                      rfl

theorem cell23_2629434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_2629434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629434 prefixEnd_2629434 := by exact prefixLift 2629434
  have htrace : WordTrace (prefixWord ++ tailWord_2629434) baseStart_2629434 baseEnd_2629434 := by
    simpa [prefixWord, tailWord_2629434, baseEnd_2629434] using wordTrace_append hprefix tailTrace_2629434
  have hstable : (prefixWord ++ tailWord_2629434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629434).length < 2 ^ (prefixWord ++ tailWord_2629434).sum := by decide
  have hdescent : baseEnd_2629434 < baseStart_2629434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629438 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2629438 : Nat := 118140960795 + 2629438 * 2 ^ 59
def prefixEnd_2629438 : Nat := 4983230072969 + 3 ^ 40 * 2629438 * 2
def baseEnd_2629438 : Nat := 150018393910776505048049

theorem tailTrace_2629438 : CollatzResearch.WordTrace tailWord_2629438 prefixEnd_2629438 150018393910776505048049 := by
  unfold tailWord_2629438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987935331000334137880121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63935655098668448735360645 11987935331000334137880121)
  ·
    refine ⟨8990951498250250603410091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11987935331000334137880121 8990951498250250603410091)
    ·
      refine ⟨13486427247375375905115137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8990951498250250603410091 13486427247375375905115137)
      ·
        refine ⟨10114820435531531928836353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13486427247375375905115137 10114820435531531928836353)
        ·
          refine ⟨7586115326648648946627265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114820435531531928836353 7586115326648648946627265)
          ·
            refine ⟨5689586494986486709970449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7586115326648648946627265 5689586494986486709970449)
            ·
              refine ⟨4267189871239865032477837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5689586494986486709970449 4267189871239865032477837)
              ·
                refine ⟨1600196201714949387179189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4267189871239865032477837 1600196201714949387179189)
                ·
                  refine ⟨150018393910776505048049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600196201714949387179189 150018393910776505048049)
                  ·
                    rfl

theorem cell23_2629438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2629438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629438 prefixEnd_2629438 := by exact prefixLift 2629438
  have htrace : WordTrace (prefixWord ++ tailWord_2629438) baseStart_2629438 baseEnd_2629438 := by
    simpa [prefixWord, tailWord_2629438, baseEnd_2629438] using wordTrace_append hprefix tailTrace_2629438
  have hstable : (prefixWord ++ tailWord_2629438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629438).length < 2 ^ (prefixWord ++ tailWord_2629438).sum := by decide
  have hdescent : baseEnd_2629438 < baseStart_2629438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629471 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 4, 2]
def baseStart_2629471 : Nat := 118140960795 + 2629471 * 2 ^ 59
def prefixEnd_2629471 : Nat := 4983230072969 + 3 ^ 40 * 2629471 * 2
def baseEnd_2629471 : Nat := 1350182490058586916319789

theorem tailTrace_2629471 : CollatzResearch.WordTrace tailWord_2629471 prefixEnd_2629471 1350182490058586916319789 := by
  unfold tailWord_2629471
  simp only [CollatzResearch.WordTrace]
  refine ⟨95904686256883119738992267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63936457504588746492661511 95904686256883119738992267)
  ·
    refine ⟨143857029385324679608488401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95904686256883119738992267 143857029385324679608488401)
    ·
      refine ⟨107892772038993509706366301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143857029385324679608488401 107892772038993509706366301)
      ·
        refine ⟨40459789514622566139887363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107892772038993509706366301 40459789514622566139887363)
        ·
          refine ⟨60689684271933849209831045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40459789514622566139887363 60689684271933849209831045)
          ·
            refine ⟨11379315800987596726843321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60689684271933849209831045 11379315800987596726843321)
            ·
              refine ⟨8534486850740697545132491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11379315800987596726843321 8534486850740697545132491)
              ·
                refine ⟨12801730276111046317698737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534486850740697545132491 12801730276111046317698737)
                ·
                  refine ⟨9601297707083284738274053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12801730276111046317698737 9601297707083284738274053)
                  ·
                    refine ⟨1800243320078115888426385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9601297707083284738274053 1800243320078115888426385)
                    ·
                      refine ⟨1350182490058586916319789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800243320078115888426385 1350182490058586916319789)
                      ·
                        rfl

theorem cell23_2629471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_2629471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629471 prefixEnd_2629471 := by exact prefixLift 2629471
  have htrace : WordTrace (prefixWord ++ tailWord_2629471) baseStart_2629471 baseEnd_2629471 := by
    simpa [prefixWord, tailWord_2629471, baseEnd_2629471] using wordTrace_append hprefix tailTrace_2629471
  have hstable : (prefixWord ++ tailWord_2629471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629471).length < 2 ^ (prefixWord ++ tailWord_2629471).sum := by decide
  have hdescent : baseEnd_2629471 < baseStart_2629471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629487 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_2629487 : Nat := 118140960795 + 2629487 * 2 ^ 59
def prefixEnd_2629487 : Nat := 4983230072969 + 3 ^ 40 * 2629487 * 2
def baseEnd_2629487 : Nat := 1350190705749058853719715

theorem tailTrace_2629487 : CollatzResearch.WordTrace tailWord_2629487 prefixEnd_2629487 1350190705749058853719715 := by
  unfold tailWord_2629487
  simp only [CollatzResearch.WordTrace]
  refine ⟨95905269824825154471574715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63936846549883436314383143 95905269824825154471574715)
  ·
    refine ⟨143857904737237731707362073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95905269824825154471574715 143857904737237731707362073)
    ·
      refine ⟨107893428552928298780521555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143857904737237731707362073 107893428552928298780521555)
      ·
        refine ⟨161840142829392448170782333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107893428552928298780521555 161840142829392448170782333)
        ·
          refine ⟨60690053561022168064043375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161840142829392448170782333 60690053561022168064043375)
          ·
            refine ⟨91035080341533252096065063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60690053561022168064043375 91035080341533252096065063)
            ·
              refine ⟨136552620512299878144097595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91035080341533252096065063 136552620512299878144097595)
              ·
                refine ⟨204828930768449817216146393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136552620512299878144097595 204828930768449817216146393)
                ·
                  refine ⟨153621698076337362912109795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204828930768449817216146393 153621698076337362912109795)
                  ·
                    refine ⟨230432547114506044368164693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153621698076337362912109795 230432547114506044368164693)
                    ·
                      refine ⟨1350190705749058853719715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 230432547114506044368164693 1350190705749058853719715)
                      ·
                        rfl

theorem cell23_2629487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_2629487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629487 prefixEnd_2629487 := by exact prefixLift 2629487
  have htrace : WordTrace (prefixWord ++ tailWord_2629487) baseStart_2629487 baseEnd_2629487 := by
    simpa [prefixWord, tailWord_2629487, baseEnd_2629487] using wordTrace_append hprefix tailTrace_2629487
  have hstable : (prefixWord ++ tailWord_2629487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629487).length < 2 ^ (prefixWord ++ tailWord_2629487).sum := by decide
  have hdescent : baseEnd_2629487 < baseStart_2629487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629498 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_2629498 : Nat := 118140960795 + 2629498 * 2 ^ 59
def prefixEnd_2629498 : Nat := 4983230072969 + 3 ^ 40 * 2629498 * 2
def baseEnd_2629498 : Nat := 450065451345419436894055

theorem tailTrace_2629498 : CollatzResearch.WordTrace tailWord_2629498 prefixEnd_2629498 450065451345419436894055 := by
  unfold tailWord_2629498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976417756946325837556287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63937114018523535566816765 23976417756946325837556287)
  ·
    refine ⟨35964626635419488756334431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976417756946325837556287 35964626635419488756334431)
    ·
      refine ⟨53946939953129233134501647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35964626635419488756334431 53946939953129233134501647)
      ·
        refine ⟨80920409929693849701752471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53946939953129233134501647 80920409929693849701752471)
        ·
          refine ⟨121380614894540774552628707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80920409929693849701752471 121380614894540774552628707)
          ·
            refine ⟨182070922341811161828943061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121380614894540774552628707 182070922341811161828943061)
            ·
              refine ⟨4267287242386199105365853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182070922341811161828943061 4267287242386199105365853)
              ·
                refine ⟨1600232715894824664512195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4267287242386199105365853 1600232715894824664512195)
                ·
                  refine ⟨2400349073842236996768293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600232715894824664512195 2400349073842236996768293)
                  ·
                    refine ⟨450065451345419436894055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400349073842236996768293 450065451345419436894055)
                    ·
                      rfl

theorem cell23_2629498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_2629498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629498 prefixEnd_2629498 := by exact prefixLift 2629498
  have htrace : WordTrace (prefixWord ++ tailWord_2629498) baseStart_2629498 baseEnd_2629498 := by
    simpa [prefixWord, tailWord_2629498, baseEnd_2629498] using wordTrace_append hprefix tailTrace_2629498
  have hstable : (prefixWord ++ tailWord_2629498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629498).length < 2 ^ (prefixWord ++ tailWord_2629498).sum := by decide
  have hdescent : baseEnd_2629498 < baseStart_2629498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629528 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 6]
def baseStart_2629528 : Nat := 118140960795 + 2629528 * 2 ^ 59
def prefixEnd_2629528 : Nat := 4983230072969 + 3 ^ 40 * 2629528 * 2
def baseEnd_2629528 : Nat := 150023528717321465923003

theorem tailTrace_2629528 : CollatzResearch.WordTrace tailWord_2629528 prefixEnd_2629528 150023528717321465923003 := by
  unfold tailWord_2629528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47953382608838309236908619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63937843478451078982544825 47953382608838309236908619)
  ·
    refine ⟨71930073913257463855362929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47953382608838309236908619 71930073913257463855362929)
    ·
      refine ⟨53947555434943097891522197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71930073913257463855362929 53947555434943097891522197)
      ·
        refine ⟨2528791661012957713665103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53947555434943097891522197 2528791661012957713665103)
        ·
          refine ⟨3793187491519436570497655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528791661012957713665103 3793187491519436570497655)
          ·
            refine ⟨5689781237279154855746483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793187491519436570497655 5689781237279154855746483)
            ·
              refine ⟨8534671855918732283619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5689781237279154855746483 8534671855918732283619725)
              ·
                refine ⟨3200501945969524606357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8534671855918732283619725 3200501945969524606357397)
                ·
                  refine ⟨150023528717321465923003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3200501945969524606357397 150023528717321465923003)
                  ·
                    rfl

theorem cell23_2629528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_2629528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629528 prefixEnd_2629528 := by exact prefixLift 2629528
  have htrace : WordTrace (prefixWord ++ tailWord_2629528) baseStart_2629528 baseEnd_2629528 := by
    simpa [prefixWord, tailWord_2629528, baseEnd_2629528] using wordTrace_append hprefix tailTrace_2629528
  have hstable : (prefixWord ++ tailWord_2629528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629528).length < 2 ^ (prefixWord ++ tailWord_2629528).sum := by decide
  have hdescent : baseEnd_2629528 < baseStart_2629528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629584 : List Nat := [2, 1, 1, 1, 1, 2, 7, 8]
def baseStart_2629584 : Nat := 118140960795 + 2629584 * 2 ^ 59
def prefixEnd_2629584 : Nat := 4983230072969 + 3 ^ 40 * 2629584 * 2
def baseEnd_2629584 : Nat := 50008907902686850896547

theorem tailTrace_2629584 : CollatzResearch.WordTrace tailWord_2629584 prefixEnd_2629584 50008907902686850896547 := by
  unfold tailWord_2629584
  simp only [CollatzResearch.WordTrace]
  refine ⟨47954403852736870018927903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63939205136982493358570537 47954403852736870018927903)
  ·
    refine ⟨71931605779105305028391855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47954403852736870018927903 71931605779105305028391855)
    ·
      refine ⟨107897408668657957542587783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71931605779105305028391855 107897408668657957542587783)
      ·
        refine ⟨161846113002986936313881675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107897408668657957542587783 161846113002986936313881675)
        ·
          refine ⟨242769169504480404470822513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161846113002986936313881675 242769169504480404470822513)
          ·
            refine ⟨182076877128360303353116885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242769169504480404470822513 182076877128360303353116885)
            ·
              refine ⟨4267426807695944609838677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182076877128360303353116885 4267426807695944609838677)
              ·
                refine ⟨50008907902686850896547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4267426807695944609838677 50008907902686850896547)
                ·
                  rfl

theorem cell23_2629584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_2629584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629584 prefixEnd_2629584 := by exact prefixLift 2629584
  have htrace : WordTrace (prefixWord ++ tailWord_2629584) baseStart_2629584 baseEnd_2629584 := by
    simpa [prefixWord, tailWord_2629584, baseEnd_2629584] using wordTrace_append hprefix tailTrace_2629584
  have hstable : (prefixWord ++ tailWord_2629584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629584).length < 2 ^ (prefixWord ++ tailWord_2629584).sum := by decide
  have hdescent : baseEnd_2629584 < baseStart_2629584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629588 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_2629588 : Nat := 118140960795 + 2629588 * 2 ^ 59
def prefixEnd_2629588 : Nat := 4983230072969 + 3 ^ 40 * 2629588 * 2
def baseEnd_2629588 : Nat := 450080855765054319518917

theorem tailTrace_2629588 : CollatzResearch.WordTrace tailWord_2629588 prefixEnd_2629588 450080855765054319518917 := by
  unfold tailWord_2629588
  simp only [CollatzResearch.WordTrace]
  refine ⟨47954476798729624360500709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63939302398306165814000945 47954476798729624360500709)
  ·
    refine ⟨8991464399761804567593883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47954476798729624360500709 8991464399761804567593883)
    ·
      refine ⟨13487196599642706851390825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991464399761804567593883 13487196599642706851390825)
      ·
        refine ⟨10115397449732030138543119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13487196599642706851390825 10115397449732030138543119)
        ·
          refine ⟨15173096174598045207814679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115397449732030138543119 15173096174598045207814679)
          ·
            refine ⟨22759644261897067811722019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15173096174598045207814679 22759644261897067811722019)
            ·
              refine ⟨34139466392845601717583029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22759644261897067811722019 34139466392845601717583029)
              ·
                refine ⟨3200574974329275161023409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34139466392845601717583029 3200574974329275161023409)
                ·
                  refine ⟨2400431230746956370767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200574974329275161023409 2400431230746956370767557)
                  ·
                    refine ⟨450080855765054319518917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400431230746956370767557 450080855765054319518917)
                    ·
                      rfl

theorem cell23_2629588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_2629588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629588 prefixEnd_2629588 := by exact prefixLift 2629588
  have htrace : WordTrace (prefixWord ++ tailWord_2629588) baseStart_2629588 baseEnd_2629588 := by
    simpa [prefixWord, tailWord_2629588, baseEnd_2629588] using wordTrace_append hprefix tailTrace_2629588
  have hstable : (prefixWord ++ tailWord_2629588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629588).length < 2 ^ (prefixWord ++ tailWord_2629588).sum := by decide
  have hdescent : baseEnd_2629588 < baseStart_2629588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629591 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2629591 : Nat := 118140960795 + 2629591 * 2 ^ 59
def prefixEnd_2629591 : Nat := 4983230072969 + 3 ^ 40 * 2629591 * 2
def baseEnd_2629591 : Nat := 1350244107737126446819237

theorem tailTrace_2629591 : CollatzResearch.WordTrace tailWord_2629591 prefixEnd_2629591 1350244107737126446819237 := by
  unfold tailWord_2629591
  simp only [CollatzResearch.WordTrace]
  refine ⟨95909063016448380233360627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63939375344298920155573751 95909063016448380233360627)
  ·
    refine ⟨143863594524672570350040941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95909063016448380233360627 143863594524672570350040941)
    ·
      refine ⟨53948847946752213881265353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143863594524672570350040941 53948847946752213881265353)
      ·
        refine ⟨40461635960064160410949015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53948847946752213881265353 40461635960064160410949015)
        ·
          refine ⟨60692453940096240616423523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40461635960064160410949015 60692453940096240616423523)
          ·
            refine ⟨91038680910144360924635285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60692453940096240616423523 91038680910144360924635285)
            ·
              refine ⟨4267438167663016918342279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91038680910144360924635285 4267438167663016918342279)
              ·
                refine ⟨6401157251494525377513419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4267438167663016918342279 6401157251494525377513419)
                ·
                  refine ⟨9601735877241788066270129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401157251494525377513419 9601735877241788066270129)
                  ·
                    refine ⟨7201301907931341049702597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9601735877241788066270129 7201301907931341049702597)
                    ·
                      refine ⟨1350244107737126446819237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7201301907931341049702597 1350244107737126446819237)
                      ·
                        rfl

theorem cell23_2629591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2629591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629591 prefixEnd_2629591 := by exact prefixLift 2629591
  have htrace : WordTrace (prefixWord ++ tailWord_2629591) baseStart_2629591 baseEnd_2629591 := by
    simpa [prefixWord, tailWord_2629591, baseEnd_2629591] using wordTrace_append hprefix tailTrace_2629591
  have hstable : (prefixWord ++ tailWord_2629591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629591).length < 2 ^ (prefixWord ++ tailWord_2629591).sum := by decide
  have hdescent : baseEnd_2629591 < baseStart_2629591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629622 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2629622 : Nat := 118140960795 + 2629622 * 2 ^ 59
def prefixEnd_2629622 : Nat := 4983230072969 + 3 ^ 40 * 2629622 * 2
def baseEnd_2629622 : Nat := 450086675212471941843865

theorem tailTrace_2629622 : CollatzResearch.WordTrace tailWord_2629622 prefixEnd_2629622 450086675212471941843865 := by
  unfold tailWord_2629622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994387104958504532983695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63940129119557381685159413 5994387104958504532983695)
  ·
    refine ⟨8991580657437756799475543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994387104958504532983695 8991580657437756799475543)
    ·
      refine ⟨13487370986156635199213315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991580657437756799475543 13487370986156635199213315)
      ·
        refine ⟨20231056479234952798819973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13487370986156635199213315 20231056479234952798819973)
        ·
          refine ⟨3793323089856553649778745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20231056479234952798819973 3793323089856553649778745)
          ·
            refine ⟨2844992317392415237334059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793323089856553649778745 2844992317392415237334059)
            ·
              refine ⟨4267488476088622856001089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844992317392415237334059 4267488476088622856001089)
              ·
                refine ⟨3200616357066467142000817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267488476088622856001089 3200616357066467142000817)
                ·
                  refine ⟨2400462267799850356500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200616357066467142000817 2400462267799850356500613)
                  ·
                    refine ⟨450086675212471941843865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400462267799850356500613 450086675212471941843865)
                    ·
                      rfl

theorem cell23_2629622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2629622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629622 prefixEnd_2629622 := by exact prefixLift 2629622
  have htrace : WordTrace (prefixWord ++ tailWord_2629622) baseStart_2629622 baseEnd_2629622 := by
    simpa [prefixWord, tailWord_2629622, baseEnd_2629622] using wordTrace_append hprefix tailTrace_2629622
  have hstable : (prefixWord ++ tailWord_2629622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629622).length < 2 ^ (prefixWord ++ tailWord_2629622).sum := by decide
  have hdescent : baseEnd_2629622 < baseStart_2629622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629628 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2629628 : Nat := 118140960795 + 2629628 * 2 ^ 59
def prefixEnd_2629628 : Nat := 4983230072969 + 3 ^ 40 * 2629628 * 2
def baseEnd_2629628 : Nat := 1350263106521342802056567

theorem tailTrace_2629628 : CollatzResearch.WordTrace tailWord_2629628 prefixEnd_2629628 1350263106521342802056567 := by
  unfold tailWord_2629628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955206258657167776228769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63940275011542890368305025 47955206258657167776228769)
  ·
    refine ⟨35966404693992875832171577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47955206258657167776228769 35966404693992875832171577)
    ·
      refine ⟨26974803520494656874128683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35966404693992875832171577 26974803520494656874128683)
      ·
        refine ⟨40462205280741985311193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26974803520494656874128683 40462205280741985311193025)
        ·
          refine ⟨30346653960556488983394769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40462205280741985311193025 30346653960556488983394769)
          ·
            refine ⟨22759990470417366737546077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30346653960556488983394769 22759990470417366737546077)
            ·
              refine ⟨8534996426406512526579779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22759990470417366737546077 8534996426406512526579779)
              ·
                refine ⟨12802494639609768789869669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534996426406512526579779 12802494639609768789869669)
                ·
                  refine ⟨2400467744926831648100563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12802494639609768789869669 2400467744926831648100563)
                  ·
                    refine ⟨3600701617390247472150845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2400467744926831648100563 3600701617390247472150845)
                    ·
                      refine ⟨1350263106521342802056567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3600701617390247472150845 1350263106521342802056567)
                      ·
                        rfl

theorem cell23_2629628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2629628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629628 prefixEnd_2629628 := by exact prefixLift 2629628
  have htrace : WordTrace (prefixWord ++ tailWord_2629628) baseStart_2629628 baseEnd_2629628 := by
    simpa [prefixWord, tailWord_2629628, baseEnd_2629628] using wordTrace_append hprefix tailTrace_2629628
  have hstable : (prefixWord ++ tailWord_2629628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629628).length < 2 ^ (prefixWord ++ tailWord_2629628).sum := by decide
  have hdescent : baseEnd_2629628 < baseStart_2629628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629652 : List Nat := [2, 4, 3, 2, 1, 2, 2, 7]
def baseStart_2629652 : Nat := 118140960795 + 2629652 * 2 ^ 59
def prefixEnd_2629652 : Nat := 4983230072969 + 3 ^ 40 * 2629652 * 2
def baseEnd_2629652 : Nat := 50010201113224100302091

theorem tailTrace_2629652 : CollatzResearch.WordTrace tailWord_2629652 prefixEnd_2629652 50010201113224100302091 := by
  unfold tailWord_2629652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955643934613693825665605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63940858579484925100887473 47955643934613693825665605)
  ·
    refine ⟨8991683237740067592312301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47955643934613693825665605 8991683237740067592312301)
    ·
      refine ⟨3371881214152525347117113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8991683237740067592312301 3371881214152525347117113)
      ·
        refine ⟨2528910910614394010337835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3371881214152525347117113 2528910910614394010337835)
        ·
          refine ⟨3793366365921591015506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528910910614394010337835 3793366365921591015506753)
          ·
            refine ⟨2845024774441193261630065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793366365921591015506753 2845024774441193261630065)
            ·
              refine ⟨2133768580830894946222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845024774441193261630065 2133768580830894946222549)
              ·
                refine ⟨50010201113224100302091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2133768580830894946222549 50010201113224100302091)
                ·
                  rfl

theorem cell23_2629652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 7].length) (baseStart_2629652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629652 prefixEnd_2629652 := by exact prefixLift 2629652
  have htrace : WordTrace (prefixWord ++ tailWord_2629652) baseStart_2629652 baseEnd_2629652 := by
    simpa [prefixWord, tailWord_2629652, baseEnd_2629652] using wordTrace_append hprefix tailTrace_2629652
  have hstable : (prefixWord ++ tailWord_2629652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629652).length < 2 ^ (prefixWord ++ tailWord_2629652).sum := by decide
  have hdescent : baseEnd_2629652 < baseStart_2629652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629685 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_2629685 : Nat := 118140960795 + 2629685 * 2 ^ 59
def prefixEnd_2629685 : Nat := 4983230072969 + 3 ^ 40 * 2629685 * 2
def baseEnd_2629685 : Nat := 1350292374918649079043805

theorem tailTrace_2629685 : CollatzResearch.WordTrace tailWord_2629685 prefixEnd_2629685 1350292374918649079043805 := by
  unfold tailWord_2629685
  simp only [CollatzResearch.WordTrace]
  refine ⟨95912491478107834287282509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63941660985405222858188339 95912491478107834287282509)
  ·
    refine ⟨35967184304290437857730941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95912491478107834287282509 35967184304290437857730941)
    ·
      refine ⟨13487694114108914196649103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35967184304290437857730941 13487694114108914196649103)
      ·
        refine ⟨20231541171163371294973655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13487694114108914196649103 20231541171163371294973655)
        ·
          refine ⟨30347311756745056942460483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20231541171163371294973655 30347311756745056942460483)
          ·
            refine ⟨45520967635117585413690725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30347311756745056942460483 45520967635117585413690725)
            ·
              refine ⟨8535181431584547265067011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45520967635117585413690725 8535181431584547265067011)
              ·
                refine ⟨12802772147376820897600517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535181431584547265067011 12802772147376820897600517)
                ·
                  refine ⟨2400519777633153918300097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12802772147376820897600517 2400519777633153918300097)
                  ·
                    refine ⟨1800389833224865438725073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2400519777633153918300097 1800389833224865438725073)
                    ·
                      refine ⟨1350292374918649079043805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800389833224865438725073 1350292374918649079043805)
                      ·
                        rfl

theorem cell23_2629685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_2629685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629685 prefixEnd_2629685 := by exact prefixLift 2629685
  have htrace : WordTrace (prefixWord ++ tailWord_2629685) baseStart_2629685 baseEnd_2629685 := by
    simpa [prefixWord, tailWord_2629685, baseEnd_2629685] using wordTrace_append hprefix tailTrace_2629685
  have hstable : (prefixWord ++ tailWord_2629685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629685).length < 2 ^ (prefixWord ++ tailWord_2629685).sum := by decide
  have hdescent : baseEnd_2629685 < baseStart_2629685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629701 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_2629701 : Nat := 118140960795 + 2629701 * 2 ^ 59
def prefixEnd_2629701 : Nat := 4983230072969 + 3 ^ 40 * 2629701 * 2
def baseEnd_2629701 : Nat := 1350300590609121016443731

theorem tailTrace_2629701 : CollatzResearch.WordTrace tailWord_2629701 prefixEnd_2629701 1350300590609121016443731 := by
  unfold tailWord_2629701
  simp only [CollatzResearch.WordTrace]
  refine ⟨95913075046049869019864957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63942050030699912679909971 95913075046049869019864957)
  ·
    refine ⟨35967403142268700882449359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95913075046049869019864957 35967403142268700882449359)
    ·
      refine ⟨53951104713403051323674039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35967403142268700882449359 53951104713403051323674039)
      ·
        refine ⟨80926657070104576985511059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53951104713403051323674039 80926657070104576985511059)
        ·
          refine ⟨121389985605156865478266589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80926657070104576985511059 121389985605156865478266589)
          ·
            refine ⟨45521244601933824554349971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121389985605156865478266589 45521244601933824554349971)
            ·
              refine ⟨68281866902900736831524957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45521244601933824554349971 68281866902900736831524957)
              ·
                refine ⟨25605700088587776311821859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68281866902900736831524957 25605700088587776311821859)
                ·
                  refine ⟨38408550132881664467732789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25605700088587776311821859 38408550132881664467732789)
                  ·
                    refine ⟨3600801574957656043849949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38408550132881664467732789 3600801574957656043849949)
                    ·
                      refine ⟨1350300590609121016443731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3600801574957656043849949 1350300590609121016443731)
                      ·
                        rfl

theorem cell23_2629701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_2629701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629701 prefixEnd_2629701 := by exact prefixLift 2629701
  have htrace : WordTrace (prefixWord ++ tailWord_2629701) baseStart_2629701 baseEnd_2629701 := by
    simpa [prefixWord, tailWord_2629701, baseEnd_2629701] using wordTrace_append hprefix tailTrace_2629701
  have hstable : (prefixWord ++ tailWord_2629701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629701).length < 2 ^ (prefixWord ++ tailWord_2629701).sum := by decide
  have hdescent : baseEnd_2629701 < baseStart_2629701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629702 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2629702 : Nat := 118140960795 + 2629702 * 2 ^ 59
def prefixEnd_2629702 : Nat := 4983230072969 + 3 ^ 40 * 2629702 * 2
def baseEnd_2629702 : Nat := 1350301104089775512531227

theorem tailTrace_2629702 : CollatzResearch.WordTrace tailWord_2629702 prefixEnd_2629702 1350301104089775512531227 := by
  unfold tailWord_2629702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997284734970195193457855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63942074346030830793767573 2997284734970195193457855)
  ·
    refine ⟨4495927102455292790186783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997284734970195193457855 4495927102455292790186783)
    ·
      refine ⟨6743890653682939185280175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495927102455292790186783 6743890653682939185280175)
      ·
        refine ⟨10115835980524408777920263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743890653682939185280175 10115835980524408777920263)
        ·
          refine ⟨15173753970786613166880395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115835980524408777920263 15173753970786613166880395)
          ·
            refine ⟨22760630956179919750320593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15173753970786613166880395 22760630956179919750320593)
            ·
              refine ⟨17070473217134939812740445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22760630956179919750320593 17070473217134939812740445)
              ·
                refine ⟨6401427456425602429777667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17070473217134939812740445 6401427456425602429777667)
                ·
                  refine ⟨9602141184638403644666501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401427456425602429777667 9602141184638403644666501)
                  ·
                    refine ⟨1800401472119700683374969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9602141184638403644666501 1800401472119700683374969)
                    ·
                      refine ⟨1350301104089775512531227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800401472119700683374969 1350301104089775512531227)
                      ·
                        rfl

theorem cell23_2629702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2629702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629702 prefixEnd_2629702 := by exact prefixLift 2629702
  have htrace : WordTrace (prefixWord ++ tailWord_2629702) baseStart_2629702 baseEnd_2629702 := by
    simpa [prefixWord, tailWord_2629702, baseEnd_2629702] using wordTrace_append hprefix tailTrace_2629702
  have hstable : (prefixWord ++ tailWord_2629702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629702).length < 2 ^ (prefixWord ++ tailWord_2629702).sum := by decide
  have hdescent : baseEnd_2629702 < baseStart_2629702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629731 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2629731 : Nat := 118140960795 + 2629731 * 2 ^ 59
def prefixEnd_2629731 : Nat := 4983230072969 + 3 ^ 40 * 2629731 * 2
def baseEnd_2629731 : Nat := 1350315995028755899068593

theorem tailTrace_2629731 : CollatzResearch.WordTrace tailWord_2629731 prefixEnd_2629731 1350315995028755899068593 := by
  unfold tailWord_2629731
  simp only [CollatzResearch.WordTrace]
  refine ⟨95914169235941184143457047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63942779490627456095638031 95914169235941184143457047)
  ·
    refine ⟨143871253853911776215185571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95914169235941184143457047 143871253853911776215185571)
    ·
      refine ⟨215806880780867664322778357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143871253853911776215185571 215806880780867664322778357)
      ·
        refine ⟨20231895073206343530260471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215806880780867664322778357 20231895073206343530260471)
        ·
          refine ⟨30347842609809515295390707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20231895073206343530260471 30347842609809515295390707)
          ·
            refine ⟨45521763914714272943086061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30347842609809515295390707 45521763914714272943086061)
            ·
              refine ⟨17070661468017852353657273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45521763914714272943086061 17070661468017852353657273)
              ·
                refine ⟨12802996101013389265242955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17070661468017852353657273 12802996101013389265242955)
                ·
                  refine ⟨19204494151520083897864433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12802996101013389265242955 19204494151520083897864433)
                  ·
                    refine ⟨14403370613640062923398325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19204494151520083897864433 14403370613640062923398325)
                    ·
                      refine ⟨1350315995028755899068593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14403370613640062923398325 1350315995028755899068593)
                      ·
                        rfl

theorem cell23_2629731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2629731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629731 prefixEnd_2629731 := by exact prefixLift 2629731
  have htrace : WordTrace (prefixWord ++ tailWord_2629731) baseStart_2629731 baseEnd_2629731 := by
    simpa [prefixWord, tailWord_2629731, baseEnd_2629731] using wordTrace_append hprefix tailTrace_2629731
  have hstable : (prefixWord ++ tailWord_2629731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629731).length < 2 ^ (prefixWord ++ tailWord_2629731).sum := by decide
  have hdescent : baseEnd_2629731 < baseStart_2629731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629781 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 8]
def baseStart_2629781 : Nat := 118140960795 + 2629781 * 2 ^ 59
def prefixEnd_2629781 : Nat := 4983230072969 + 3 ^ 40 * 2629781 * 2
def baseEnd_2629781 : Nat := 150037963229053411493707

theorem tailTrace_2629781 : CollatzResearch.WordTrace tailWord_2629781 prefixEnd_2629781 150037963229053411493707 := by
  unfold tailWord_2629781
  simp only [CollatzResearch.WordTrace]
  refine ⟨95915992885760042682777197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63943995257173361788518131 95915992885760042682777197)
  ·
    refine ⟨35968497332160016006041449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95915992885760042682777197 35968497332160016006041449)
    ·
      refine ⟨26976372999120012004531087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35968497332160016006041449 26976372999120012004531087)
      ·
        refine ⟨40464559498680018006796631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26976372999120012004531087 40464559498680018006796631)
        ·
          refine ⟨60696839248020027010194947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40464559498680018006796631 60696839248020027010194947)
          ·
            refine ⟨91045258872030040515292421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60696839248020027010194947 91045258872030040515292421)
            ·
              refine ⟨17070986038505632596617329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91045258872030040515292421 17070986038505632596617329)
              ·
                refine ⟨12803239528879224447462997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17070986038505632596617329 12803239528879224447462997)
                ·
                  refine ⟨150037963229053411493707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12803239528879224447462997 150037963229053411493707)
                  ·
                    rfl

theorem cell23_2629781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_2629781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629781 prefixEnd_2629781 := by exact prefixLift 2629781
  have htrace : WordTrace (prefixWord ++ tailWord_2629781) baseStart_2629781 baseEnd_2629781 := by
    simpa [prefixWord, tailWord_2629781, baseEnd_2629781] using wordTrace_append hprefix tailTrace_2629781
  have hstable : (prefixWord ++ tailWord_2629781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629781).length < 2 ^ (prefixWord ++ tailWord_2629781).sum := by decide
  have hdescent : baseEnd_2629781 < baseStart_2629781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629815 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 6]
def baseStart_2629815 : Nat := 118140960795 + 2629815 * 2 ^ 59
def prefixEnd_2629815 : Nat := 4983230072969 + 3 ^ 40 * 2629815 * 2
def baseEnd_2629815 : Nat := 150039903044859285602023

theorem tailTrace_2629815 : CollatzResearch.WordTrace tailWord_2629815 prefixEnd_2629815 150039903044859285602023 := by
  unfold tailWord_2629815
  simp only [CollatzResearch.WordTrace]
  refine ⟨95917232967636866489514899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63944821978424577659676599 95917232967636866489514899)
  ·
    refine ⟨143875849451455299734272349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95917232967636866489514899 143875849451455299734272349)
    ·
      refine ⟨53953443544295737400352131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143875849451455299734272349 53953443544295737400352131)
      ·
        refine ⟨80930165316443606100528197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53953443544295737400352131 80930165316443606100528197)
        ·
          refine ⟨15174405996833176143849037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80930165316443606100528197 15174405996833176143849037)
          ·
            refine ⟨5690402248812441053943389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15174405996833176143849037 5690402248812441053943389)
            ·
              refine ⟨2133900843304665395228771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5690402248812441053943389 2133900843304665395228771)
              ·
                refine ⟨3200851264956998092843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133900843304665395228771 3200851264956998092843157)
                ·
                  refine ⟨150039903044859285602023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3200851264956998092843157 150039903044859285602023)
                  ·
                    rfl

theorem cell23_2629815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 6].length) (baseStart_2629815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629815 prefixEnd_2629815 := by exact prefixLift 2629815
  have htrace : WordTrace (prefixWord ++ tailWord_2629815) baseStart_2629815 baseEnd_2629815 := by
    simpa [prefixWord, tailWord_2629815, baseEnd_2629815] using wordTrace_append hprefix tailTrace_2629815
  have hstable : (prefixWord ++ tailWord_2629815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629815).length < 2 ^ (prefixWord ++ tailWord_2629815).sum := by decide
  have hdescent : baseEnd_2629815 < baseStart_2629815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629835 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 2, 3, 2]
def baseStart_2629835 : Nat := 118140960795 + 2629835 * 2 ^ 59
def prefixEnd_2629835 : Nat := 4983230072969 + 3 ^ 40 * 2629835 * 2
def baseEnd_2629835 : Nat := 1350369397016823492168115

theorem tailTrace_2629835 : CollatzResearch.WordTrace tailWord_2629835 prefixEnd_2629835 1350369397016823492168115 := by
  unfold tailWord_2629835
  simp only [CollatzResearch.WordTrace]
  refine ⟨95917962427564409905242959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63945308285042939936828639 95917962427564409905242959)
  ·
    refine ⟨143876943641346614857864439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95917962427564409905242959 143876943641346614857864439)
    ·
      refine ⟨215815415462019922286796659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143876943641346614857864439 215815415462019922286796659)
      ·
        refine ⟨323723123193029883430194989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215815415462019922286796659 323723123193029883430194989)
        ·
          refine ⟨121396171197386206286323121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323723123193029883430194989 121396171197386206286323121)
          ·
            refine ⟨91047128398039654714742341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121396171197386206286323121 91047128398039654714742341)
            ·
              refine ⟨17071336574632435259014189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91047128398039654714742341 17071336574632435259014189)
              ·
                refine ⟨6401751215487163222130321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17071336574632435259014189 6401751215487163222130321)
                ·
                  refine ⟨4801313411615372416597741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6401751215487163222130321 4801313411615372416597741)
                  ·
                    refine ⟨1800492529355764656224153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4801313411615372416597741 1800492529355764656224153)
                    ·
                      refine ⟨1350369397016823492168115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800492529355764656224153 1350369397016823492168115)
                      ·
                        rfl

theorem cell23_2629835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3, 2].length) (baseStart_2629835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629835 prefixEnd_2629835 := by exact prefixLift 2629835
  have htrace : WordTrace (prefixWord ++ tailWord_2629835) baseStart_2629835 baseEnd_2629835 := by
    simpa [prefixWord, tailWord_2629835, baseEnd_2629835] using wordTrace_append hprefix tailTrace_2629835
  have hstable : (prefixWord ++ tailWord_2629835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629835).length < 2 ^ (prefixWord ++ tailWord_2629835).sum := by decide
  have hdescent : baseEnd_2629835 < baseStart_2629835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629836 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_2629836 : Nat := 118140960795 + 2629836 * 2 ^ 59
def prefixEnd_2629836 : Nat := 4983230072969 + 3 ^ 40 * 2629836 * 2
def baseEnd_2629836 : Nat := 450123303499159329418537

theorem tailTrace_2629836 : CollatzResearch.WordTrace tailWord_2629836 prefixEnd_2629836 450123303499159329418537 := by
  unfold tailWord_2629836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47958999450280393538014681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63945332600373858050686241 47958999450280393538014681)
  ·
    refine ⟨35969249587710295153511011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47958999450280393538014681 35969249587710295153511011)
    ·
      refine ⟨53953874381565442730266517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969249587710295153511011 53953874381565442730266517)
      ·
        refine ⟨2529087861635880127981243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53953874381565442730266517 2529087861635880127981243)
        ·
          refine ⟨3793631792453820191971865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529087861635880127981243 3793631792453820191971865)
          ·
            refine ⟨2845223844340365143978899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793631792453820191971865 2845223844340365143978899)
            ·
              refine ⟨4267835766510547715968349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845223844340365143978899 4267835766510547715968349)
              ·
                refine ⟨1600438412441455393488131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4267835766510547715968349 1600438412441455393488131)
                ·
                  refine ⟨2400657618662183090232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600438412441455393488131 2400657618662183090232197)
                  ·
                    refine ⟨450123303499159329418537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400657618662183090232197 450123303499159329418537)
                    ·
                      rfl

theorem cell23_2629836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_2629836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629836 prefixEnd_2629836 := by exact prefixLift 2629836
  have htrace : WordTrace (prefixWord ++ tailWord_2629836) baseStart_2629836 baseEnd_2629836 := by
    simpa [prefixWord, tailWord_2629836, baseEnd_2629836] using wordTrace_append hprefix tailTrace_2629836
  have hstable : (prefixWord ++ tailWord_2629836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629836).length < 2 ^ (prefixWord ++ tailWord_2629836).sum := by decide
  have hdescent : baseEnd_2629836 < baseStart_2629836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629868 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2629868 : Nat := 118140960795 + 2629868 * 2 ^ 59
def prefixEnd_2629868 : Nat := 4983230072969 + 3 ^ 40 * 2629868 * 2
def baseEnd_2629868 : Nat := 1350386341878421863055463

theorem tailTrace_2629868 : CollatzResearch.WordTrace tailWord_2629868 prefixEnd_2629868 1350386341878421863055463 := by
  unfold tailWord_2629868
  simp only [CollatzResearch.WordTrace]
  refine ⟨47959583018222428270597129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63946110690963237694129505 47959583018222428270597129)
  ·
    refine ⟨35969687263666821202947847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47959583018222428270597129 35969687263666821202947847)
    ·
      refine ⟨53954530895500231804421771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969687263666821202947847 53954530895500231804421771)
      ·
        refine ⟨80931796343250347706632657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53954530895500231804421771 80931796343250347706632657)
        ·
          refine ⟨60698847257437760779974493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80931796343250347706632657 60698847257437760779974493)
          ·
            refine ⟨22762067721539160292490435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60698847257437760779974493 22762067721539160292490435)
            ·
              refine ⟨34143101582308740438735653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22762067721539160292490435 34143101582308740438735653)
              ·
                refine ⟨6401831546682888832262935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34143101582308740438735653 6401831546682888832262935)
                ·
                  refine ⟨9602747320024333248394403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401831546682888832262935 9602747320024333248394403)
                  ·
                    refine ⟨14404120980036499872591605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9602747320024333248394403 14404120980036499872591605)
                    ·
                      refine ⟨1350386341878421863055463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14404120980036499872591605 1350386341878421863055463)
                      ·
                        rfl

theorem cell23_2629868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2629868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629868 prefixEnd_2629868 := by exact prefixLift 2629868
  have htrace : WordTrace (prefixWord ++ tailWord_2629868) baseStart_2629868 baseEnd_2629868 := by
    simpa [prefixWord, tailWord_2629868, baseEnd_2629868] using wordTrace_append hprefix tailTrace_2629868
  have hstable : (prefixWord ++ tailWord_2629868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629868).length < 2 ^ (prefixWord ++ tailWord_2629868).sum := by decide
  have hdescent : baseEnd_2629868 < baseStart_2629868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629875 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 2, 4]
def baseStart_2629875 : Nat := 118140960795 + 2629875 * 2 ^ 59
def prefixEnd_2629875 : Nat := 4983230072969 + 3 ^ 40 * 2629875 * 2
def baseEnd_2629875 : Nat := 450129978747667778555977

theorem tailTrace_2629875 : CollatzResearch.WordTrace tailWord_2629875 prefixEnd_2629875 450129978747667778555977 := by
  unfold tailWord_2629875
  simp only [CollatzResearch.WordTrace]
  refine ⟨95919421347419496736699079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63946280898279664491132719 95919421347419496736699079)
  ·
    refine ⟨143879132021129245105048619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95919421347419496736699079 143879132021129245105048619)
    ·
      refine ⟨215818698031693867657572929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143879132021129245105048619 215818698031693867657572929)
      ·
        refine ⟨161864023523770400743179697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215818698031693867657572929 161864023523770400743179697)
        ·
          refine ⟨121398017642827800557384773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161864023523770400743179697 121398017642827800557384773)
          ·
            refine ⟨22762128308030212604509645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121398017642827800557384773 22762128308030212604509645)
            ·
              refine ⟨8535798115511329726691117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22762128308030212604509645 8535798115511329726691117)
              ·
                refine ⟨3200924293316748647509169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8535798115511329726691117 3200924293316748647509169)
                ·
                  refine ⟨2400693219987561485631877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200924293316748647509169 2400693219987561485631877)
                  ·
                    refine ⟨450129978747667778555977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400693219987561485631877 450129978747667778555977)
                    ·
                      rfl

theorem cell23_2629875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 4].length) (baseStart_2629875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629875 prefixEnd_2629875 := by exact prefixLift 2629875
  have htrace : WordTrace (prefixWord ++ tailWord_2629875) baseStart_2629875 baseEnd_2629875 := by
    simpa [prefixWord, tailWord_2629875, baseEnd_2629875] using wordTrace_append hprefix tailTrace_2629875
  have hstable : (prefixWord ++ tailWord_2629875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629875).length < 2 ^ (prefixWord ++ tailWord_2629875).sum := by decide
  have hdescent : baseEnd_2629875 < baseStart_2629875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629882 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_2629882 : Nat := 118140960795 + 2629882 * 2 ^ 59
def prefixEnd_2629882 : Nat := 4983230072969 + 3 ^ 40 * 2629882 * 2
def baseEnd_2629882 : Nat := 1350393530607584808280399

theorem tailTrace_2629882 : CollatzResearch.WordTrace tailWord_2629882 prefixEnd_2629882 1350393530607584808280399 := by
  unfold tailWord_2629882
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979919164598534233050975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63946451105596091288135933 23979919164598534233050975)
  ·
    refine ⟨35969878746897801349576463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23979919164598534233050975 35969878746897801349576463)
    ·
      refine ⟨53954818120346702024364695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969878746897801349576463 53954818120346702024364695)
      ·
        refine ⟨80932227180520053036547043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53954818120346702024364695 80932227180520053036547043)
        ·
          refine ⟨121398340770780079554820565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80932227180520053036547043 121398340770780079554820565)
          ·
            refine ⟨2845273611815158114566107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 121398340770780079554820565 2845273611815158114566107)
            ·
              refine ⟨4267910417722737171849161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845273611815158114566107 4267910417722737171849161)
              ·
                refine ⟨3200932813292052878886871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267910417722737171849161 3200932813292052878886871)
                ·
                  refine ⟨4801399219938079318330307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200932813292052878886871 4801399219938079318330307)
                  ·
                    refine ⟨7202098829907118977495461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4801399219938079318330307 7202098829907118977495461)
                    ·
                      refine ⟨1350393530607584808280399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7202098829907118977495461 1350393530607584808280399)
                      ·
                        rfl

theorem cell23_2629882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_2629882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629882 prefixEnd_2629882 := by exact prefixLift 2629882
  have htrace : WordTrace (prefixWord ++ tailWord_2629882) baseStart_2629882 baseEnd_2629882 := by
    simpa [prefixWord, tailWord_2629882, baseEnd_2629882] using wordTrace_append hprefix tailTrace_2629882
  have hstable : (prefixWord ++ tailWord_2629882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629882).length < 2 ^ (prefixWord ++ tailWord_2629882).sum := by decide
  have hdescent : baseEnd_2629882 < baseStart_2629882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629899 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 1, 2, 2]
def baseStart_2629899 : Nat := 118140960795 + 2629899 * 2 ^ 59
def prefixEnd_2629899 : Nat := 4983230072969 + 3 ^ 40 * 2629899 * 2
def baseEnd_2629899 : Nat := 1350402259778711241767821

theorem tailTrace_2629899 : CollatzResearch.WordTrace tailWord_2629899 prefixEnd_2629899 1350402259778711241767821 := by
  unfold tailWord_2629899
  simp only [CollatzResearch.WordTrace]
  refine ⟨95920296699332548835572751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63946864466221699223715167 95920296699332548835572751)
  ·
    refine ⟨143880445048998823253359127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95920296699332548835572751 143880445048998823253359127)
    ·
      refine ⟨215820667573498234880038691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143880445048998823253359127 215820667573498234880038691)
      ·
        refine ⟨323731001360247352320058037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215820667573498234880038691 323731001360247352320058037)
        ·
          refine ⟨30349781377523189280005441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 323731001360247352320058037 30349781377523189280005441)
          ·
            refine ⟨22762336033142391960004081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30349781377523189280005441 22762336033142391960004081)
            ·
              refine ⟨17071752024856793970003061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22762336033142391960004081 17071752024856793970003061)
              ·
                refine ⟨1600476752330324434687787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17071752024856793970003061 1600476752330324434687787)
                ·
                  refine ⟨2400715128495486652031681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600476752330324434687787 2400715128495486652031681)
                  ·
                    refine ⟨1800536346371614989023761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2400715128495486652031681 1800536346371614989023761)
                    ·
                      refine ⟨1350402259778711241767821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800536346371614989023761 1350402259778711241767821)
                      ·
                        rfl

theorem cell23_2629899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 2, 2].length) (baseStart_2629899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629899 prefixEnd_2629899 := by exact prefixLift 2629899
  have htrace : WordTrace (prefixWord ++ tailWord_2629899) baseStart_2629899 baseEnd_2629899 := by
    simpa [prefixWord, tailWord_2629899, baseEnd_2629899] using wordTrace_append hprefix tailTrace_2629899
  have hstable : (prefixWord ++ tailWord_2629899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629899).length < 2 ^ (prefixWord ++ tailWord_2629899).sum := by decide
  have hdescent : baseEnd_2629899 < baseStart_2629899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629915 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 3]
def baseStart_2629915 : Nat := 118140960795 + 2629915 * 2 ^ 59
def prefixEnd_2629915 : Nat := 4983230072969 + 3 ^ 40 * 2629915 * 2
def baseEnd_2629915 : Nat := 1350410475469183179167747

theorem tailTrace_2629915 : CollatzResearch.WordTrace tailWord_2629915 prefixEnd_2629915 1350410475469183179167747 := by
  unfold tailWord_2629915
  simp only [CollatzResearch.WordTrace]
  refine ⟨95920880267274583568155199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63947253511516389045436799 95920880267274583568155199)
  ·
    refine ⟨143881320400911875352232799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95920880267274583568155199 143881320400911875352232799)
    ·
      refine ⟨215821980601367813028349199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143881320400911875352232799 215821980601367813028349199)
      ·
        refine ⟨323732970902051719542523799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215821980601367813028349199 323732970902051719542523799)
        ·
          refine ⟨485599456353077579313785699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323732970902051719542523799 485599456353077579313785699)
          ·
            refine ⟨728399184529616368970678549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485599456353077579313785699 728399184529616368970678549)
            ·
              refine ⟨34143711774825767295500557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 728399184529616368970678549 34143711774825767295500557)
              ·
                refine ⟨12803891915559662735812709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34143711774825767295500557 12803891915559662735812709)
                ·
                  refine ⟨2400729734167436762964883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12803891915559662735812709 2400729734167436762964883)
                  ·
                    refine ⟨3601094601251155144447325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2400729734167436762964883 3601094601251155144447325)
                    ·
                      refine ⟨1350410475469183179167747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601094601251155144447325 1350410475469183179167747)
                      ·
                        rfl

theorem cell23_2629915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 3].length) (baseStart_2629915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629915 prefixEnd_2629915 := by exact prefixLift 2629915
  have htrace : WordTrace (prefixWord ++ tailWord_2629915) baseStart_2629915 baseEnd_2629915 := by
    simpa [prefixWord, tailWord_2629915, baseEnd_2629915] using wordTrace_append hprefix tailTrace_2629915
  have hstable : (prefixWord ++ tailWord_2629915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629915).length < 2 ^ (prefixWord ++ tailWord_2629915).sum := by decide
  have hdescent : baseEnd_2629915 < baseStart_2629915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629932 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2629932 : Nat := 118140960795 + 2629932 * 2 ^ 59
def prefixEnd_2629932 : Nat := 4983230072969 + 3 ^ 40 * 2629932 * 2
def baseEnd_2629932 : Nat := 1350419204640309612655169

theorem tailTrace_2629932 : CollatzResearch.WordTrace tailWord_2629932 prefixEnd_2629932 1350419204640309612655169 := by
  unfold tailWord_2629932
  simp only [CollatzResearch.WordTrace]
  refine ⟨47960750154106497735762025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63947666872141996981016033 47960750154106497735762025)
  ·
    refine ⟨35970562615579873301821519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47960750154106497735762025 35970562615579873301821519)
    ·
      refine ⟨53955843923369809952732279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35970562615579873301821519 53955843923369809952732279)
      ·
        refine ⟨80933765885054714929098419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53955843923369809952732279 80933765885054714929098419)
        ·
          refine ⟨121400648827582072393647629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80933765885054714929098419 121400648827582072393647629)
          ·
            refine ⟨45525243310343277147617861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121400648827582072393647629 45525243310343277147617861)
            ·
              refine ⟨8535983120689364465178349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45525243310343277147617861 8535983120689364465178349)
              ·
                refine ⟨3200993670258511674441881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8535983120689364465178349 3200993670258511674441881)
                ·
                  refine ⟨2400745252693883755831411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200993670258511674441881 2400745252693883755831411)
                  ·
                    refine ⟨3601117879040825633747117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2400745252693883755831411 3601117879040825633747117)
                    ·
                      refine ⟨1350419204640309612655169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601117879040825633747117 1350419204640309612655169)
                      ·
                        rfl

theorem cell23_2629932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2629932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629932 prefixEnd_2629932 := by exact prefixLift 2629932
  have htrace : WordTrace (prefixWord ++ tailWord_2629932) baseStart_2629932 baseEnd_2629932 := by
    simpa [prefixWord, tailWord_2629932, baseEnd_2629932] using wordTrace_append hprefix tailTrace_2629932
  have hstable : (prefixWord ++ tailWord_2629932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629932).length < 2 ^ (prefixWord ++ tailWord_2629932).sum := by decide
  have hdescent : baseEnd_2629932 < baseStart_2629932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629948 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_2629948 : Nat := 118140960795 + 2629948 * 2 ^ 59
def prefixEnd_2629948 : Nat := 4983230072969 + 3 ^ 40 * 2629948 * 2
def baseEnd_2629948 : Nat := 450142473443593850018365

theorem tailTrace_2629948 : CollatzResearch.WordTrace tailWord_2629948 prefixEnd_2629948 450142473443593850018365 := by
  unfold tailWord_2629948
  simp only [CollatzResearch.WordTrace]
  refine ⟨47961041938077515102053249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63948055917436686802737665 47961041938077515102053249)
  ·
    refine ⟨35970781453558136326539937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47961041938077515102053249 35970781453558136326539937)
    ·
      refine ⟨26978086090168602244904953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35970781453558136326539937 26978086090168602244904953)
      ·
        refine ⟨20233564567626451683678715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26978086090168602244904953 20233564567626451683678715)
        ·
          refine ⟨30350346851439677525518073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20233564567626451683678715 30350346851439677525518073)
          ·
            refine ⟨22762760138579758144138555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30350346851439677525518073 22762760138579758144138555)
            ·
              refine ⟨34144140207869637216207833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22762760138579758144138555 34144140207869637216207833)
              ·
                refine ⟨25608105155902227912155875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34144140207869637216207833 25608105155902227912155875)
                ·
                  refine ⟨38412157733853341868233813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25608105155902227912155875 38412157733853341868233813)
                  ·
                    refine ⟨450142473443593850018365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38412157733853341868233813 450142473443593850018365)
                    ·
                      rfl

theorem cell23_2629948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_2629948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629948 prefixEnd_2629948 := by exact prefixLift 2629948
  have htrace : WordTrace (prefixWord ++ tailWord_2629948) baseStart_2629948 baseEnd_2629948 := by
    simpa [prefixWord, tailWord_2629948, baseEnd_2629948] using wordTrace_append hprefix tailTrace_2629948
  have hstable : (prefixWord ++ tailWord_2629948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629948).length < 2 ^ (prefixWord ++ tailWord_2629948).sum := by decide
  have hdescent : baseEnd_2629948 < baseStart_2629948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629953 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2629953 : Nat := 118140960795 + 2629953 * 2 ^ 59
def prefixEnd_2629953 : Nat := 4983230072969 + 3 ^ 40 * 2629953 * 2
def baseEnd_2629953 : Nat := 1350429987734054030492573

theorem tailTrace_2629953 : CollatzResearch.WordTrace tailWord_2629953 prefixEnd_2629953 1350429987734054030492573 := by
  unfold tailWord_2629953
  simp only [CollatzResearch.WordTrace]
  refine ⟨95922266241136916058038513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63948177494091277372025675 95922266241136916058038513)
  ·
    refine ⟨71941699680852687043528885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95922266241136916058038513 71941699680852687043528885)
    ·
      refine ⟨6744534345079939410330833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71941699680852687043528885 6744534345079939410330833)
      ·
        refine ⟨5058400758809954557748125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6744534345079939410330833 5058400758809954557748125)
        ·
          refine ⟨1896900284553732959155547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5058400758809954557748125 1896900284553732959155547)
          ·
            refine ⟨2845350426830599438733321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896900284553732959155547 2845350426830599438733321)
            ·
              refine ⟨2134012820122949579049991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845350426830599438733321 2134012820122949579049991)
              ·
                refine ⟨3201019230184424368574987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134012820122949579049991 3201019230184424368574987)
                ·
                  refine ⟨4801528845276636552862481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201019230184424368574987 4801528845276636552862481)
                  ·
                    refine ⟨3601146633957477414646861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4801528845276636552862481 3601146633957477414646861)
                    ·
                      refine ⟨1350429987734054030492573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601146633957477414646861 1350429987734054030492573)
                      ·
                        rfl

theorem cell23_2629953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2629953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629953 prefixEnd_2629953 := by exact prefixLift 2629953
  have htrace : WordTrace (prefixWord ++ tailWord_2629953) baseStart_2629953 baseEnd_2629953 := by
    simpa [prefixWord, tailWord_2629953, baseEnd_2629953] using wordTrace_append hprefix tailTrace_2629953
  have hstable : (prefixWord ++ tailWord_2629953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629953).length < 2 ^ (prefixWord ++ tailWord_2629953).sum := by decide
  have hdescent : baseEnd_2629953 < baseStart_2629953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2629989 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_2629989 : Nat := 118140960795 + 2629989 * 2 ^ 59
def prefixEnd_2629989 : Nat := 4983230072969 + 3 ^ 40 * 2629989 * 2
def baseEnd_2629989 : Nat := 1350448473037615889642407

theorem tailTrace_2629989 : CollatzResearch.WordTrace tailWord_2629989 prefixEnd_2629989 1350448473037615889642407 := by
  unfold tailWord_2629989
  simp only [CollatzResearch.WordTrace]
  refine ⟨95923579269006494206349021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63949052846004329470899347 95923579269006494206349021)
  ·
    refine ⟨35971342225877435327380883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95923579269006494206349021 35971342225877435327380883)
    ·
      refine ⟨53957013338816152991071325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35971342225877435327380883 53957013338816152991071325)
      ·
        refine ⟨20233880002056057371651747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53957013338816152991071325 20233880002056057371651747)
        ·
          refine ⟨30350820003084086057477621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20233880002056057371651747 30350820003084086057477621)
          ·
            refine ⟨2845389375289133067888527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30350820003084086057477621 2845389375289133067888527)
            ·
              refine ⟨4268084062933699601832791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845389375289133067888527 4268084062933699601832791)
              ·
                refine ⟨6402126094400549402749187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268084062933699601832791 6402126094400549402749187)
                ·
                  refine ⟨9603189141600824104123781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402126094400549402749187 9603189141600824104123781)
                  ·
                    refine ⟨1800597964050154519523209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9603189141600824104123781 1800597964050154519523209)
                    ·
                      refine ⟨1350448473037615889642407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800597964050154519523209 1350448473037615889642407)
                      ·
                        rfl

theorem cell23_2629989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_2629989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2629989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2629989 prefixEnd_2629989 := by exact prefixLift 2629989
  have htrace : WordTrace (prefixWord ++ tailWord_2629989) baseStart_2629989 baseEnd_2629989 := by
    simpa [prefixWord, tailWord_2629989, baseEnd_2629989] using wordTrace_append hprefix tailTrace_2629989
  have hstable : (prefixWord ++ tailWord_2629989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2629989).length < 2 ^ (prefixWord ++ tailWord_2629989).sum := by decide
  have hdescent : baseEnd_2629989 < baseStart_2629989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2629989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630025 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_2630025 : Nat := 118140960795 + 2630025 * 2 ^ 59
def prefixEnd_2630025 : Nat := 4983230072969 + 3 ^ 40 * 2630025 * 2
def baseEnd_2630025 : Nat := 450155652780392582930747

theorem tailTrace_2630025 : CollatzResearch.WordTrace tailWord_2630025 prefixEnd_2630025 450155652780392582930747 := by
  unfold tailWord_2630025
  simp only [CollatzResearch.WordTrace]
  refine ⟨95924892296876072354659529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63949928197917381569773019 95924892296876072354659529)
  ·
    refine ⟨71943669222657054265994647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95924892296876072354659529 71943669222657054265994647)
    ·
      refine ⟨107915503833985581398991971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71943669222657054265994647 107915503833985581398991971)
      ·
        refine ⟨161873255750978372098487957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107915503833985581398991971 161873255750978372098487957)
        ·
          refine ⟨7587808863327111192116623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161873255750978372098487957 7587808863327111192116623)
          ·
            refine ⟨11381713294990666788174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587808863327111192116623 11381713294990666788174935)
            ·
              refine ⟨17072569942486000182262403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11381713294990666788174935 17072569942486000182262403)
              ·
                refine ⟨25608854913729000273393605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17072569942486000182262403 25608854913729000273393605)
                ·
                  refine ⟨4801660296324187551261301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25608854913729000273393605 4801660296324187551261301)
                  ·
                    refine ⟨450155652780392582930747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4801660296324187551261301 450155652780392582930747)
                    ·
                      rfl

theorem cell23_2630025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_2630025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630025 prefixEnd_2630025 := by exact prefixLift 2630025
  have htrace : WordTrace (prefixWord ++ tailWord_2630025) baseStart_2630025 baseEnd_2630025 := by
    simpa [prefixWord, tailWord_2630025, baseEnd_2630025] using wordTrace_append hprefix tailTrace_2630025
  have hstable : (prefixWord ++ tailWord_2630025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630025).length < 2 ^ (prefixWord ++ tailWord_2630025).sum := by decide
  have hdescent : baseEnd_2630025 < baseStart_2630025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630095 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_2630095 : Nat := 118140960795 + 2630095 * 2 ^ 59
def prefixEnd_2630095 : Nat := 4983230072969 + 3 ^ 40 * 2630095 * 2
def baseEnd_2630095 : Nat := 1350502901986992474916919

theorem tailTrace_2630095 : CollatzResearch.WordTrace tailWord_2630095 prefixEnd_2630095 1350502901986992474916919 := by
  unfold tailWord_2630095
  simp only [CollatzResearch.WordTrace]
  refine ⟨95927445406622474309707739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63951630271081649539805159 95927445406622474309707739)
  ·
    refine ⟨143891168109933711464561609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95927445406622474309707739 143891168109933711464561609)
    ·
      refine ⟨107918376082450283598421207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143891168109933711464561609 107918376082450283598421207)
      ·
        refine ⟨161877564123675425397631811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107918376082450283598421207 161877564123675425397631811)
        ·
          refine ⟨242816346185513138096447717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161877564123675425397631811 242816346185513138096447717)
          ·
            refine ⟨45528064909783713393083947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 242816346185513138096447717 45528064909783713393083947)
            ·
              refine ⟨68292097364675570089625921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45528064909783713393083947 68292097364675570089625921)
              ·
                refine ⟨51219073023506677567219441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68292097364675570089625921 51219073023506677567219441)
                ·
                  refine ⟨38414304767630008175414581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51219073023506677567219441 38414304767630008175414581)
                  ·
                    refine ⟨3601341071965313266445117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38414304767630008175414581 3601341071965313266445117)
                    ·
                      refine ⟨1350502901986992474916919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601341071965313266445117 1350502901986992474916919)
                      ·
                        rfl

theorem cell23_2630095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_2630095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630095 prefixEnd_2630095 := by exact prefixLift 2630095
  have htrace : WordTrace (prefixWord ++ tailWord_2630095) baseStart_2630095 baseEnd_2630095 := by
    simpa [prefixWord, tailWord_2630095, baseEnd_2630095] using wordTrace_append hprefix tailTrace_2630095
  have hstable : (prefixWord ++ tailWord_2630095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630095).length < 2 ^ (prefixWord ++ tailWord_2630095).sum := by decide
  have hdescent : baseEnd_2630095 < baseStart_2630095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630236 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2630236 : Nat := 118140960795 + 2630236 * 2 ^ 59
def prefixEnd_2630236 : Nat := 4983230072969 + 3 ^ 40 * 2630236 * 2
def baseEnd_2630236 : Nat := 1350575302759276423253771

theorem tailTrace_2630236 : CollatzResearch.WordTrace tailWord_2630236 prefixEnd_2630236 1350575302759276423253771 := by
  unfold tailWord_2630236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47966294049555827695295281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63955058732741103593727041 47966294049555827695295281)
  ·
    refine ⟨35974720537166870771471461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47966294049555827695295281 35974720537166870771471461)
    ·
      refine ⟨6745260100718788269650899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35974720537166870771471461 6745260100718788269650899)
      ·
        refine ⟨10117890151078182404476349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745260100718788269650899 10117890151078182404476349)
        ·
          refine ⟨3794208806654318401678631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10117890151078182404476349 3794208806654318401678631)
          ·
            refine ⟨5691313209981477602517947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794208806654318401678631 5691313209981477602517947)
            ·
              refine ⟨8536969814972216403776921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691313209981477602517947 8536969814972216403776921)
              ·
                refine ⟨6402727361229162302832691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536969814972216403776921 6402727361229162302832691)
                ·
                  refine ⟨9604091041843743454249037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402727361229162302832691 9604091041843743454249037)
                  ·
                    refine ⟨3601534140691403795343389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9604091041843743454249037 3601534140691403795343389)
                    ·
                      refine ⟨1350575302759276423253771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601534140691403795343389 1350575302759276423253771)
                      ·
                        rfl

theorem cell23_2630236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2630236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630236 prefixEnd_2630236 := by exact prefixLift 2630236
  have htrace : WordTrace (prefixWord ++ tailWord_2630236) baseStart_2630236 baseEnd_2630236 := by
    simpa [prefixWord, tailWord_2630236, baseEnd_2630236] using wordTrace_append hprefix tailTrace_2630236
  have hstable : (prefixWord ++ tailWord_2630236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630236).length < 2 ^ (prefixWord ++ tailWord_2630236).sum := by decide
  have hdescent : baseEnd_2630236 < baseStart_2630236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630253 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2630253 : Nat := 118140960795 + 2630253 * 2 ^ 59
def prefixEnd_2630253 : Nat := 4983230072969 + 3 ^ 40 * 2630253 * 2
def baseEnd_2630253 : Nat := 1350584031930402856741193

theorem tailTrace_2630253 : CollatzResearch.WordTrace tailWord_2630253 prefixEnd_2630253 1350584031930402856741193 := by
  unfold tailWord_2630253
  simp only [CollatzResearch.WordTrace]
  refine ⟨95933208140050067293959413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63955472093366711529306275 95933208140050067293959413)
  ·
    refine ⟨8993738263129693808808695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95933208140050067293959413 8993738263129693808808695)
    ·
      refine ⟨13490607394694540713213043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8993738263129693808808695 13490607394694540713213043)
      ·
        refine ⟨20235911092041811069819565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13490607394694540713213043 20235911092041811069819565)
        ·
          refine ⟨7588466659515679151182337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20235911092041811069819565 7588466659515679151182337)
          ·
            refine ⟨5691349994636759363386753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7588466659515679151182337 5691349994636759363386753)
            ·
              refine ⟨4268512495977569522540065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691349994636759363386753 4268512495977569522540065)
              ·
                refine ⟨3201384371983177141905049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268512495977569522540065 3201384371983177141905049)
                ·
                  refine ⟨2401038278987382856428787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201384371983177141905049 2401038278987382856428787)
                  ·
                    refine ⟨3601557418481074284643181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2401038278987382856428787 3601557418481074284643181)
                    ·
                      refine ⟨1350584031930402856741193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3601557418481074284643181 1350584031930402856741193)
                      ·
                        rfl

theorem cell23_2630253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2630253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630253 prefixEnd_2630253 := by exact prefixLift 2630253
  have htrace : WordTrace (prefixWord ++ tailWord_2630253) baseStart_2630253 baseEnd_2630253 := by
    simpa [prefixWord, tailWord_2630253, baseEnd_2630253] using wordTrace_append hprefix tailTrace_2630253
  have hstable : (prefixWord ++ tailWord_2630253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630253).length < 2 ^ (prefixWord ++ tailWord_2630253).sum := by decide
  have hdescent : baseEnd_2630253 < baseStart_2630253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630269 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2630269 : Nat := 118140960795 + 2630269 * 2 ^ 59
def prefixEnd_2630269 : Nat := 4983230072969 + 3 ^ 40 * 2630269 * 2
def baseEnd_2630269 : Nat := 450197415873624931380373

theorem tailTrace_2630269 : CollatzResearch.WordTrace tailWord_2630269 prefixEnd_2630269 450197415873624931380373 := by
  unfold tailWord_2630269
  simp only [CollatzResearch.WordTrace]
  refine ⟨95933791707992102026541861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63955861138661401351027907 95933791707992102026541861)
  ·
    refine ⟨17987585945248519129976599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95933791707992102026541861 17987585945248519129976599)
    ·
      refine ⟨26981378917872778694964899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17987585945248519129976599 26981378917872778694964899)
      ·
        refine ⟨40472068376809168042447349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26981378917872778694964899 40472068376809168042447349)
        ·
          refine ⟨3794256410325859503979439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40472068376809168042447349 3794256410325859503979439)
          ·
            refine ⟨5691384615488789255969159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794256410325859503979439 5691384615488789255969159)
            ·
              refine ⟨8537076923233183883953739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691384615488789255969159 8537076923233183883953739)
              ·
                refine ⟨12805615384849775825930609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8537076923233183883953739 12805615384849775825930609)
                ·
                  refine ⟨9604211538637331869447957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12805615384849775825930609 9604211538637331869447957)
                  ·
                    refine ⟨450197415873624931380373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9604211538637331869447957 450197415873624931380373)
                    ·
                      rfl

theorem cell23_2630269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2630269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630269 prefixEnd_2630269 := by exact prefixLift 2630269
  have htrace : WordTrace (prefixWord ++ tailWord_2630269) baseStart_2630269 baseEnd_2630269 := by
    simpa [prefixWord, tailWord_2630269, baseEnd_2630269] using wordTrace_append hprefix tailTrace_2630269
  have hstable : (prefixWord ++ tailWord_2630269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630269).length < 2 ^ (prefixWord ++ tailWord_2630269).sum := by decide
  have hdescent : baseEnd_2630269 < baseStart_2630269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630272 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_2630272 : Nat := 118140960795 + 2630272 * 2 ^ 59
def prefixEnd_2630272 : Nat := 4983230072969 + 3 ^ 40 * 2630272 * 2
def baseEnd_2630272 : Nat := 1350593788062838282403605

theorem tailTrace_2630272 : CollatzResearch.WordTrace tailWord_2630272 prefixEnd_2630272 1350593788062838282403605 := by
  unfold tailWord_2630272
  simp only [CollatzResearch.WordTrace]
  refine ⟨47966950563490616769450535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63955934084654155692600713 47966950563490616769450535)
  ·
    refine ⟨71950425845235925154175803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47966950563490616769450535 71950425845235925154175803)
    ·
      refine ⟨107925638767853887731263705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71950425845235925154175803 107925638767853887731263705)
      ·
        refine ⟨80944229075890415798447779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107925638767853887731263705 80944229075890415798447779)
        ·
          refine ⟨121416343613835623697671669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80944229075890415798447779 121416343613835623697671669)
          ·
            refine ⟨11382782213797089721656719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121416343613835623697671669 11382782213797089721656719)
            ·
              refine ⟨17074173320695634582485079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11382782213797089721656719 17074173320695634582485079)
              ·
                refine ⟨25611259981043451873727619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17074173320695634582485079 25611259981043451873727619)
                ·
                  refine ⟨38416889971565177810591429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25611259981043451873727619 38416889971565177810591429)
                  ·
                    refine ⟨7203166869668470839485893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38416889971565177810591429 7203166869668470839485893)
                    ·
                      refine ⟨1350593788062838282403605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7203166869668470839485893 1350593788062838282403605)
                      ·
                        rfl

theorem cell23_2630272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_2630272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630272 prefixEnd_2630272 := by exact prefixLift 2630272
  have htrace : WordTrace (prefixWord ++ tailWord_2630272) baseStart_2630272 baseEnd_2630272 := by
    simpa [prefixWord, tailWord_2630272, baseEnd_2630272] using wordTrace_append hprefix tailTrace_2630272
  have hstable : (prefixWord ++ tailWord_2630272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630272).length < 2 ^ (prefixWord ++ tailWord_2630272).sum := by decide
  have hdescent : baseEnd_2630272 < baseStart_2630272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630276 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2630276 : Nat := 118140960795 + 2630276 * 2 ^ 59
def prefixEnd_2630276 : Nat := 4983230072969 + 3 ^ 40 * 2630276 * 2
def baseEnd_2630276 : Nat := 1350595841985456266753587

theorem tailTrace_2630276 : CollatzResearch.WordTrace tailWord_2630276 prefixEnd_2630276 1350595841985456266753587 := by
  unfold tailWord_2630276
  simp only [CollatzResearch.WordTrace]
  refine ⟨47967023509483371111023341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63956031345977828148031121 47967023509483371111023341)
  ·
    refine ⟨17987633816056264166633753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47967023509483371111023341 17987633816056264166633753)
    ·
      refine ⟨13490725362042198124975315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17987633816056264166633753 13490725362042198124975315)
      ·
        refine ⟨20236088043063297187462973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13490725362042198124975315 20236088043063297187462973)
        ·
          refine ⟨7588533016148736445298615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20236088043063297187462973 7588533016148736445298615)
          ·
            refine ⟨11382799524223104667947923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7588533016148736445298615 11382799524223104667947923)
            ·
              refine ⟨17074199286334657001921885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11382799524223104667947923 17074199286334657001921885)
              ·
                refine ⟨6402824732375496375720707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17074199286334657001921885 6402824732375496375720707)
                ·
                  refine ⟨9604237098563244563581061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6402824732375496375720707 9604237098563244563581061)
                  ·
                    refine ⟨1800794455980608355671449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9604237098563244563581061 1800794455980608355671449)
                    ·
                      refine ⟨1350595841985456266753587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800794455980608355671449 1350595841985456266753587)
                      ·
                        rfl

theorem cell23_2630276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2630276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630276 prefixEnd_2630276 := by exact prefixLift 2630276
  have htrace : WordTrace (prefixWord ++ tailWord_2630276) baseStart_2630276 baseEnd_2630276 := by
    simpa [prefixWord, tailWord_2630276, baseEnd_2630276] using wordTrace_append hprefix tailTrace_2630276
  have hstable : (prefixWord ++ tailWord_2630276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630276).length < 2 ^ (prefixWord ++ tailWord_2630276).sum := by decide
  have hdescent : baseEnd_2630276 < baseStart_2630276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630322 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2630322 : Nat := 118140960795 + 2630322 * 2 ^ 59
def prefixEnd_2630322 : Nat := 4983230072969 + 3 ^ 40 * 2630322 * 2
def baseEnd_2630322 : Nat := 1350619462095563086778375

theorem tailTrace_2630322 : CollatzResearch.WordTrace tailWord_2630322 prefixEnd_2630322 1350619462095563086778375 := by
  unfold tailWord_2630322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23983931194200023019555305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63957149851200061385480813 23983931194200023019555305)
  ·
    refine ⟨17987948395650017264666479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23983931194200023019555305 17987948395650017264666479)
    ·
      refine ⟨26981922593475025896999719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17987948395650017264666479 26981922593475025896999719)
      ·
        refine ⟨40472883890212538845499579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26981922593475025896999719 40472883890212538845499579)
        ·
          refine ⟨60709325835318808268249369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40472883890212538845499579 60709325835318808268249369)
          ·
            refine ⟨45531994376489106201187027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60709325835318808268249369 45531994376489106201187027)
            ·
              refine ⟨68297991564733659301780541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45531994376489106201187027 68297991564733659301780541)
              ·
                refine ⟨25611746836775122238167703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68297991564733659301780541 25611746836775122238167703)
                ·
                  refine ⟨38417620255162683357251555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25611746836775122238167703 38417620255162683357251555)
                  ·
                    refine ⟨57626430382744025035877333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38417620255162683357251555 57626430382744025035877333)
                    ·
                      refine ⟨1350619462095563086778375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57626430382744025035877333 1350619462095563086778375)
                      ·
                        rfl

theorem cell23_2630322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2630322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630322 prefixEnd_2630322 := by exact prefixLift 2630322
  have htrace : WordTrace (prefixWord ++ tailWord_2630322) baseStart_2630322 baseEnd_2630322 := by
    simpa [prefixWord, tailWord_2630322, baseEnd_2630322] using wordTrace_append hprefix tailTrace_2630322
  have hstable : (prefixWord ++ tailWord_2630322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630322).length < 2 ^ (prefixWord ++ tailWord_2630322).sum := by decide
  have hdescent : baseEnd_2630322 < baseStart_2630322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630456 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_2630456 : Nat := 118140960795 + 2630456 * 2 ^ 59
def prefixEnd_2630456 : Nat := 4983230072969 + 3 ^ 40 * 2630456 * 2
def baseEnd_2630456 : Nat := 1350688268503265562502759

theorem tailTrace_2630456 : CollatzResearch.WordTrace tailWord_2630456 prefixEnd_2630456 1350688268503265562502759 := by
  unfold tailWord_2630456
  simp only [CollatzResearch.WordTrace]
  refine ⟨47970306079157316481799611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63960408105543088642399481 47970306079157316481799611)
  ·
    refine ⟨71955459118735974722699417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47970306079157316481799611 71955459118735974722699417)
    ·
      refine ⟨53966594339051981042024563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71955459118735974722699417 53966594339051981042024563)
      ·
        refine ⟨80949891508577971563036845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53966594339051981042024563 80949891508577971563036845)
        ·
          refine ⟨30356209315716739336138817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80949891508577971563036845 30356209315716739336138817)
          ·
            refine ⟨22767156986787554502104113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30356209315716739336138817 22767156986787554502104113)
            ·
              refine ⟨17075367740090665876578085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22767156986787554502104113 17075367740090665876578085)
              ·
                refine ⟨3201631451266999851858391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17075367740090665876578085 3201631451266999851858391)
                ·
                  refine ⟨4802447176900499777787587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201631451266999851858391 4802447176900499777787587)
                  ·
                    refine ⟨7203670765350749666681381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4802447176900499777787587 7203670765350749666681381)
                    ·
                      refine ⟨1350688268503265562502759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7203670765350749666681381 1350688268503265562502759)
                      ·
                        rfl

theorem cell23_2630456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_2630456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630456 prefixEnd_2630456 := by exact prefixLift 2630456
  have htrace : WordTrace (prefixWord ++ tailWord_2630456) baseStart_2630456 baseEnd_2630456 := by
    simpa [prefixWord, tailWord_2630456, baseEnd_2630456] using wordTrace_append hprefix tailTrace_2630456
  have hstable : (prefixWord ++ tailWord_2630456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630456).length < 2 ^ (prefixWord ++ tailWord_2630456).sum := by decide
  have hdescent : baseEnd_2630456 < baseStart_2630456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630469 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_2630469 : Nat := 118140960795 + 2630469 * 2 ^ 59
def prefixEnd_2630469 : Nat := 4983230072969 + 3 ^ 40 * 2630469 * 2
def baseEnd_2630469 : Nat := 1350694943751774011640199

theorem tailTrace_2630469 : CollatzResearch.WordTrace tailWord_2630469 prefixEnd_2630469 1350694943751774011640199 := by
  unfold tailWord_2630469
  simp only [CollatzResearch.WordTrace]
  refine ⟨95941086307267536183822461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63960724204845024122548307 95941086307267536183822461)
  ·
    refine ⟨35977907365225326068933423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95941086307267536183822461 35977907365225326068933423)
    ·
      refine ⟨53966861047837989103400135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35977907365225326068933423 53966861047837989103400135)
      ·
        refine ⟨80950291571756983655100203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53966861047837989103400135 80950291571756983655100203)
        ·
          refine ⟨121425437357635475482650305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80950291571756983655100203 121425437357635475482650305)
          ·
            refine ⟨91069078018226606611987729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121425437357635475482650305 91069078018226606611987729)
            ·
              refine ⟨68301808513669954958990797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91069078018226606611987729 68301808513669954958990797)
              ·
                refine ⟨25613178192626233109621549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68301808513669954958990797 25613178192626233109621549)
                ·
                  refine ⟨9604941822234837416108081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25613178192626233109621549 9604941822234837416108081)
                  ·
                    refine ⟨7203706366676128062081061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9604941822234837416108081 7203706366676128062081061)
                    ·
                      refine ⟨1350694943751774011640199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7203706366676128062081061 1350694943751774011640199)
                      ·
                        rfl

theorem cell23_2630469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_2630469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630469 prefixEnd_2630469 := by exact prefixLift 2630469
  have htrace : WordTrace (prefixWord ++ tailWord_2630469) baseStart_2630469 baseEnd_2630469 := by
    simpa [prefixWord, tailWord_2630469, baseEnd_2630469] using wordTrace_append hprefix tailTrace_2630469
  have hstable : (prefixWord ++ tailWord_2630469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630469).length < 2 ^ (prefixWord ++ tailWord_2630469).sum := by decide
  have hdescent : baseEnd_2630469 < baseStart_2630469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630473 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 1, 1, 4]
def baseStart_2630473 : Nat := 118140960795 + 2630473 * 2 ^ 59
def prefixEnd_2630473 : Nat := 4983230072969 + 3 ^ 40 * 2630473 * 2
def baseEnd_2630473 : Nat := 1350696997674391995990181

theorem tailTrace_2630473 : CollatzResearch.WordTrace tailWord_2630473 prefixEnd_2630473 1350696997674391995990181 := by
  unfold tailWord_2630473
  simp only [CollatzResearch.WordTrace]
  refine ⟨95941232199253044866968073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63960821466168696577978715 95941232199253044866968073)
  ·
    refine ⟨71955924149439783650226055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95941232199253044866968073 71955924149439783650226055)
    ·
      refine ⟨107933886224159675475339083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71955924149439783650226055 107933886224159675475339083)
      ·
        refine ⟨161900829336239513213008625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107933886224159675475339083 161900829336239513213008625)
        ·
          refine ⟨121425622002179634909756469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161900829336239513213008625 121425622002179634909756469)
          ·
            refine ⟨11383652062704340772789669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121425622002179634909756469 11383652062704340772789669)
            ·
              refine ⟨2134434761757063894898063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11383652062704340772789669 2134434761757063894898063)
              ·
                refine ⟨3201652142635595842347095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134434761757063894898063 3201652142635595842347095)
                ·
                  refine ⟨4802478213953393763520643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201652142635595842347095 4802478213953393763520643)
                  ·
                    refine ⟨7203717320930090645280965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4802478213953393763520643 7203717320930090645280965)
                    ·
                      refine ⟨1350696997674391995990181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7203717320930090645280965 1350696997674391995990181)
                      ·
                        rfl

theorem cell23_2630473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 1, 4].length) (baseStart_2630473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630473 prefixEnd_2630473 := by exact prefixLift 2630473
  have htrace : WordTrace (prefixWord ++ tailWord_2630473) baseStart_2630473 baseEnd_2630473 := by
    simpa [prefixWord, tailWord_2630473, baseEnd_2630473] using wordTrace_append hprefix tailTrace_2630473
  have hstable : (prefixWord ++ tailWord_2630473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630473).length < 2 ^ (prefixWord ++ tailWord_2630473).sum := by decide
  have hdescent : baseEnd_2630473 < baseStart_2630473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630490 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_2630490 : Nat := 118140960795 + 2630490 * 2 ^ 59
def prefixEnd_2630490 : Nat := 4983230072969 + 3 ^ 40 * 2630490 * 2
def baseEnd_2630490 : Nat := 1350705726845518429477603

theorem tailTrace_2630490 : CollatzResearch.WordTrace tailWord_2630490 prefixEnd_2630490 1350705726845518429477603 := by
  unfold tailWord_2630490
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985463060047864192584231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63961234826794304513557949 23985463060047864192584231)
  ·
    refine ⟨35978194590071796288876347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23985463060047864192584231 35978194590071796288876347)
    ·
      refine ⟨53967291885107694433314521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35978194590071796288876347 53967291885107694433314521)
      ·
        refine ⟨40475468913830770824985891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53967291885107694433314521 40475468913830770824985891)
        ·
          refine ⟨60713203370746156237478837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40475468913830770824985891 60713203370746156237478837)
          ·
            refine ⟨5691862816007452147263641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60713203370746156237478837 5691862816007452147263641)
            ·
              refine ⟨4268897112005589110447731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691862816007452147263641 4268897112005589110447731)
              ·
                refine ⟨6403345668008383665671597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268897112005589110447731 6403345668008383665671597)
                ·
                  refine ⟨2401254625503143874626849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6403345668008383665671597 2401254625503143874626849)
                  ·
                    refine ⟨1800940969127357905970137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2401254625503143874626849 1800940969127357905970137)
                    ·
                      refine ⟨1350705726845518429477603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1800940969127357905970137 1350705726845518429477603)
                      ·
                        rfl

theorem cell23_2630490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_2630490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630490 prefixEnd_2630490 := by exact prefixLift 2630490
  have htrace : WordTrace (prefixWord ++ tailWord_2630490) baseStart_2630490 baseEnd_2630490 := by
    simpa [prefixWord, tailWord_2630490, baseEnd_2630490] using wordTrace_append hprefix tailTrace_2630490
  have hstable : (prefixWord ++ tailWord_2630490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630490).length < 2 ^ (prefixWord ++ tailWord_2630490).sum := by decide
  have hdescent : baseEnd_2630490 < baseStart_2630490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630500 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_2630500 : Nat := 118140960795 + 2630500 * 2 ^ 59
def prefixEnd_2630500 : Nat := 4983230072969 + 3 ^ 40 * 2630500 * 2
def baseEnd_2630500 : Nat := 450236953884021130117519

theorem tailTrace_2630500 : CollatzResearch.WordTrace tailWord_2630500 prefixEnd_2630500 450236953884021130117519 := by
  unfold tailWord_2630500
  simp only [CollatzResearch.WordTrace]
  refine ⟨47971108485077614239100477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63961477980103485652133969 47971108485077614239100477)
  ·
    refine ⟨17989165681904105339662679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47971108485077614239100477 17989165681904105339662679)
    ·
      refine ⟨26983748522856158009494019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17989165681904105339662679 26983748522856158009494019)
      ·
        refine ⟨40475622784284237014241029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26983748522856158009494019 40475622784284237014241029)
        ·
          refine ⟨7589179272053294440170193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40475622784284237014241029 7589179272053294440170193)
          ·
            refine ⟨5691884454039970830127645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7589179272053294440170193 5691884454039970830127645)
            ·
              refine ⟨2134456670264989061297867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5691884454039970830127645 2134456670264989061297867)
              ·
                refine ⟨3201685005397483591946801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134456670264989061297867 3201685005397483591946801)
                ·
                  refine ⟨2401263754048112693960101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201685005397483591946801 2401263754048112693960101)
                  ·
                    refine ⟨450236953884021130117519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401263754048112693960101 450236953884021130117519)
                    ·
                      rfl

theorem cell23_2630500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_2630500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630500 prefixEnd_2630500 := by exact prefixLift 2630500
  have htrace : WordTrace (prefixWord ++ tailWord_2630500) baseStart_2630500 baseEnd_2630500 := by
    simpa [prefixWord, tailWord_2630500, baseEnd_2630500] using wordTrace_append hprefix tailTrace_2630500
  have hstable : (prefixWord ++ tailWord_2630500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630500).length < 2 ^ (prefixWord ++ tailWord_2630500).sum := by decide
  have hdescent : baseEnd_2630500 < baseStart_2630500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630503 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2630503 : Nat := 118140960795 + 2630503 * 2 ^ 59
def prefixEnd_2630503 : Nat := 4983230072969 + 3 ^ 40 * 2630503 * 2
def baseEnd_2630503 : Nat := 1350712402094026878615043

theorem tailTrace_2630503 : CollatzResearch.WordTrace tailWord_2630503 prefixEnd_2630503 1350712402094026878615043 := by
  unfold tailWord_2630503
  simp only [CollatzResearch.WordTrace]
  refine ⟨95942326389144359990560163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63961550926096239993706775 95942326389144359990560163)
  ·
    refine ⟨143913489583716539985840245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95942326389144359990560163 143913489583716539985840245)
    ·
      refine ⟨13491889648473425623672523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143913489583716539985840245 13491889648473425623672523)
      ·
        refine ⟨20237834472710138435508785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13491889648473425623672523 20237834472710138435508785)
        ·
          refine ⟨15178375854532603826631589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20237834472710138435508785 15178375854532603826631589)
          ·
            refine ⟨2845945472724863217493423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15178375854532603826631589 2845945472724863217493423)
            ·
              refine ⟨4268918209087294826240135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845945472724863217493423 4268918209087294826240135)
              ·
                refine ⟨6403377313630942239360203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268918209087294826240135 6403377313630942239360203)
                ·
                  refine ⟨9605065970446413359040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403377313630942239360203 9605065970446413359040305)
                  ·
                    refine ⟨7203799477834810019280229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9605065970446413359040305 7203799477834810019280229)
                    ·
                      refine ⟨1350712402094026878615043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7203799477834810019280229 1350712402094026878615043)
                      ·
                        rfl

theorem cell23_2630503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2630503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630503 prefixEnd_2630503 := by exact prefixLift 2630503
  have htrace : WordTrace (prefixWord ++ tailWord_2630503) baseStart_2630503 baseEnd_2630503 := by
    simpa [prefixWord, tailWord_2630503, baseEnd_2630503] using wordTrace_append hprefix tailTrace_2630503
  have hstable : (prefixWord ++ tailWord_2630503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630503).length < 2 ^ (prefixWord ++ tailWord_2630503).sum := by decide
  have hdescent : baseEnd_2630503 < baseStart_2630503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630530 : List Nat := [3, 4, 2, 2, 1, 2, 9]
def baseStart_2630530 : Nat := 118140960795 + 2630530 * 2 ^ 59
def prefixEnd_2630530 : Nat := 4983230072969 + 3 ^ 40 * 2630530 * 2
def baseEnd_2630530 : Nat := 16675632914465410777499

theorem tailTrace_2630530 : CollatzResearch.WordTrace tailWord_2630530 prefixEnd_2630530 16675632914465410777499 := by
  unfold tailWord_2630530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985827790011635900448261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63962207440031029067862029 23985827790011635900448261)
  ·
    refine ⟨4497342710627181731334049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23985827790011635900448261 4497342710627181731334049)
    ·
      refine ⟨3373007032970386298500537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4497342710627181731334049 3373007032970386298500537)
      ·
        refine ⟨2529755274727789723875403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3373007032970386298500537 2529755274727789723875403)
        ·
          refine ⟨3794632912091684585813105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529755274727789723875403 3794632912091684585813105)
          ·
            refine ⟨2845974684068763439359829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794632912091684585813105 2845974684068763439359829)
            ·
              refine ⟨16675632914465410777499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2845974684068763439359829 16675632914465410777499)
              ·
                rfl

theorem cell23_2630530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 9].length) (baseStart_2630530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630530 prefixEnd_2630530 := by exact prefixLift 2630530
  have htrace : WordTrace (prefixWord ++ tailWord_2630530) baseStart_2630530 baseEnd_2630530 := by
    simpa [prefixWord, tailWord_2630530, baseEnd_2630530] using wordTrace_append hprefix tailTrace_2630530
  have hstable : (prefixWord ++ tailWord_2630530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630530).length < 2 ^ (prefixWord ++ tailWord_2630530).sum := by decide
  have hdescent : baseEnd_2630530 < baseStart_2630530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630539 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 6]
def baseStart_2630539 : Nat := 118140960795 + 2630539 * 2 ^ 59
def prefixEnd_2630539 : Nat := 4983230072969 + 3 ^ 40 * 2630539 * 2
def baseEnd_2630539 : Nat := 450243629132529579254959

theorem tailTrace_2630539 : CollatzResearch.WordTrace tailWord_2630539 prefixEnd_2630539 450243629132529579254959 := by
  unfold tailWord_2630539
  simp only [CollatzResearch.WordTrace]
  refine ⟨95943639417013938138870671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63962426278009292092580447 95943639417013938138870671)
  ·
    refine ⟨143915459125520907208306007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95943639417013938138870671 143915459125520907208306007)
    ·
      refine ⟨215873188688281360812459011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143915459125520907208306007 215873188688281360812459011)
      ·
        refine ⟨323809783032422041218688517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215873188688281360812459011 323809783032422041218688517)
        ·
          refine ⟨60714334318579132728504097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323809783032422041218688517 60714334318579132728504097)
          ·
            refine ⟨45535750738934349546378073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60714334318579132728504097 45535750738934349546378073)
            ·
              refine ⟨34151813054200762159783555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45535750738934349546378073 34151813054200762159783555)
              ·
                refine ⟨51227719581301143239675333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34151813054200762159783555 51227719581301143239675333)
                ·
                  refine ⟨9605197421493964357439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51227719581301143239675333 9605197421493964357439125)
                  ·
                    refine ⟨450243629132529579254959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9605197421493964357439125 450243629132529579254959)
                    ·
                      rfl

theorem cell23_2630539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_2630539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630539 prefixEnd_2630539 := by exact prefixLift 2630539
  have htrace : WordTrace (prefixWord ++ tailWord_2630539) baseStart_2630539 baseEnd_2630539 := by
    simpa [prefixWord, tailWord_2630539, baseEnd_2630539] using wordTrace_append hprefix tailTrace_2630539
  have hstable : (prefixWord ++ tailWord_2630539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630539).length < 2 ^ (prefixWord ++ tailWord_2630539).sum := by decide
  have hdescent : baseEnd_2630539 < baseStart_2630539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630569 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 9]
def baseStart_2630569 : Nat := 118140960795 + 2630569 * 2 ^ 59
def prefixEnd_2630569 : Nat := 4983230072969 + 3 ^ 40 * 2630569 * 2
def baseEnd_2630569 : Nat := 150082921313024846709971

theorem tailTrace_2630569 : CollatzResearch.WordTrace tailWord_2630569 prefixEnd_2630569 150082921313024846709971 := by
  unfold tailWord_2630569
  simp only [CollatzResearch.WordTrace]
  refine ⟨95944733606905253262462761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63963155737936835508308507 95944733606905253262462761)
  ·
    refine ⟨71958550205178939946847071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95944733606905253262462761 71958550205178939946847071)
    ·
      refine ⟨107937825307768409920270607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71958550205178939946847071 107937825307768409920270607)
      ·
        refine ⟨161906737961652614880405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107937825307768409920270607 161906737961652614880405911)
        ·
          refine ⟨242860106942478922320608867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161906737961652614880405911 242860106942478922320608867)
          ·
            refine ⟨364290160413718383480913301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242860106942478922320608867 364290160413718383480913301)
            ·
              refine ⟨17076101269393049225667811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 364290160413718383480913301 17076101269393049225667811)
              ·
                refine ⟨25614151904089573838501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17076101269393049225667811 25614151904089573838501717)
                ·
                  refine ⟨150082921313024846709971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25614151904089573838501717 150082921313024846709971)
                  ·
                    rfl

theorem cell23_2630569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_2630569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630569 prefixEnd_2630569 := by exact prefixLift 2630569
  have htrace : WordTrace (prefixWord ++ tailWord_2630569) baseStart_2630569 baseEnd_2630569 := by
    simpa [prefixWord, tailWord_2630569, baseEnd_2630569] using wordTrace_append hprefix tailTrace_2630569
  have hstable : (prefixWord ++ tailWord_2630569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630569).length < 2 ^ (prefixWord ++ tailWord_2630569).sum := by decide
  have hdescent : baseEnd_2630569 < baseStart_2630569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_2630579 : Nat := 118140960795 + 2630579 * 2 ^ 59
def prefixEnd_2630579 : Nat := 4983230072969 + 3 ^ 40 * 2630579 * 2
def baseEnd_2630579 : Nat := 1350751426623768581264693

theorem tailTrace_2630579 : CollatzResearch.WordTrace tailWord_2630579 prefixEnd_2630579 1350751426623768581264693 := by
  unfold tailWord_2630579
  simp only [CollatzResearch.WordTrace]
  refine ⟨95945098336869024970326791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63963398891246016646884527 95945098336869024970326791)
  ·
    refine ⟨143917647505303537455490187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95945098336869024970326791 143917647505303537455490187)
    ·
      refine ⟨215876471257955306183235281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143917647505303537455490187 215876471257955306183235281)
      ·
        refine ⟨161907353443466479637426461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215876471257955306183235281 161907353443466479637426461)
        ·
          refine ⟨60715257541299929864034923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161907353443466479637426461 60715257541299929864034923)
          ·
            refine ⟨91072886311949894796052385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60715257541299929864034923 91072886311949894796052385)
            ·
              refine ⟨68304664733962421097039289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91072886311949894796052385 68304664733962421097039289)
              ·
                refine ⟨51228498550471815822779467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68304664733962421097039289 51228498550471815822779467)
                ·
                  refine ⟨76842747825707723734169201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51228498550471815822779467 76842747825707723734169201)
                  ·
                    refine ⟨57632060869280792800626901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76842747825707723734169201 57632060869280792800626901)
                    ·
                      refine ⟨1350751426623768581264693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57632060869280792800626901 1350751426623768581264693)
                      ·
                        rfl

theorem cell23_2630579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_2630579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630579 prefixEnd_2630579 := by exact prefixLift 2630579
  have htrace : WordTrace (prefixWord ++ tailWord_2630579) baseStart_2630579 baseEnd_2630579 := by
    simpa [prefixWord, tailWord_2630579, baseEnd_2630579] using wordTrace_append hprefix tailTrace_2630579
  have hstable : (prefixWord ++ tailWord_2630579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630579).length < 2 ^ (prefixWord ++ tailWord_2630579).sum := by decide
  have hdescent : baseEnd_2630579 < baseStart_2630579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630603 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 5]
def baseStart_2630603 : Nat := 118140960795 + 2630603 * 2 ^ 59
def prefixEnd_2630603 : Nat := 4983230072969 + 3 ^ 40 * 2630603 * 2
def baseEnd_2630603 : Nat := 150084861128830720818287

theorem tailTrace_2630603 : CollatzResearch.WordTrace tailWord_2630603 prefixEnd_2630603 150084861128830720818287 := by
  unfold tailWord_2630603
  simp only [CollatzResearch.WordTrace]
  refine ⟨95945973688782077069200463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63963982459188051379466975 95945973688782077069200463)
  ·
    refine ⟨143918960533173115603800695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95945973688782077069200463 143918960533173115603800695)
    ·
      refine ⟨215878440799759673405701043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143918960533173115603800695 215878440799759673405701043)
      ·
        refine ⟨323817661199639510108551565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215878440799759673405701043 323817661199639510108551565)
        ·
          refine ⟨121431622949864816290706837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323817661199639510108551565 121431622949864816290706837)
          ·
            refine ⟨5692107325774913263626883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121431622949864816290706837 5692107325774913263626883)
            ·
              refine ⟨8538160988662369895440325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692107325774913263626883 8538160988662369895440325)
              ·
                refine ⟨1600905185374194355395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8538160988662369895440325 1600905185374194355395061)
                ·
                  refine ⟨150084861128830720818287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600905185374194355395061 150084861128830720818287)
                  ·
                    rfl

theorem cell23_2630603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 5].length) (baseStart_2630603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630603 prefixEnd_2630603 := by exact prefixLift 2630603
  have htrace : WordTrace (prefixWord ++ tailWord_2630603) baseStart_2630603 baseEnd_2630603 := by
    simpa [prefixWord, tailWord_2630603, baseEnd_2630603] using wordTrace_append hprefix tailTrace_2630603
  have hstable : (prefixWord ++ tailWord_2630603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630603).length < 2 ^ (prefixWord ++ tailWord_2630603).sum := by decide
  have hdescent : baseEnd_2630603 < baseStart_2630603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630614 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2630614 : Nat := 118140960795 + 2630614 * 2 ^ 59
def prefixEnd_2630614 : Nat := 4983230072969 + 3 ^ 40 * 2630614 * 2
def baseEnd_2630614 : Nat := 1350769398446675944327033

theorem tailTrace_2630614 : CollatzResearch.WordTrace tailWord_2630614 prefixEnd_2630614 1350769398446675944327033 := by
  unfold tailWord_2630614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996648430733889121740681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63964249927828150631900597 5996648430733889121740681)
  ·
    refine ⟨4497486323050416841305511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5996648430733889121740681 4497486323050416841305511)
    ·
      refine ⟨6746229484575625261958267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497486323050416841305511 6746229484575625261958267)
      ·
        refine ⟨10119344226863437892937401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746229484575625261958267 10119344226863437892937401)
        ·
          refine ⟨7589508170147578419703051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119344226863437892937401 7589508170147578419703051)
          ·
            refine ⟨11384262255221367629554577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589508170147578419703051 11384262255221367629554577)
            ·
              refine ⟨8538196691416025722165933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384262255221367629554577 8538196691416025722165933)
              ·
                refine ⟨3201823759281009645812225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8538196691416025722165933 3201823759281009645812225)
                ·
                  refine ⟨2401367819460757234359169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201823759281009645812225 2401367819460757234359169)
                  ·
                    refine ⟨1801025864595567925769377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2401367819460757234359169 1801025864595567925769377)
                    ·
                      refine ⟨1350769398446675944327033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801025864595567925769377 1350769398446675944327033)
                      ·
                        rfl

theorem cell23_2630614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2630614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630614 prefixEnd_2630614 := by exact prefixLift 2630614
  have htrace : WordTrace (prefixWord ++ tailWord_2630614) baseStart_2630614 baseEnd_2630614 := by
    simpa [prefixWord, tailWord_2630614, baseEnd_2630614] using wordTrace_append hprefix tailTrace_2630614
  have hstable : (prefixWord ++ tailWord_2630614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630614).length < 2 ^ (prefixWord ++ tailWord_2630614).sum := by decide
  have hdescent : baseEnd_2630614 < baseStart_2630614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630670 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2630670 : Nat := 118140960795 + 2630670 * 2 ^ 59
def prefixEnd_2630670 : Nat := 4983230072969 + 3 ^ 40 * 2630670 * 2
def baseEnd_2630670 : Nat := 1350798153363327725226775

theorem tailTrace_2630670 : CollatzResearch.WordTrace tailWord_2630670 prefixEnd_2630670 1350798153363327725226775 := by
  unfold tailWord_2630670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993552172442418438986183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63965611586359565007926309 11993552172442418438986183)
  ·
    refine ⟨17990328258663627658479275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993552172442418438986183 17990328258663627658479275)
    ·
      refine ⟨26985492387995441487718913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990328258663627658479275 26985492387995441487718913)
      ·
        refine ⟨20239119290996581115789185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26985492387995441487718913 20239119290996581115789185)
        ·
          refine ⟨15179339468247435836841889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20239119290996581115789185 15179339468247435836841889)
          ·
            refine ⟨11384504601185576877631417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15179339468247435836841889 11384504601185576877631417)
            ·
              refine ⟨8538378450889182658223563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384504601185576877631417 8538378450889182658223563)
              ·
                refine ⟨12807567676333773987335345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538378450889182658223563 12807567676333773987335345)
                ·
                  refine ⟨9605675757250330490501509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12807567676333773987335345 9605675757250330490501509)
                  ·
                    refine ⟨1801064204484436966969033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9605675757250330490501509 1801064204484436966969033)
                    ·
                      refine ⟨1350798153363327725226775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801064204484436966969033 1350798153363327725226775)
                      ·
                        rfl

theorem cell23_2630670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2630670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630670 prefixEnd_2630670 := by exact prefixLift 2630670
  have htrace : WordTrace (prefixWord ++ tailWord_2630670) baseStart_2630670 baseEnd_2630670 := by
    simpa [prefixWord, tailWord_2630670, baseEnd_2630670] using wordTrace_append hprefix tailTrace_2630670
  have hstable : (prefixWord ++ tailWord_2630670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630670).length < 2 ^ (prefixWord ++ tailWord_2630670).sum := by decide
  have hdescent : baseEnd_2630670 < baseStart_2630670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630736 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_2630736 : Nat := 118140960795 + 2630736 * 2 ^ 59
def prefixEnd_2630736 : Nat := 4983230072969 + 3 ^ 40 * 2630736 * 2
def baseEnd_2630736 : Nat := 450277347695508155667157

theorem tailTrace_2630736 : CollatzResearch.WordTrace tailWord_2630736 prefixEnd_2630736 450277347695508155667157 := by
  unfold tailWord_2630736
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975412298650120391896031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63967216398200160522528041 47975412298650120391896031)
  ·
    refine ⟨71963118447975180587844047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47975412298650120391896031 71963118447975180587844047)
    ·
      refine ⟨107944677671962770881766071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71963118447975180587844047 107944677671962770881766071)
      ·
        refine ⟨161917016507944156322649107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107944677671962770881766071 161917016507944156322649107)
        ·
          refine ⟨242875524761916234483973661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161917016507944156322649107 242875524761916234483973661)
          ·
            refine ⟨91078321785718587931490123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242875524761916234483973661 91078321785718587931490123)
            ·
              refine ⟨136617482678577881897235185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91078321785718587931490123 136617482678577881897235185)
              ·
                refine ⟨102463112008933411422926389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136617482678577881897235185 102463112008933411422926389)
                ·
                  refine ⟨9605916750837507320899349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102463112008933411422926389 9605916750837507320899349)
                  ·
                    refine ⟨450277347695508155667157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9605916750837507320899349 450277347695508155667157)
                    ·
                      rfl

theorem cell23_2630736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_2630736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630736 prefixEnd_2630736 := by exact prefixLift 2630736
  have htrace : WordTrace (prefixWord ++ tailWord_2630736) baseStart_2630736 baseEnd_2630736 := by
    simpa [prefixWord, tailWord_2630736, baseEnd_2630736] using wordTrace_append hprefix tailTrace_2630736
  have hstable : (prefixWord ++ tailWord_2630736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630736).length < 2 ^ (prefixWord ++ tailWord_2630736).sum := by decide
  have hdescent : baseEnd_2630736 < baseStart_2630736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630740 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_2630740 : Nat := 118140960795 + 2630740 * 2 ^ 59
def prefixEnd_2630740 : Nat := 4983230072969 + 3 ^ 40 * 2630740 * 2
def baseEnd_2630740 : Nat := 450278032336380817117151

theorem tailTrace_2630740 : CollatzResearch.WordTrace tailWord_2630740 prefixEnd_2630740 450278032336380817117151 := by
  unfold tailWord_2630740
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975485244642874733468837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63967313659523832977958449 47975485244642874733468837)
  ·
    refine ⟨8995403483370539012525407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47975485244642874733468837 8995403483370539012525407)
    ·
      refine ⟨13493105225055808518788111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8995403483370539012525407 13493105225055808518788111)
      ·
        refine ⟨20239657837583712778182167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493105225055808518788111 20239657837583712778182167)
        ·
          refine ⟨30359486756375569167273251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20239657837583712778182167 30359486756375569167273251)
          ·
            refine ⟨45539230134563353750909877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30359486756375569167273251 45539230134563353750909877)
            ·
              refine ⟨4269302825115314414147801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45539230134563353750909877 4269302825115314414147801)
              ·
                refine ⟨3201977118836485810610851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269302825115314414147801 3201977118836485810610851)
                ·
                  refine ⟨4802965678254728715916277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3201977118836485810610851 4802965678254728715916277)
                  ·
                    refine ⟨450278032336380817117151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4802965678254728715916277 450278032336380817117151)
                    ·
                      rfl

theorem cell23_2630740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_2630740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630740 prefixEnd_2630740 := by exact prefixLift 2630740
  have htrace : WordTrace (prefixWord ++ tailWord_2630740) baseStart_2630740 baseEnd_2630740 := by
    simpa [prefixWord, tailWord_2630740, baseEnd_2630740] using wordTrace_append hprefix tailTrace_2630740
  have hstable : (prefixWord ++ tailWord_2630740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630740).length < 2 ^ (prefixWord ++ tailWord_2630740).sum := by decide
  have hdescent : baseEnd_2630740 < baseStart_2630740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630753 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2630753 : Nat := 118140960795 + 2630753 * 2 ^ 59
def prefixEnd_2630753 : Nat := 4983230072969 + 3 ^ 40 * 2630753 * 2
def baseEnd_2630753 : Nat := 450280257419216966829631

theorem tailTrace_2630753 : CollatzResearch.WordTrace tailWord_2630753 prefixEnd_2630753 450280257419216966829631 := by
  unfold tailWord_2630753
  simp only [CollatzResearch.WordTrace]
  refine ⟨95951444638238652687160913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63967629758825768458107275 95951444638238652687160913)
  ·
    refine ⟨71963583478678989515370685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95951444638238652687160913 71963583478678989515370685)
    ·
      refine ⟨26986343804504621068264007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71963583478678989515370685 26986343804504621068264007)
      ·
        refine ⟨40479515706756931602396011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986343804504621068264007 40479515706756931602396011)
        ·
          refine ⟨60719273560135397403594017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40479515706756931602396011 60719273560135397403594017)
          ·
            refine ⟨45539455170101548052695513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60719273560135397403594017 45539455170101548052695513)
            ·
              refine ⟨34154591377576161039521635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45539455170101548052695513 34154591377576161039521635)
              ·
                refine ⟨51231887066364241559282453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34154591377576161039521635 51231887066364241559282453)
                ·
                  refine ⟨2401494706235823823091365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51231887066364241559282453 2401494706235823823091365)
                  ·
                    refine ⟨450280257419216966829631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401494706235823823091365 450280257419216966829631)
                    ·
                      rfl

theorem cell23_2630753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2630753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630753 prefixEnd_2630753 := by exact prefixLift 2630753
  have htrace : WordTrace (prefixWord ++ tailWord_2630753) baseStart_2630753 baseEnd_2630753 := by
    simpa [prefixWord, tailWord_2630753, baseEnd_2630753] using wordTrace_append hprefix tailTrace_2630753
  have hstable : (prefixWord ++ tailWord_2630753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630753).length < 2 ^ (prefixWord ++ tailWord_2630753).sum := by decide
  have hdescent : baseEnd_2630753 < baseStart_2630753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630814 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2630814 : Nat := 118140960795 + 2630814 * 2 ^ 59
def prefixEnd_2630814 : Nat := 4983230072969 + 3 ^ 40 * 2630814 * 2
def baseEnd_2630814 : Nat := 1350872094577575161826113

theorem tailTrace_2630814 : CollatzResearch.WordTrace tailWord_2630814 prefixEnd_2630814 1350872094577575161826113 := by
  unfold tailWord_2630814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994208686377207513141437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63969112994011773403420997 11994208686377207513141437)
  ·
    refine ⟨4497828257391452817428039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11994208686377207513141437 4497828257391452817428039)
    ·
      refine ⟨6746742386087179226142059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497828257391452817428039 6746742386087179226142059)
      ·
        refine ⟨10120113579130768839213089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746742386087179226142059 10120113579130768839213089)
        ·
          refine ⟨7590085184348076629409817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10120113579130768839213089 7590085184348076629409817)
          ·
            refine ⟨5692563888261057472057363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7590085184348076629409817 5692563888261057472057363)
            ·
              refine ⟨8538845832391586208086045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692563888261057472057363 8538845832391586208086045)
              ·
                refine ⟨3202067187146844828032267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8538845832391586208086045 3202067187146844828032267)
                ·
                  refine ⟨4803100780720267242048401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202067187146844828032267 4803100780720267242048401)
                  ·
                    refine ⟨3602325585540200431536301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803100780720267242048401 3602325585540200431536301)
                    ·
                      refine ⟨1350872094577575161826113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3602325585540200431536301 1350872094577575161826113)
                      ·
                        rfl

theorem cell23_2630814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2630814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630814 prefixEnd_2630814 := by exact prefixLift 2630814
  have htrace : WordTrace (prefixWord ++ tailWord_2630814) baseStart_2630814 baseEnd_2630814 := by
    simpa [prefixWord, tailWord_2630814, baseEnd_2630814] using wordTrace_append hprefix tailTrace_2630814
  have hstable : (prefixWord ++ tailWord_2630814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630814).length < 2 ^ (prefixWord ++ tailWord_2630814).sum := by decide
  have hdescent : baseEnd_2630814 < baseStart_2630814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630838 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2630838 : Nat := 118140960795 + 2630838 * 2 ^ 59
def prefixEnd_2630838 : Nat := 4983230072969 + 3 ^ 40 * 2630838 * 2
def baseEnd_2630838 : Nat := 450294806037761022642001

theorem tailTrace_2630838 : CollatzResearch.WordTrace tailWord_2630838 prefixEnd_2630838 450294806037761022642001 := by
  unfold tailWord_2630838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997159052683169512750323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63969696561953808136003445 5997159052683169512750323)
  ·
    refine ⟨8995738579024754269125485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997159052683169512750323 8995738579024754269125485)
    ·
      refine ⟨3373401967134282850922057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8995738579024754269125485 3373401967134282850922057)
      ·
        refine ⟨2530051475350712138191543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3373401967134282850922057 2530051475350712138191543)
        ·
          refine ⟨3795077213026068207287315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530051475350712138191543 3795077213026068207287315)
          ·
            refine ⟨5692615819539102310930973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795077213026068207287315 5692615819539102310930973)
            ·
              refine ⟨2134730932327163366599115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5692615819539102310930973 2134730932327163366599115)
              ·
                refine ⟨3202096398490745049898673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134730932327163366599115 3202096398490745049898673)
                ·
                  refine ⟨2401572298868058787424005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202096398490745049898673 2401572298868058787424005)
                  ·
                    refine ⟨450294806037761022642001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401572298868058787424005 450294806037761022642001)
                    ·
                      rfl

theorem cell23_2630838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2630838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630838 prefixEnd_2630838 := by exact prefixLift 2630838
  have htrace : WordTrace (prefixWord ++ tailWord_2630838) baseStart_2630838 baseEnd_2630838 := by
    simpa [prefixWord, tailWord_2630838, baseEnd_2630838] using wordTrace_append hprefix tailTrace_2630838
  have hstable : (prefixWord ++ tailWord_2630838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630838).length < 2 ^ (prefixWord ++ tailWord_2630838).sum := by decide
  have hdescent : baseEnd_2630838 < baseStart_2630838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630853 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_2630853 : Nat := 118140960795 + 2630853 * 2 ^ 59
def prefixEnd_2630853 : Nat := 4983230072969 + 3 ^ 40 * 2630853 * 2
def baseEnd_2630853 : Nat := 1350892120323100509238433

theorem tailTrace_2630853 : CollatzResearch.WordTrace tailWord_2630853 prefixEnd_2630853 1350892120323100509238433 := by
  unfold tailWord_2630853
  simp only [CollatzResearch.WordTrace]
  refine ⟨95955091937876369765801213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63970061291917579843867475 95955091937876369765801213)
  ·
    refine ⟨35983159476703638662175455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95955091937876369765801213 35983159476703638662175455)
    ·
      refine ⟨53974739215055457993263183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35983159476703638662175455 53974739215055457993263183)
      ·
        refine ⟨80962108822583186989894775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53974739215055457993263183 80962108822583186989894775)
        ·
          refine ⟨121443163233874780484842163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80962108822583186989894775 121443163233874780484842163)
          ·
            refine ⟨182164744850812170727263245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121443163233874780484842163 182164744850812170727263245)
            ·
              refine ⟨68311779319054564022723717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182164744850812170727263245 68311779319054564022723717)
              ·
                refine ⟨12808458622322730754260697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68311779319054564022723717 12808458622322730754260697)
                ·
                  refine ⟨9606343966742048065695523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12808458622322730754260697 9606343966742048065695523)
                  ·
                    refine ⟨14409515950113072098543285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9606343966742048065695523 14409515950113072098543285)
                    ·
                      refine ⟨1350892120323100509238433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14409515950113072098543285 1350892120323100509238433)
                      ·
                        rfl

theorem cell23_2630853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_2630853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630853 prefixEnd_2630853 := by exact prefixLift 2630853
  have htrace : WordTrace (prefixWord ++ tailWord_2630853) baseStart_2630853 baseEnd_2630853 := by
    simpa [prefixWord, tailWord_2630853, baseEnd_2630853] using wordTrace_append hprefix tailTrace_2630853
  have hstable : (prefixWord ++ tailWord_2630853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630853).length < 2 ^ (prefixWord ++ tailWord_2630853).sum := by decide
  have hdescent : baseEnd_2630853 < baseStart_2630853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630863 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_2630863 : Nat := 118140960795 + 2630863 * 2 ^ 59
def prefixEnd_2630863 : Nat := 4983230072969 + 3 ^ 40 * 2630863 * 2
def baseEnd_2630863 : Nat := 1350897255129645470113387

theorem tailTrace_2630863 : CollatzResearch.WordTrace tailWord_2630863 prefixEnd_2630863 1350897255129645470113387 := by
  unfold tailWord_2630863
  simp only [CollatzResearch.WordTrace]
  refine ⟨95955456667840141473665243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63970304445226760982443495 95955456667840141473665243)
  ·
    refine ⟨143933185001760212210497865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95955456667840141473665243 143933185001760212210497865)
    ·
      refine ⟨107949888751320159157873399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143933185001760212210497865 107949888751320159157873399)
      ·
        refine ⟨161924833126980238736810099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107949888751320159157873399 161924833126980238736810099)
        ·
          refine ⟨242887249690470358105215149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161924833126980238736810099 242887249690470358105215149)
          ·
            refine ⟨91082718633926384289455681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242887249690470358105215149 91082718633926384289455681)
            ·
              refine ⟨68312038975444788217091761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91082718633926384289455681 68312038975444788217091761)
              ·
                refine ⟨51234029231583591162818821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68312038975444788217091761 51234029231583591162818821)
                ·
                  refine ⟨9606380480921923343028529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51234029231583591162818821 9606380480921923343028529)
                  ·
                    refine ⟨7204785360691442507271397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9606380480921923343028529 7204785360691442507271397)
                    ·
                      refine ⟨1350897255129645470113387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7204785360691442507271397 1350897255129645470113387)
                      ·
                        rfl

theorem cell23_2630863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_2630863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630863 prefixEnd_2630863 := by exact prefixLift 2630863
  have htrace : WordTrace (prefixWord ++ tailWord_2630863) baseStart_2630863 baseEnd_2630863 := by
    simpa [prefixWord, tailWord_2630863, baseEnd_2630863] using wordTrace_append hprefix tailTrace_2630863
  have hstable : (prefixWord ++ tailWord_2630863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630863).length < 2 ^ (prefixWord ++ tailWord_2630863).sum := by decide
  have hdescent : baseEnd_2630863 < baseStart_2630863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630890 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_2630890 : Nat := 118140960795 + 2630890 * 2 ^ 59
def prefixEnd_2630890 : Nat := 4983230072969 + 3 ^ 40 * 2630890 * 2
def baseEnd_2630890 : Nat := 150101235456368540497307

theorem tailTrace_2630890 : CollatzResearch.WordTrace tailWord_2630890 prefixEnd_2630890 150101235456368540497307 := by
  unfold tailWord_2630890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23989110359685581271224531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63970960959161550056598749 23989110359685581271224531)
  ·
    refine ⟨35983665539528371906836797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23989110359685581271224531 35983665539528371906836797)
    ·
      refine ⟨13493874577323139465063799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35983665539528371906836797 13493874577323139465063799)
      ·
        refine ⟨20240811865984709197595699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493874577323139465063799 20240811865984709197595699)
        ·
          refine ⟨30361217798977063796393549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240811865984709197595699 30361217798977063796393549)
          ·
            refine ⟨11385456674616398923647581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30361217798977063796393549 11385456674616398923647581)
            ·
              refine ⟨4269546252981149596367843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11385456674616398923647581 4269546252981149596367843)
              ·
                refine ⟨6404319379471724394551765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269546252981149596367843 6404319379471724394551765)
                ·
                  refine ⟨150101235456368540497307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6404319379471724394551765 150101235456368540497307)
                  ·
                    rfl

theorem cell23_2630890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_2630890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630890 prefixEnd_2630890 := by exact prefixLift 2630890
  have htrace : WordTrace (prefixWord ++ tailWord_2630890) baseStart_2630890 baseEnd_2630890 := by
    simpa [prefixWord, tailWord_2630890, baseEnd_2630890] using wordTrace_append hprefix tailTrace_2630890
  have hstable : (prefixWord ++ tailWord_2630890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630890).length < 2 ^ (prefixWord ++ tailWord_2630890).sum := by decide
  have hdescent : baseEnd_2630890 < baseStart_2630890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630941 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 5]
def baseStart_2630941 : Nat := 118140960795 + 2630941 * 2 ^ 59
def prefixEnd_2630941 : Nat := 4983230072969 + 3 ^ 40 * 2630941 * 2
def baseEnd_2630941 : Nat := 150104145180077351659781

theorem tailTrace_2630941 : CollatzResearch.WordTrace tailWord_2630941 prefixEnd_2630941 150104145180077351659781 := by
  unfold tailWord_2630941
  simp only [CollatzResearch.WordTrace]
  refine ⟨95958301561557560795004677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63972201041038373863336451 95958301561557560795004677)
  ·
    refine ⟨17992181542792042649063377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95958301561557560795004677 17992181542792042649063377)
    ·
      refine ⟨13494136157094031986797533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17992181542792042649063377 13494136157094031986797533)
      ·
        refine ⟨5060301058910261995049075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13494136157094031986797533 5060301058910261995049075)
        ·
          refine ⟨7590451588365392992573613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5060301058910261995049075 7590451588365392992573613)
          ·
            refine ⟨2846419345637022372215105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7590451588365392992573613 2846419345637022372215105)
            ·
              refine ⟨2134814509227766779161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2846419345637022372215105 2134814509227766779161329)
              ·
                refine ⟨1601110881920825084370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134814509227766779161329 1601110881920825084370997)
                ·
                  refine ⟨150104145180077351659781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601110881920825084370997 150104145180077351659781)
                  ·
                    rfl

theorem cell23_2630941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_2630941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630941 prefixEnd_2630941 := by exact prefixLift 2630941
  have htrace : WordTrace (prefixWord ++ tailWord_2630941) baseStart_2630941 baseEnd_2630941 := by
    simpa [prefixWord, tailWord_2630941, baseEnd_2630941] using wordTrace_append hprefix tailTrace_2630941
  have hstable : (prefixWord ++ tailWord_2630941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630941).length < 2 ^ (prefixWord ++ tailWord_2630941).sum := by decide
  have hdescent : baseEnd_2630941 < baseStart_2630941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630960 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_2630960 : Nat := 118140960795 + 2630960 * 2 ^ 59
def prefixEnd_2630960 : Nat := 4983230072969 + 3 ^ 40 * 2630960 * 2
def baseEnd_2630960 : Nat := 1350947062753131590600441

theorem tailTrace_2630960 : CollatzResearch.WordTrace tailWord_2630960 prefixEnd_2630960 1350947062753131590600441 := by
  unfold tailWord_2630960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47979497274244363519973167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63972663032325818026630889 47979497274244363519973167)
  ·
    refine ⟨71969245911366545279959751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47979497274244363519973167 71969245911366545279959751)
    ·
      refine ⟨107953868867049817919939627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71969245911366545279959751 107953868867049817919939627)
      ·
        refine ⟨161930803300574726879909441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107953868867049817919939627 161930803300574726879909441)
        ·
          refine ⟨121448102475431045159932081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161930803300574726879909441 121448102475431045159932081)
          ·
            refine ⟨91086076856573283869949061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121448102475431045159932081 91086076856573283869949061)
            ·
              refine ⟨17078639410607490725615449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91086076856573283869949061 17078639410607490725615449)
              ·
                refine ⟨12808979557955618044211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17078639410607490725615449 12808979557955618044211587)
                ·
                  refine ⟨19213469336933427066317381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12808979557955618044211587 19213469336933427066317381)
                  ·
                    refine ⟨3602525500675017574934509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19213469336933427066317381 3602525500675017574934509)
                    ·
                      refine ⟨1350947062753131590600441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3602525500675017574934509 1350947062753131590600441)
                      ·
                        rfl

theorem cell23_2630960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_2630960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630960 prefixEnd_2630960 := by exact prefixLift 2630960
  have htrace : WordTrace (prefixWord ++ tailWord_2630960) baseStart_2630960 baseEnd_2630960 := by
    simpa [prefixWord, tailWord_2630960, baseEnd_2630960] using wordTrace_append hprefix tailTrace_2630960
  have hstable : (prefixWord ++ tailWord_2630960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630960).length < 2 ^ (prefixWord ++ tailWord_2630960).sum := by decide
  have hdescent : baseEnd_2630960 < baseStart_2630960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2630997 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 6]
def baseStart_2630997 : Nat := 118140960795 + 2630997 * 2 ^ 59
def prefixEnd_2630997 : Nat := 4983230072969 + 3 ^ 40 * 2630997 * 2
def baseEnd_2630997 : Nat := 150107340170816438426419

theorem tailTrace_2630997 : CollatzResearch.WordTrace tailWord_2630997 prefixEnd_2630997 150107340170816438426419 := by
  unfold tailWord_2630997
  simp only [CollatzResearch.WordTrace]
  refine ⟨95960344049354682359043245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63973562699569788239362163 95960344049354682359043245)
  ·
    refine ⟨35985129018508005884641217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95960344049354682359043245 35985129018508005884641217)
    ·
      refine ⟨26988846763881004413480913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35985129018508005884641217 26988846763881004413480913)
      ·
        refine ⟨20241635072910753310110685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26988846763881004413480913 20241635072910753310110685)
        ·
          refine ⟨7590613152341532491291507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20241635072910753310110685 7590613152341532491291507)
          ·
            refine ⟨11385919728512298736937261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7590613152341532491291507 11385919728512298736937261)
            ·
              refine ⟨4269719898192112026351473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11385919728512298736937261 4269719898192112026351473)
              ·
                refine ⟨3202289923644084019763605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269719898192112026351473 3202289923644084019763605)
                ·
                  refine ⟨150107340170816438426419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3202289923644084019763605 150107340170816438426419)
                  ·
                    rfl

theorem cell23_2630997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_2630997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2630997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2630997 prefixEnd_2630997 := by exact prefixLift 2630997
  have htrace : WordTrace (prefixWord ++ tailWord_2630997) baseStart_2630997 baseEnd_2630997 := by
    simpa [prefixWord, tailWord_2630997, baseEnd_2630997] using wordTrace_append hprefix tailTrace_2630997
  have hstable : (prefixWord ++ tailWord_2630997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2630997).length < 2 ^ (prefixWord ++ tailWord_2630997).sum := by decide
  have hdescent : baseEnd_2630997 < baseStart_2630997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2630997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631017 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 6, 3, 2]
def baseStart_2631017 : Nat := 118140960795 + 2631017 * 2 ^ 59
def prefixEnd_2631017 : Nat := 4983230072969 + 3 ^ 40 * 2631017 * 2
def baseEnd_2631017 : Nat := 1350976331150437867587679

theorem tailTrace_2631017 : CollatzResearch.WordTrace tailWord_2631017 prefixEnd_2631017 1350976331150437867587679 := by
  unfold tailWord_2631017
  simp only [CollatzResearch.WordTrace]
  refine ⟨95961073509282225774771305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63974049006188150516514203 95961073509282225774771305)
  ·
    refine ⟨71970805131961669331078479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95961073509282225774771305 71970805131961669331078479)
    ·
      refine ⟨107956207697942503996617719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71970805131961669331078479 107956207697942503996617719)
      ·
        refine ⟨161934311546913755994926579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107956207697942503996617719 161934311546913755994926579)
        ·
          refine ⟨242901467320370633992389869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161934311546913755994926579 242901467320370633992389869)
          ·
            refine ⟨91088050245138987747146201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242901467320370633992389869 91088050245138987747146201)
            ·
              refine ⟨68316037683854240810359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91088050245138987747146201 68316037683854240810359651)
              ·
                refine ⟨102474056525781361215539477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68316037683854240810359651 102474056525781361215539477)
                ·
                  refine ⟨4803471399646001306978413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102474056525781361215539477 4803471399646001306978413)
                  ·
                    refine ⟨1801301774867250490116905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4803471399646001306978413 1801301774867250490116905)
                    ·
                      refine ⟨1350976331150437867587679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1801301774867250490116905 1350976331150437867587679)
                      ·
                        rfl

theorem cell23_2631017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 3, 2].length) (baseStart_2631017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631017 prefixEnd_2631017 := by exact prefixLift 2631017
  have htrace : WordTrace (prefixWord ++ tailWord_2631017) baseStart_2631017 baseEnd_2631017 := by
    simpa [prefixWord, tailWord_2631017, baseEnd_2631017] using wordTrace_append hprefix tailTrace_2631017
  have hstable : (prefixWord ++ tailWord_2631017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631017).length < 2 ^ (prefixWord ++ tailWord_2631017).sum := by decide
  have hdescent : baseEnd_2631017 < baseStart_2631017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631040 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_2631040 : Nat := 118140960795 + 2631040 * 2 ^ 59
def prefixEnd_2631040 : Nat := 4983230072969 + 3 ^ 40 * 2631040 * 2
def baseEnd_2631040 : Nat := 450329380401830425866691

theorem tailTrace_2631040 : CollatzResearch.WordTrace tailWord_2631040 prefixEnd_2631040 450329380401830425866691 := by
  unfold tailWord_2631040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47980956194099450351429287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63974608258799267135239049 47980956194099450351429287)
  ·
    refine ⟨71971434291149175527143931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47980956194099450351429287 71971434291149175527143931)
    ·
      refine ⟨107957151436723763290715897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71971434291149175527143931 107957151436723763290715897)
      ·
        refine ⟨80967863577542822468036923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107957151436723763290715897 80967863577542822468036923)
        ·
          refine ⟨121451795366314233702055385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80967863577542822468036923 121451795366314233702055385)
          ·
            refine ⟨91088846524735675276541539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121451795366314233702055385 91088846524735675276541539)
            ·
              refine ⟨136633269787103512914812309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91088846524735675276541539 136633269787103512914812309)
              ·
                refine ⟨6404684521270477167881827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136633269787103512914812309 6404684521270477167881827)
                ·
                  refine ⟨9607026781905715751822741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6404684521270477167881827 9607026781905715751822741)
                  ·
                    refine ⟨450329380401830425866691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9607026781905715751822741 450329380401830425866691)
                    ·
                      rfl

theorem cell23_2631040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_2631040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631040 prefixEnd_2631040 := by exact prefixLift 2631040
  have htrace : WordTrace (prefixWord ++ tailWord_2631040) baseStart_2631040 baseEnd_2631040 := by
    simpa [prefixWord, tailWord_2631040, baseEnd_2631040] using wordTrace_append hprefix tailTrace_2631040
  have hstable : (prefixWord ++ tailWord_2631040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631040).length < 2 ^ (prefixWord ++ tailWord_2631040).sum := by decide
  have hdescent : baseEnd_2631040 < baseStart_2631040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2631084 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2631084 : Nat := 118140960795 + 2631084 * 2 ^ 59
def prefixEnd_2631084 : Nat := 4983230072969 + 3 ^ 40 * 2631084 * 2
def baseEnd_2631084 : Nat := 1351010734354289105449871

theorem tailTrace_2631084 : CollatzResearch.WordTrace tailWord_2631084 prefixEnd_2631084 1351010734354289105449871 := by
  unfold tailWord_2631084
  simp only [CollatzResearch.WordTrace]
  refine ⟨47981758600019748108730153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63975678133359664144973537 47981758600019748108730153)
  ·
    refine ⟨35986318950014811081547615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47981758600019748108730153 35986318950014811081547615)
    ·
      refine ⟨53979478425022216622321423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35986318950014811081547615 53979478425022216622321423)
      ·
        refine ⟨80969217637533324933482135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53979478425022216622321423 80969217637533324933482135)
        ·
          refine ⟨121453826456299987400223203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80969217637533324933482135 121453826456299987400223203)
          ·
            refine ⟨182180739684449981100334805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121453826456299987400223203 182180739684449981100334805)
            ·
              refine ⟨4269861086354296432039097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182180739684449981100334805 4269861086354296432039097)
              ·
                refine ⟨3202395814765722324029323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269861086354296432039097 3202395814765722324029323)
                ·
                  refine ⟨4803593722148583486043985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202395814765722324029323 4803593722148583486043985)
                  ·
                    refine ⟨3602695291611437614532989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803593722148583486043985 3602695291611437614532989)
                    ·
                      refine ⟨1351010734354289105449871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3602695291611437614532989 1351010734354289105449871)
                      ·
                        rfl

theorem cell23_2631084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2631084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2631084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2631084 prefixEnd_2631084 := by exact prefixLift 2631084
  have htrace : WordTrace (prefixWord ++ tailWord_2631084) baseStart_2631084 baseEnd_2631084 := by
    simpa [prefixWord, tailWord_2631084, baseEnd_2631084] using wordTrace_append hprefix tailTrace_2631084
  have hstable : (prefixWord ++ tailWord_2631084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2631084).length < 2 ^ (prefixWord ++ tailWord_2631084).sum := by decide
  have hdescent : baseEnd_2631084 < baseStart_2631084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2631084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
