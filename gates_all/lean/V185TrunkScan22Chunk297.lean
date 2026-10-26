import V185TrunkScan22Chunk296

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2649543 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2649543 : Nat := 118140960795 + 2649543 * 2 ^ 59
def prefixEnd_2649543 : Nat := 4983230072969 + 3 ^ 40 * 2649543 * 2
def baseEnd_2649543 : Nat := 906992715837088256351653

theorem tailTrace_2649543 : CollatzResearch.WordTrace tailWord_2649543 prefixEnd_2649543 906992715837088256351653 := by
  unfold tailWord_2649543
  simp only [CollatzResearch.WordTrace]
  refine ⟨96636772240165691763673283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64424514826777127842448855 96636772240165691763673283)
  ·
    refine ⟨144955158360248537645509925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96636772240165691763673283 144955158360248537645509925)
    ·
      refine ⟨27179092192546600808533111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144955158360248537645509925 27179092192546600808533111)
      ·
        refine ⟨40768638288819901212799667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27179092192546600808533111 40768638288819901212799667)
        ·
          refine ⟨61152957433229851819199501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40768638288819901212799667 61152957433229851819199501)
          ·
            refine ⟨22932359037461194432199813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61152957433229851819199501 22932359037461194432199813)
            ·
              refine ⟨4299817319523973956037465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22932359037461194432199813 4299817319523973956037465)
              ·
                refine ⟨3224862989642980467028099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299817319523973956037465 3224862989642980467028099)
                ·
                  refine ⟨4837294484464470700542149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224862989642980467028099 4837294484464470700542149)
                  ·
                    refine ⟨906992715837088256351653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837294484464470700542149 906992715837088256351653)
                    ·
                      rfl

theorem cell22_2649543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2649543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649543 prefixEnd_2649543 := by exact prefixLift 2649543
  have htrace : WordTrace (prefixWord ++ tailWord_2649543) baseStart_2649543 baseEnd_2649543 := by
    simpa [prefixWord, tailWord_2649543, baseEnd_2649543] using wordTrace_append hprefix tailTrace_2649543
  have hstable : (prefixWord ++ tailWord_2649543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649543).length < 2 ^ (prefixWord ++ tailWord_2649543).sum := by decide
  have hdescent : baseEnd_2649543 < baseStart_2649543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649620 : List Nat := [2, 4, 3, 1, 3, 9]
def baseStart_2649620 : Nat := 118140960795 + 2649620 * 2 ^ 59
def prefixEnd_2649620 : Nat := 4983230072969 + 3 ^ 40 * 2649620 * 2
def baseEnd_2649620 : Nat := 11197766351983774347857

theorem tailTrace_2649620 : CollatzResearch.WordTrace tailWord_2649620 prefixEnd_2649620 11197766351983774347857 := by
  unfold tailWord_2649620
  simp only [CollatzResearch.WordTrace]
  refine ⟨48319790330443366957113157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64426387107257822609484209 48319790330443366957113157)
  ·
    refine ⟨9059960686958131304458717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48319790330443366957113157 9059960686958131304458717)
    ·
      refine ⟨3397485257609299239172019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9059960686958131304458717 3397485257609299239172019)
      ·
        refine ⟨5096227886413948858758029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397485257609299239172019 5096227886413948858758029)
        ·
          refine ⟨1911085457405230822034261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5096227886413948858758029 1911085457405230822034261)
          ·
            refine ⟨11197766351983774347857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1911085457405230822034261 11197766351983774347857)
            ·
              rfl

theorem cell22_2649620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 9].length) (baseStart_2649620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649620 prefixEnd_2649620 := by exact prefixLift 2649620
  have htrace : WordTrace (prefixWord ++ tailWord_2649620) baseStart_2649620 baseEnd_2649620 := by
    simpa [prefixWord, tailWord_2649620, baseEnd_2649620] using wordTrace_append hprefix tailTrace_2649620
  have hstable : (prefixWord ++ tailWord_2649620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649620).length < 2 ^ (prefixWord ++ tailWord_2649620).sum := by decide
  have hdescent : baseEnd_2649620 < baseStart_2649620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649631 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 7]
def baseStart_2649631 : Nat := 118140960795 + 2649631 * 2 ^ 59
def prefixEnd_2649631 : Nat := 4983230072969 + 3 ^ 40 * 2649631 * 2
def baseEnd_2649631 : Nat := 302340946678495120050461

theorem tailTrace_2649631 : CollatzResearch.WordTrace tailWord_2649631 prefixEnd_2649631 302340946678495120050461 := by
  unfold tailWord_2649631
  simp only [CollatzResearch.WordTrace]
  refine ⟨96639981863846882792876747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64426654575897921861917831 96639981863846882792876747)
  ·
    refine ⟨144959972795770324189315121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96639981863846882792876747 144959972795770324189315121)
    ·
      refine ⟨108719979596827743141986341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144959972795770324189315121 108719979596827743141986341)
      ·
        refine ⟨20384996174405201839122439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108719979596827743141986341 20384996174405201839122439)
        ·
          refine ⟨30577494261607802758683659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20384996174405201839122439 30577494261607802758683659)
          ·
            refine ⟨45866241392411704138025489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30577494261607802758683659 45866241392411704138025489)
            ·
              refine ⟨34399681044308778103519117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45866241392411704138025489 34399681044308778103519117)
              ·
                refine ⟨12899880391615791788819669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34399681044308778103519117 12899880391615791788819669)
                ·
                  refine ⟨302340946678495120050461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12899880391615791788819669 302340946678495120050461)
                  ·
                    rfl

theorem cell22_2649631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_2649631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649631 prefixEnd_2649631 := by exact prefixLift 2649631
  have htrace : WordTrace (prefixWord ++ tailWord_2649631) baseStart_2649631 baseEnd_2649631 := by
    simpa [prefixWord, tailWord_2649631, baseEnd_2649631] using wordTrace_append hprefix tailTrace_2649631
  have hstable : (prefixWord ++ tailWord_2649631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649631).length < 2 ^ (prefixWord ++ tailWord_2649631).sum := by decide
  have hdescent : baseEnd_2649631 < baseStart_2649631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649686 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2649686 : Nat := 118140960795 + 2649686 * 2 ^ 59
def prefixEnd_2649686 : Nat := 4983230072969 + 3 ^ 40 * 2649686 * 2
def baseEnd_2649686 : Nat := 907041667659483550026215

theorem tailTrace_2649686 : CollatzResearch.WordTrace tailWord_2649686 prefixEnd_2649686 907041667659483550026215 := by
  unfold tailWord_2649686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6040124242415476699133057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64427991919098418124085941 6040124242415476699133057)
  ·
    refine ⟨4530093181811607524349793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6040124242415476699133057 4530093181811607524349793)
    ·
      refine ⟨3397569886358705643262345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4530093181811607524349793 3397569886358705643262345)
      ·
        refine ⟨2548177414769029232446759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3397569886358705643262345 2548177414769029232446759)
        ·
          refine ⟨3822266122153543848670139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548177414769029232446759 3822266122153543848670139)
          ·
            refine ⟨5733399183230315773005209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822266122153543848670139 5733399183230315773005209)
            ·
              refine ⟨4300049387422736829753907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733399183230315773005209 4300049387422736829753907)
              ·
                refine ⟨6450074081134105244630861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300049387422736829753907 6450074081134105244630861)
                ·
                  refine ⟨2418777780425289466736573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6450074081134105244630861 2418777780425289466736573)
                  ·
                    refine ⟨907041667659483550026215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418777780425289466736573 907041667659483550026215)
                    ·
                      rfl

theorem cell22_2649686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2649686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649686 prefixEnd_2649686 := by exact prefixLift 2649686
  have htrace : WordTrace (prefixWord ++ tailWord_2649686) baseStart_2649686 baseEnd_2649686 := by
    simpa [prefixWord, tailWord_2649686, baseEnd_2649686] using wordTrace_append hprefix tailTrace_2649686
  have hstable : (prefixWord ++ tailWord_2649686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649686).length < 2 ^ (prefixWord ++ tailWord_2649686).sum := by decide
  have hdescent : baseEnd_2649686 < baseStart_2649686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649723 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_2649723 : Nat := 118140960795 + 2649723 * 2 ^ 59
def prefixEnd_2649723 : Nat := 4983230072969 + 3 ^ 40 * 2649723 * 2
def baseEnd_2649723 : Nat := 907054333515627786851101

theorem tailTrace_2649723 : CollatzResearch.WordTrace tailWord_2649723 prefixEnd_2649723 907054333515627786851101 := by
  unfold tailWord_2649723
  simp only [CollatzResearch.WordTrace]
  refine ⟨96643337379513582505225823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64428891586342388336817215 96643337379513582505225823)
  ·
    refine ⟨144965006069270373757838735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96643337379513582505225823 144965006069270373757838735)
    ·
      refine ⟨217447509103905560636758103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144965006069270373757838735 217447509103905560636758103)
      ·
        refine ⟨326171263655858340955137155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217447509103905560636758103 326171263655858340955137155)
        ·
          refine ⟨489256895483787511432705733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326171263655858340955137155 489256895483787511432705733)
          ·
            refine ⟨91735667903210158393632325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 489256895483787511432705733 91735667903210158393632325)
            ·
              refine ⟨17200437731851904698806061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91735667903210158393632325 17200437731851904698806061)
              ·
                refine ⟨6450164149444464262052273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17200437731851904698806061 6450164149444464262052273)
                ·
                  refine ⟨4837623112083348196539205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450164149444464262052273 4837623112083348196539205)
                  ·
                    refine ⟨907054333515627786851101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837623112083348196539205 907054333515627786851101)
                    ·
                      rfl

theorem cell22_2649723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_2649723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649723 prefixEnd_2649723 := by exact prefixLift 2649723
  have htrace : WordTrace (prefixWord ++ tailWord_2649723) baseStart_2649723 baseEnd_2649723 := by
    simpa [prefixWord, tailWord_2649723, baseEnd_2649723] using wordTrace_append hprefix tailTrace_2649723
  have hstable : (prefixWord ++ tailWord_2649723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649723).length < 2 ^ (prefixWord ++ tailWord_2649723).sum := by decide
  have hdescent : baseEnd_2649723 < baseStart_2649723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649725 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_2649725 : Nat := 118140960795 + 2649725 * 2 ^ 59
def prefixEnd_2649725 : Nat := 4983230072969 + 3 ^ 40 * 2649725 * 2
def baseEnd_2649725 : Nat := 907055018156500448301095

theorem tailTrace_2649725 : CollatzResearch.WordTrace tailWord_2649725 prefixEnd_2649725 907055018156500448301095 := by
  unfold tailWord_2649725
  simp only [CollatzResearch.WordTrace]
  refine ⟨96643410325506336846798629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64428940217004224564532419 96643410325506336846798629)
  ·
    refine ⟨18120639436032438158774743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96643410325506336846798629 18120639436032438158774743)
    ·
      refine ⟨27180959154048657238162115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18120639436032438158774743 27180959154048657238162115)
      ·
        refine ⟨40771438731072985857243173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27180959154048657238162115 40771438731072985857243173)
        ·
          refine ⟨7644644762076184848233095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40771438731072985857243173 7644644762076184848233095)
          ·
            refine ⟨11466967143114277272349643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644644762076184848233095 11466967143114277272349643)
            ·
              refine ⟨17200450714671415908524465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11466967143114277272349643 17200450714671415908524465)
              ·
                refine ⟨12900338036003561931393349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17200450714671415908524465 12900338036003561931393349)
                ·
                  refine ⟨2418813381750667862136253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12900338036003561931393349 2418813381750667862136253)
                  ·
                    refine ⟨907055018156500448301095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418813381750667862136253 907055018156500448301095)
                    ·
                      rfl

theorem cell22_2649725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_2649725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649725 prefixEnd_2649725 := by exact prefixLift 2649725
  have htrace : WordTrace (prefixWord ++ tailWord_2649725) baseStart_2649725 baseEnd_2649725 := by
    simpa [prefixWord, tailWord_2649725, baseEnd_2649725] using wordTrace_append hprefix tailTrace_2649725
  have hstable : (prefixWord ++ tailWord_2649725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649725).length < 2 ^ (prefixWord ++ tailWord_2649725).sum := by decide
  have hdescent : baseEnd_2649725 < baseStart_2649725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649738 : List Nat := [3, 1, 2, 3, 2, 1, 10]
def baseStart_2649738 : Nat := 118140960795 + 2649738 * 2 ^ 59
def prefixEnd_2649738 : Nat := 4983230072969 + 3 ^ 40 * 2649738 * 2
def baseEnd_2649738 : Nat := 33594795123043435100965

theorem tailTrace_2649738 : CollatzResearch.WordTrace tailWord_2649738 prefixEnd_2649738 33594795123043435100965 := by
  unfold tailWord_2649738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160971118614810016755467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64429256316306160044681245 24160971118614810016755467)
  ·
    refine ⟨36241456677922215025133201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24160971118614810016755467 36241456677922215025133201)
    ·
      refine ⟨27181092508441661268849901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36241456677922215025133201 27181092508441661268849901)
      ·
        refine ⟨10192909690665622975818713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27181092508441661268849901 10192909690665622975818713)
        ·
          refine ⟨7644682267999217231864035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10192909690665622975818713 7644682267999217231864035)
          ·
            refine ⟨11467023401998825847796053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644682267999217231864035 11467023401998825847796053)
            ·
              refine ⟨33594795123043435100965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11467023401998825847796053 33594795123043435100965)
              ·
                rfl

theorem cell22_2649738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 10].length) (baseStart_2649738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649738 prefixEnd_2649738 := by exact prefixLift 2649738
  have htrace : WordTrace (prefixWord ++ tailWord_2649738) baseStart_2649738 baseEnd_2649738 := by
    simpa [prefixWord, tailWord_2649738, baseEnd_2649738] using wordTrace_append hprefix tailTrace_2649738
  have hstable : (prefixWord ++ tailWord_2649738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649738).length < 2 ^ (prefixWord ++ tailWord_2649738).sum := by decide
  have hdescent : baseEnd_2649738 < baseStart_2649738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649759 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 2, 3]
def baseStart_2649759 : Nat := 118140960795 + 2649759 * 2 ^ 59
def prefixEnd_2649759 : Nat := 4983230072969 + 3 ^ 40 * 2649759 * 2
def baseEnd_2649759 : Nat := 907066657051335692950991

theorem tailTrace_2649759 : CollatzResearch.WordTrace tailWord_2649759 prefixEnd_2649759 907066657051335692950991 := by
  unfold tailWord_2649759
  simp only [CollatzResearch.WordTrace]
  refine ⟨96644650407383160653536331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64429766938255440435690887 96644650407383160653536331)
  ·
    refine ⟨144966975611074740980304497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96644650407383160653536331 144966975611074740980304497)
    ·
      refine ⟨108725231708306055735228373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144966975611074740980304497 108725231708306055735228373)
      ·
        refine ⟨2548247618163423181294415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108725231708306055735228373 2548247618163423181294415)
        ·
          refine ⟨3822371427245134771941623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548247618163423181294415 3822371427245134771941623)
          ·
            refine ⟨5733557140867702157912435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822371427245134771941623 5733557140867702157912435)
            ·
              refine ⟨8600335711301553236868653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733557140867702157912435 8600335711301553236868653)
              ·
                refine ⟨3225125891738082463825745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8600335711301553236868653 3225125891738082463825745)
                ·
                  refine ⟨2418844418803561847869309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225125891738082463825745 2418844418803561847869309)
                  ·
                    refine ⟨907066657051335692950991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418844418803561847869309 907066657051335692950991)
                    ·
                      rfl

theorem cell22_2649759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_2649759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649759 prefixEnd_2649759 := by exact prefixLift 2649759
  have htrace : WordTrace (prefixWord ++ tailWord_2649759) baseStart_2649759 baseEnd_2649759 := by
    simpa [prefixWord, tailWord_2649759, baseEnd_2649759] using wordTrace_append hprefix tailTrace_2649759
  have hstable : (prefixWord ++ tailWord_2649759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649759).length < 2 ^ (prefixWord ++ tailWord_2649759).sum := by decide
  have hdescent : baseEnd_2649759 < baseStart_2649759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649774 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2649774 : Nat := 118140960795 + 2649774 * 2 ^ 59
def prefixEnd_2649774 : Nat := 4983230072969 + 3 ^ 40 * 2649774 * 2
def baseEnd_2649774 : Nat := 907071791857880653825945

theorem tailTrace_2649774 : CollatzResearch.WordTrace tailWord_2649774 prefixEnd_2649774 907071791857880653825945 := by
  unfold tailWord_2649774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080649687791102276916547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64430131668219212143554917 12080649687791102276916547)
  ·
    refine ⟨18120974531686653415374821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12080649687791102276916547 18120974531686653415374821)
    ·
      refine ⟨3397682724691247515382779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18120974531686653415374821 3397682724691247515382779)
      ·
        refine ⟨5096524087036871273074169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397682724691247515382779 5096524087036871273074169)
        ·
          refine ⟨3822393065277653454805627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096524087036871273074169 3822393065277653454805627)
          ·
            refine ⟨5733589597916480182208441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822393065277653454805627 5733589597916480182208441)
            ·
              refine ⟨4300192198437360136656331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733589597916480182208441 4300192198437360136656331)
              ·
                refine ⟨6450288297656040204984497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300192198437360136656331 6450288297656040204984497)
                ·
                  refine ⟨4837716223242030153738373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6450288297656040204984497 4837716223242030153738373)
                  ·
                    refine ⟨907071791857880653825945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837716223242030153738373 907071791857880653825945)
                    ·
                      rfl

theorem cell22_2649774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2649774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649774 prefixEnd_2649774 := by exact prefixLift 2649774
  have htrace : WordTrace (prefixWord ++ tailWord_2649774) baseStart_2649774 baseEnd_2649774 := by
    simpa [prefixWord, tailWord_2649774, baseEnd_2649774] using wordTrace_append hprefix tailTrace_2649774
  have hstable : (prefixWord ++ tailWord_2649774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649774).length < 2 ^ (prefixWord ++ tailWord_2649774).sum := by decide
  have hdescent : baseEnd_2649774 < baseStart_2649774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649800 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_2649800 : Nat := 118140960795 + 2649800 * 2 ^ 59
def prefixEnd_2649800 : Nat := 4983230072969 + 3 ^ 40 * 2649800 * 2
def baseEnd_2649800 : Nat := 302360230729741750891955

theorem tailTrace_2649800 : CollatzResearch.WordTrace tailWord_2649800 prefixEnd_2649800 302360230729741750891955 := by
  unfold tailWord_2649800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48323072900117312327889427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64430763866823083103852569 48323072900117312327889427)
  ·
    refine ⟨72484609350175968491834141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48323072900117312327889427 72484609350175968491834141)
    ·
      refine ⟨27181728506315988184437803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72484609350175968491834141 27181728506315988184437803)
      ·
        refine ⟨40772592759473982276656705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27181728506315988184437803 40772592759473982276656705)
        ·
          refine ⟨30579444569605486707492529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40772592759473982276656705 30579444569605486707492529)
          ·
            refine ⟨22934583427204115030619397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30579444569605486707492529 22934583427204115030619397)
            ·
              refine ⟨4300234392600771568241137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22934583427204115030619397 4300234392600771568241137)
              ·
                refine ⟨3225175794450578676180853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300234392600771568241137 3225175794450578676180853)
                ·
                  refine ⟨302360230729741750891955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225175794450578676180853 302360230729741750891955)
                  ·
                    rfl

theorem cell22_2649800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_2649800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649800 prefixEnd_2649800 := by exact prefixLift 2649800
  have htrace : WordTrace (prefixWord ++ tailWord_2649800) baseStart_2649800 baseEnd_2649800 := by
    simpa [prefixWord, tailWord_2649800, baseEnd_2649800] using wordTrace_append hprefix tailTrace_2649800
  have hstable : (prefixWord ++ tailWord_2649800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649800).length < 2 ^ (prefixWord ++ tailWord_2649800).sum := by decide
  have hdescent : baseEnd_2649800 < baseStart_2649800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649847 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2649847 : Nat := 118140960795 + 2649847 * 2 ^ 59
def prefixEnd_2649847 : Nat := 4983230072969 + 3 ^ 40 * 2649847 * 2
def baseEnd_2649847 : Nat := 907096781249732796750721

theorem tailTrace_2649847 : CollatzResearch.WordTrace tailWord_2649847 prefixEnd_2649847 907096781249732796750721 := by
  unfold tailWord_2649847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96647860031064351682739795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64431906687376234455159863 96647860031064351682739795)
  ·
    refine ⟨144971790046596527524109693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96647860031064351682739795 144971790046596527524109693)
    ·
      refine ⟨54364421267473697821541135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144971790046596527524109693 54364421267473697821541135)
      ·
        refine ⟨81546631901210546732311703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54364421267473697821541135 81546631901210546732311703)
        ·
          refine ⟨122319947851815820098467555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81546631901210546732311703 122319947851815820098467555)
          ·
            refine ⟨183479921777723730147701333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122319947851815820098467555 183479921777723730147701333)
            ·
              refine ⟨2150155333332699962668375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 183479921777723730147701333 2150155333332699962668375)
              ·
                refine ⟨3225232999999049944002563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150155333332699962668375 3225232999999049944002563)
                ·
                  refine ⟨4837849499998574916003845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225232999999049944002563 4837849499998574916003845)
                  ·
                    refine ⟨907096781249732796750721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837849499998574916003845 907096781249732796750721)
                    ·
                      rfl

theorem cell22_2649847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2649847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649847 prefixEnd_2649847 := by exact prefixLift 2649847
  have htrace : WordTrace (prefixWord ++ tailWord_2649847) baseStart_2649847 baseEnd_2649847 := by
    simpa [prefixWord, tailWord_2649847, baseEnd_2649847] using wordTrace_append hprefix tailTrace_2649847
  have hstable : (prefixWord ++ tailWord_2649847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649847).length < 2 ^ (prefixWord ++ tailWord_2649847).sum := by decide
  have hdescent : baseEnd_2649847 < baseStart_2649847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649873 : List Nat := [1, 2, 2, 1, 1, 3, 1, 11]
def baseStart_2649873 : Nat := 118140960795 + 2649873 * 2 ^ 59
def prefixEnd_2649873 : Nat := 4983230072969 + 3 ^ 40 * 2649873 * 2
def baseEnd_2649873 : Nat := 100789520175675266177849

theorem tailTrace_2649873 : CollatzResearch.WordTrace tailWord_2649873 prefixEnd_2649873 100789520175675266177849 := by
  unfold tailWord_2649873
  simp only [CollatzResearch.WordTrace]
  refine ⟨96648808328970158123186273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64432538885980105415457515 96648808328970158123186273)
  ·
    refine ⟨72486606246727618592389705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96648808328970158123186273 72486606246727618592389705)
    ·
      refine ⟨54364954685045713944292279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72486606246727618592389705 54364954685045713944292279)
      ·
        refine ⟨81547432027568570916438419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54364954685045713944292279 81547432027568570916438419)
        ·
          refine ⟨122321148041352856374657629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81547432027568570916438419 122321148041352856374657629)
          ·
            refine ⟨45870430515507321140496611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122321148041352856374657629 45870430515507321140496611)
            ·
              refine ⟨68805645773260981710744917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45870430515507321140496611 68805645773260981710744917)
              ·
                refine ⟨100789520175675266177849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68805645773260981710744917 100789520175675266177849)
                ·
                  rfl

theorem cell22_2649873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 11].length) (baseStart_2649873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649873 prefixEnd_2649873 := by exact prefixLift 2649873
  have htrace : WordTrace (prefixWord ++ tailWord_2649873) baseStart_2649873 baseEnd_2649873 := by
    simpa [prefixWord, tailWord_2649873, baseEnd_2649873] using wordTrace_append hprefix tailTrace_2649873
  have hstable : (prefixWord ++ tailWord_2649873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649873).length < 2 ^ (prefixWord ++ tailWord_2649873).sum := by decide
  have hdescent : baseEnd_2649873 < baseStart_2649873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649877 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2649877 : Nat := 118140960795 + 2649877 * 2 ^ 59
def prefixEnd_2649877 : Nat := 4983230072969 + 3 ^ 40 * 2649877 * 2
def baseEnd_2649877 : Nat := 907107050862822718500629

theorem tailTrace_2649877 : CollatzResearch.WordTrace tailWord_2649877 prefixEnd_2649877 907107050862822718500629 := by
  unfold tailWord_2649877
  simp only [CollatzResearch.WordTrace]
  refine ⟨96648954220955666806331885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64432636147303777870887923 96648954220955666806331885)
  ·
    refine ⟨36243357832858375052374457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96648954220955666806331885 36243357832858375052374457)
    ·
      refine ⟨27182518374643781289280843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36243357832858375052374457 27182518374643781289280843)
      ·
        refine ⟨40773777561965671933921265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27182518374643781289280843 40773777561965671933921265)
        ·
          refine ⟨30580333171474253950440949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40773777561965671933921265 30580333171474253950440949)
          ·
            refine ⟨2866906234825711307853839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30580333171474253950440949 2866906234825711307853839)
            ·
              refine ⟨4300359352238566961780759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866906234825711307853839 4300359352238566961780759)
              ·
                refine ⟨6450539028357850442671139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300359352238566961780759 6450539028357850442671139)
                ·
                  refine ⟨9675808542536775664006709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6450539028357850442671139 9675808542536775664006709)
                  ·
                    refine ⟨907107050862822718500629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9675808542536775664006709 907107050862822718500629)
                    ·
                      rfl

theorem cell22_2649877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2649877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649877 prefixEnd_2649877 := by exact prefixLift 2649877
  have htrace : WordTrace (prefixWord ++ tailWord_2649877) baseStart_2649877 baseEnd_2649877 := by
    simpa [prefixWord, tailWord_2649877, baseEnd_2649877] using wordTrace_append hprefix tailTrace_2649877
  have hstable : (prefixWord ++ tailWord_2649877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649877).length < 2 ^ (prefixWord ++ tailWord_2649877).sum := by decide
  have hdescent : baseEnd_2649877 < baseStart_2649877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649890 : List Nat := [3, 3, 1, 1, 2, 1, 3, 8]
def baseStart_2649890 : Nat := 118140960795 + 2649890 * 2 ^ 59
def prefixEnd_2649890 : Nat := 4983230072969 + 3 ^ 40 * 2649890 * 2
def baseEnd_2649890 : Nat := 100790166780943890880621

theorem tailTrace_2649890 : CollatzResearch.WordTrace tailWord_2649890 prefixEnd_2649890 100790166780943890880621 := by
  unfold tailWord_2649890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24162357092477142506638781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64432952246605713351036749 24162357092477142506638781)
  ·
    refine ⟨9060883909678928439989543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24162357092477142506638781 9060883909678928439989543)
    ·
      refine ⟨13591325864518392659984315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060883909678928439989543 13591325864518392659984315)
      ·
        refine ⟨20386988796777588989976473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13591325864518392659984315 20386988796777588989976473)
        ·
          refine ⟨15290241597583191742482355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20386988796777588989976473 15290241597583191742482355)
          ·
            refine ⟨22935362396374787613723533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15290241597583191742482355 22935362396374787613723533)
            ·
              refine ⟨8600760898640545355146325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22935362396374787613723533 8600760898640545355146325)
              ·
                refine ⟨100790166780943890880621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8600760898640545355146325 100790166780943890880621)
                ·
                  rfl

theorem cell22_2649890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_2649890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649890 prefixEnd_2649890 := by exact prefixLift 2649890
  have htrace : WordTrace (prefixWord ++ tailWord_2649890) baseStart_2649890 baseEnd_2649890 := by
    simpa [prefixWord, tailWord_2649890, baseEnd_2649890] using wordTrace_append hprefix tailTrace_2649890
  have hstable : (prefixWord ++ tailWord_2649890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649890).length < 2 ^ (prefixWord ++ tailWord_2649890).sum := by decide
  have hdescent : baseEnd_2649890 < baseStart_2649890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649907 : List Nat := [1, 1, 1, 2, 8, 1, 8]
def baseStart_2649907 : Nat := 118140960795 + 2649907 * 2 ^ 59
def prefixEnd_2649907 : Nat := 4983230072969 + 3 ^ 40 * 2649907 * 2
def baseEnd_2649907 : Nat := 33596937795404171861131

theorem tailTrace_2649907 : CollatzResearch.WordTrace tailWord_2649907 prefixEnd_2649907 33596937795404171861131 := by
  unfold tailWord_2649907
  simp only [CollatzResearch.WordTrace]
  refine ⟨96650048410846981929923975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64433365607231321286615983 96650048410846981929923975)
  ·
    refine ⟨144975072616270472894885963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96650048410846981929923975 144975072616270472894885963)
    ·
      refine ⟨217462608924405709342328945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144975072616270472894885963 217462608924405709342328945)
      ·
        refine ⟨163096956693304282006746709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217462608924405709342328945 163096956693304282006746709)
        ·
          refine ⟨1911292461249659554766563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 163096956693304282006746709 1911292461249659554766563)
          ·
            refine ⟨2866938691874489332149845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911292461249659554766563 2866938691874489332149845)
            ·
              refine ⟨33596937795404171861131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2866938691874489332149845 33596937795404171861131)
              ·
                rfl

theorem cell22_2649907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 8].length) (baseStart_2649907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2649907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2649907 prefixEnd_2649907 := by exact prefixLift 2649907
  have htrace : WordTrace (prefixWord ++ tailWord_2649907) baseStart_2649907 baseEnd_2649907 := by
    simpa [prefixWord, tailWord_2649907, baseEnd_2649907] using wordTrace_append hprefix tailTrace_2649907
  have hstable : (prefixWord ++ tailWord_2649907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649907).length < 2 ^ (prefixWord ++ tailWord_2649907).sum := by decide
  have hdescent : baseEnd_2649907 < baseStart_2649907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650104 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_2650104 : Nat := 118140960795 + 2650104 * 2 ^ 59
def prefixEnd_2650104 : Nat := 4983230072969 + 3 ^ 40 * 2650104 * 2
def baseEnd_2650104 : Nat := 302394919200623264358311

theorem tailTrace_2650104 : CollatzResearch.WordTrace tailWord_2650104 prefixEnd_2650104 302394919200623264358311 := by
  unfold tailWord_2650104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48328616795566642287422683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64438155727422189716563577 48328616795566642287422683)
  ·
    refine ⟨72492925193349963431134025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48328616795566642287422683 72492925193349963431134025)
    ·
      refine ⟨54369693895012472573350519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72492925193349963431134025 54369693895012472573350519)
      ·
        refine ⟨81554540842518708860025779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54369693895012472573350519 81554540842518708860025779)
        ·
          refine ⟨122331811263778063290038669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81554540842518708860025779 122331811263778063290038669)
          ·
            refine ⟨45874429223916773733764501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122331811263778063290038669 45874429223916773733764501)
            ·
              refine ⟨2150363869871098768770211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45874429223916773733764501 2150363869871098768770211)
              ·
                refine ⟨3225545804806648153155317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150363869871098768770211 3225545804806648153155317)
                ·
                  refine ⟨302394919200623264358311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225545804806648153155317 302394919200623264358311)
                  ·
                    rfl

theorem cell22_2650104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_2650104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650104 prefixEnd_2650104 := by exact prefixLift 2650104
  have htrace : WordTrace (prefixWord ++ tailWord_2650104) baseStart_2650104 baseEnd_2650104 := by
    simpa [prefixWord, tailWord_2650104, baseEnd_2650104] using wordTrace_append hprefix tailTrace_2650104
  have hstable : (prefixWord ++ tailWord_2650104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650104).length < 2 ^ (prefixWord ++ tailWord_2650104).sum := by decide
  have hdescent : baseEnd_2650104 < baseStart_2650104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650147 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_2650147 : Nat := 118140960795 + 2650147 * 2 ^ 59
def prefixEnd_2650147 : Nat := 4983230072969 + 3 ^ 40 * 2650147 * 2
def baseEnd_2650147 : Nat := 907199477380632014249801

theorem tailTrace_2650147 : CollatzResearch.WordTrace tailWord_2650147 prefixEnd_2650147 907199477380632014249801 := by
  unfold tailWord_2650147
  simp only [CollatzResearch.WordTrace]
  refine ⟨96658801929977502918660695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64439201286651668612440463 96658801929977502918660695)
  ·
    refine ⟨144988202894966254377991043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96658801929977502918660695 144988202894966254377991043)
    ·
      refine ⟨217482304342449381566986565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144988202894966254377991043 217482304342449381566986565)
      ·
        refine ⟨40777932064209259043809981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217482304342449381566986565 40777932064209259043809981)
        ·
          refine ⟨15291724524078472141428743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40777932064209259043809981 15291724524078472141428743)
          ·
            refine ⟨22937586786117708212143115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15291724524078472141428743 22937586786117708212143115)
            ·
              refine ⟨34406380179176562318214673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22937586786117708212143115 34406380179176562318214673)
              ·
                refine ⟨25804785134382421738661005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34406380179176562318214673 25804785134382421738661005)
                ·
                  refine ⟨9676794425393408151997877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25804785134382421738661005 9676794425393408151997877)
                  ·
                    refine ⟨907199477380632014249801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9676794425393408151997877 907199477380632014249801)
                    ·
                      rfl

theorem cell22_2650147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_2650147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650147 prefixEnd_2650147 := by exact prefixLift 2650147
  have htrace : WordTrace (prefixWord ++ tailWord_2650147) baseStart_2650147 baseEnd_2650147 := by
    simpa [prefixWord, tailWord_2650147, baseEnd_2650147] using wordTrace_append hprefix tailTrace_2650147
  have hstable : (prefixWord ++ tailWord_2650147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650147).length < 2 ^ (prefixWord ++ tailWord_2650147).sum := by decide
  have hdescent : baseEnd_2650147 < baseStart_2650147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650194 : List Nat := [3, 2, 2, 1, 4, 1, 9]
def baseStart_2650194 : Nat := 118140960795 + 2650194 * 2 ^ 59
def prefixEnd_2650194 : Nat := 4983230072969 + 3 ^ 40 * 2650194 * 2
def baseEnd_2650194 : Nat := 33600576534857020678691

theorem tailTrace_2650194 : CollatzResearch.WordTrace tailWord_2650194 prefixEnd_2650194 33600576534857020678691 := by
  unfold tailWord_2650194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165129040201807486405409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64440344107204819963747757 24165129040201807486405409)
  ·
    refine ⟨18123846780151355614804057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24165129040201807486405409 18123846780151355614804057)
    ·
      refine ⟨13592885085113516711103043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18123846780151355614804057 13592885085113516711103043)
      ·
        refine ⟨20389327627670275066654565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13592885085113516711103043 20389327627670275066654565)
        ·
          refine ⟨3822998930188176574997731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20389327627670275066654565 3822998930188176574997731)
          ·
            refine ⟨5734498395282264862496597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822998930188176574997731 5734498395282264862496597)
            ·
              refine ⟨33600576534857020678691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5734498395282264862496597 33600576534857020678691)
              ·
                rfl

theorem cell22_2650194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 9].length) (baseStart_2650194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650194 prefixEnd_2650194 := by exact prefixLift 2650194
  have htrace : WordTrace (prefixWord ++ tailWord_2650194) baseStart_2650194 baseEnd_2650194 := by
    simpa [prefixWord, tailWord_2650194, baseEnd_2650194] using wordTrace_append hprefix tailTrace_2650194
  have hstable : (prefixWord ++ tailWord_2650194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650194).length < 2 ^ (prefixWord ++ tailWord_2650194).sum := by decide
  have hdescent : baseEnd_2650194 < baseStart_2650194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650207 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2650207 : Nat := 118140960795 + 2650207 * 2 ^ 59
def prefixEnd_2650207 : Nat := 4983230072969 + 3 ^ 40 * 2650207 * 2
def baseEnd_2650207 : Nat := 907220016606811857749617

theorem tailTrace_2650207 : CollatzResearch.WordTrace tailWord_2650207 prefixEnd_2650207 907220016606811857749617 := by
  unfold tailWord_2650207
  simp only [CollatzResearch.WordTrace]
  refine ⟨96660990309760133165844875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64440660206506755443896583 96660990309760133165844875)
  ·
    refine ⟨144991485464640199748767313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96660990309760133165844875 144991485464640199748767313)
    ·
      refine ⟨108743614098480149811575485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144991485464640199748767313 108743614098480149811575485)
      ·
        refine ⟨40778855286930056179340807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108743614098480149811575485 40778855286930056179340807)
        ·
          refine ⟨61168282930395084269011211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40778855286930056179340807 61168282930395084269011211)
          ·
            refine ⟨91752424395592626403516817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61168282930395084269011211 91752424395592626403516817)
            ·
              refine ⟨68814318296694469802637613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91752424395592626403516817 68814318296694469802637613)
              ·
                refine ⟨25805369361260426175989105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68814318296694469802637613 25805369361260426175989105)
                ·
                  refine ⟨19354027020945319631991829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25805369361260426175989105 19354027020945319631991829)
                  ·
                    refine ⟨907220016606811857749617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19354027020945319631991829 907220016606811857749617)
                    ·
                      rfl

theorem cell22_2650207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2650207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650207 prefixEnd_2650207 := by exact prefixLift 2650207
  have htrace : WordTrace (prefixWord ++ tailWord_2650207) baseStart_2650207 baseEnd_2650207 := by
    simpa [prefixWord, tailWord_2650207, baseEnd_2650207] using wordTrace_append hprefix tailTrace_2650207
  have hstable : (prefixWord ++ tailWord_2650207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650207).length < 2 ^ (prefixWord ++ tailWord_2650207).sum := by decide
  have hdescent : baseEnd_2650207 < baseStart_2650207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650226 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_2650226 : Nat := 118140960795 + 2650226 * 2 ^ 59
def prefixEnd_2650226 : Nat := 4983230072969 + 3 ^ 40 * 2650226 * 2
def baseEnd_2650226 : Nat := 907226520695102141524559

theorem tailTrace_2650226 : CollatzResearch.WordTrace tailWord_2650226 prefixEnd_2650226 907226520695102141524559 := by
  unfold tailWord_2650226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165420824172824852696633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64441122197794199607191021 24165420824172824852696633)
  ·
    refine ⟨18124065618129618639522475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24165420824172824852696633 18124065618129618639522475)
    ·
      refine ⟨27186098427194427959283713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18124065618129618639522475 27186098427194427959283713)
      ·
        refine ⟨20389573820395820969462785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27186098427194427959283713 20389573820395820969462785)
        ·
          refine ⟨15292180365296865727097089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20389573820395820969462785 15292180365296865727097089)
          ·
            refine ⟨11469135273972649295322817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15292180365296865727097089 11469135273972649295322817)
            ·
              refine ⟨8601851455479486971492113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11469135273972649295322817 8601851455479486971492113)
              ·
                refine ⟨6451388591609615228619085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8601851455479486971492113 6451388591609615228619085)
                ·
                  refine ⟨2419270721853605710732157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6451388591609615228619085 2419270721853605710732157)
                  ·
                    refine ⟨907226520695102141524559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419270721853605710732157 907226520695102141524559)
                    ·
                      rfl

theorem cell22_2650226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_2650226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650226 prefixEnd_2650226 := by exact prefixLift 2650226
  have htrace : WordTrace (prefixWord ++ tailWord_2650226) baseStart_2650226 baseEnd_2650226 := by
    simpa [prefixWord, tailWord_2650226, baseEnd_2650226] using wordTrace_append hprefix tailTrace_2650226
  have hstable : (prefixWord ++ tailWord_2650226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650226).length < 2 ^ (prefixWord ++ tailWord_2650226).sum := by decide
  have hdescent : baseEnd_2650226 < baseStart_2650226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650243 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 1, 3]
def baseStart_2650243 : Nat := 118140960795 + 2650243 * 2 ^ 59
def prefixEnd_2650243 : Nat := 4983230072969 + 3 ^ 40 * 2650243 * 2
def baseEnd_2650243 : Nat := 907232340142519763849507

theorem tailTrace_2650243 : CollatzResearch.WordTrace tailWord_2650243 prefixEnd_2650243 907232340142519763849507 := by
  unfold tailWord_2650243
  simp only [CollatzResearch.WordTrace]
  refine ⟨96662303337629711314155383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64441535558419807542770255 96662303337629711314155383)
  ·
    refine ⟨144993455006444566971233075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96662303337629711314155383 144993455006444566971233075)
    ·
      refine ⟨217490182509666850456849613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144993455006444566971233075 217490182509666850456849613)
      ·
        refine ⟨81558818441125068921318605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217490182509666850456849613 81558818441125068921318605)
        ·
          refine ⟨30584556915421900845494477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81558818441125068921318605 30584556915421900845494477)
          ·
            refine ⟨11469208843283212817060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30584556915421900845494477 11469208843283212817060429)
            ·
              refine ⟨4300953316231204806397661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11469208843283212817060429 4300953316231204806397661)
              ·
                refine ⟨1612857493586701802399123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300953316231204806397661 1612857493586701802399123)
                ·
                  refine ⟨2419286240380052703598685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612857493586701802399123 2419286240380052703598685)
                  ·
                    refine ⟨907232340142519763849507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419286240380052703598685 907232340142519763849507)
                    ·
                      rfl

theorem cell22_2650243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 3].length) (baseStart_2650243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650243 prefixEnd_2650243 := by exact prefixLift 2650243
  have htrace : WordTrace (prefixWord ++ tailWord_2650243) baseStart_2650243 baseEnd_2650243 := by
    simpa [prefixWord, tailWord_2650243, baseEnd_2650243] using wordTrace_append hprefix tailTrace_2650243
  have hstable : (prefixWord ++ tailWord_2650243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650243).length < 2 ^ (prefixWord ++ tailWord_2650243).sum := by decide
  have hdescent : baseEnd_2650243 < baseStart_2650243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650262 : List Nat := [5, 3, 2, 1, 1, 1, 2, 7]
def baseStart_2650262 : Nat := 118140960795 + 2650262 * 2 ^ 59
def prefixEnd_2650262 : Nat := 4983230072969 + 3 ^ 40 * 2650262 * 2
def baseEnd_2650262 : Nat := 100804316025645560847161

theorem tailTrace_2650262 : CollatzResearch.WordTrace tailWord_2650262 prefixEnd_2650262 100804316025645560847161 := by
  unfold tailWord_2650262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041437270285054847443565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64441997549707251706064693 6041437270285054847443565)
  ·
    refine ⟨2265538976356895567791337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6041437270285054847443565 2265538976356895567791337)
    ·
      refine ⟨1699154232267671675843503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2265538976356895567791337 1699154232267671675843503)
      ·
        refine ⟨2548731348401507513765255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1699154232267671675843503 2548731348401507513765255)
        ·
          refine ⟨3823097022602261270647883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548731348401507513765255 3823097022602261270647883)
          ·
            refine ⟨5734645533903391905971825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823097022602261270647883 5734645533903391905971825)
            ·
              refine ⟨4300984150427543929478869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734645533903391905971825 4300984150427543929478869)
              ·
                refine ⟨100804316025645560847161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4300984150427543929478869 100804316025645560847161)
                ·
                  rfl

theorem cell22_2650262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_2650262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650262 prefixEnd_2650262 := by exact prefixLift 2650262
  have htrace : WordTrace (prefixWord ++ tailWord_2650262) baseStart_2650262 baseEnd_2650262 := by
    simpa [prefixWord, tailWord_2650262, baseEnd_2650262] using wordTrace_append hprefix tailTrace_2650262
  have hstable : (prefixWord ++ tailWord_2650262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650262).length < 2 ^ (prefixWord ++ tailWord_2650262).sum := by decide
  have hdescent : baseEnd_2650262 < baseStart_2650262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650267 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 10]
def baseStart_2650267 : Nat := 118140960795 + 2650267 * 2 ^ 59
def prefixEnd_2650267 : Nat := 4983230072969 + 3 ^ 40 * 2650267 * 2
def baseEnd_2650267 : Nat := 302413518610997233749811

theorem tailTrace_2650267 : CollatzResearch.WordTrace tailWord_2650267 prefixEnd_2650267 302413518610997233749811 := by
  unfold tailWord_2650267
  simp only [CollatzResearch.WordTrace]
  refine ⟨96663178689542763413029055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64442119126361842275352703 96663178689542763413029055)
  ·
    refine ⟨144994768034314145119543583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96663178689542763413029055 144994768034314145119543583)
    ·
      refine ⟨217492152051471217679315375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144994768034314145119543583 217492152051471217679315375)
      ·
        refine ⟨326238228077206826518973063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217492152051471217679315375 326238228077206826518973063)
        ·
          refine ⟨489357342115810239778459595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326238228077206826518973063 489357342115810239778459595)
          ·
            refine ⟨734036013173715359667689393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489357342115810239778459595 734036013173715359667689393)
            ·
              refine ⟨550527009880286519750767045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734036013173715359667689393 550527009880286519750767045)
              ·
                refine ⟨103223814352553722453268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550527009880286519750767045 103223814352553722453268821)
                ·
                  refine ⟨302413518610997233749811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103223814352553722453268821 302413518610997233749811)
                  ·
                    rfl

theorem cell22_2650267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_2650267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650267 prefixEnd_2650267 := by exact prefixLift 2650267
  have htrace : WordTrace (prefixWord ++ tailWord_2650267) baseStart_2650267 baseEnd_2650267 := by
    simpa [prefixWord, tailWord_2650267, baseEnd_2650267] using wordTrace_append hprefix tailTrace_2650267
  have hstable : (prefixWord ++ tailWord_2650267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650267).length < 2 ^ (prefixWord ++ tailWord_2650267).sum := by decide
  have hdescent : baseEnd_2650267 < baseStart_2650267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650273 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 5]
def baseStart_2650273 : Nat := 118140960795 + 2650273 * 2 ^ 59
def prefixEnd_2650273 : Nat := 4983230072969 + 3 ^ 40 * 2650273 * 2
def baseEnd_2650273 : Nat := 302414203251869895199805

theorem tailTrace_2650273 : CollatzResearch.WordTrace tailWord_2650273 prefixEnd_2650273 302414203251869895199805 := by
  unfold tailWord_2650273
  simp only [CollatzResearch.WordTrace]
  refine ⟨96663397527521026437747473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64442265018347350958498315 96663397527521026437747473)
  ·
    refine ⟨72497548145640769828310605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96663397527521026437747473 72497548145640769828310605)
    ·
      refine ⟨27186580554615288685616477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72497548145640769828310605 27186580554615288685616477)
      ·
        refine ⟨10194967707980733257106179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27186580554615288685616477 10194967707980733257106179)
        ·
          refine ⟨15292451561971099885659269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194967707980733257106179 15292451561971099885659269)
          ·
            refine ⟨2867334667869581228561113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15292451561971099885659269 2867334667869581228561113)
            ·
              refine ⟨2150501000902185921420835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867334667869581228561113 2150501000902185921420835)
              ·
                refine ⟨3225751501353278882131253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150501000902185921420835 3225751501353278882131253)
                ·
                  refine ⟨302414203251869895199805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3225751501353278882131253 302414203251869895199805)
                  ·
                    rfl

theorem cell22_2650273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_2650273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650273 prefixEnd_2650273 := by exact prefixLift 2650273
  have htrace : WordTrace (prefixWord ++ tailWord_2650273) baseStart_2650273 baseEnd_2650273 := by
    simpa [prefixWord, tailWord_2650273, baseEnd_2650273] using wordTrace_append hprefix tailTrace_2650273
  have hstable : (prefixWord ++ tailWord_2650273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650273).length < 2 ^ (prefixWord ++ tailWord_2650273).sum := by decide
  have hdescent : baseEnd_2650273 < baseStart_2650273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650299 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_2650299 : Nat := 118140960795 + 2650299 * 2 ^ 59
def prefixEnd_2650299 : Nat := 4983230072969 + 3 ^ 40 * 2650299 * 2
def baseEnd_2650299 : Nat := 907251510086954284449335

theorem tailTrace_2650299 : CollatzResearch.WordTrace tailWord_2650299 prefixEnd_2650299 907251510086954284449335 := by
  unfold tailWord_2650299
  simp only [CollatzResearch.WordTrace]
  refine ⟨96664345825426832878193951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64442897216951221918795967 96664345825426832878193951)
  ·
    refine ⟨144996518738140249317290927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96664345825426832878193951 144996518738140249317290927)
    ·
      refine ⟨217494778107210373975936391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144996518738140249317290927 217494778107210373975936391)
      ·
        refine ⟨326242167160815560963904587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217494778107210373975936391 326242167160815560963904587)
        ·
          refine ⟨489363250741223341445856881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326242167160815560963904587 489363250741223341445856881)
          ·
            refine ⟨367022438055917506084392661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489363250741223341445856881 367022438055917506084392661)
            ·
              refine ⟨8602088391935566548852953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 367022438055917506084392661 8602088391935566548852953)
              ·
                refine ⟨6451566293951674911639715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8602088391935566548852953 6451566293951674911639715)
                ·
                  refine ⟨9677349440927512367459573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451566293951674911639715 9677349440927512367459573)
                  ·
                    refine ⟨907251510086954284449335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9677349440927512367459573 907251510086954284449335)
                    ·
                      rfl

theorem cell22_2650299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_2650299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650299 prefixEnd_2650299 := by exact prefixLift 2650299
  have htrace : WordTrace (prefixWord ++ tailWord_2650299) baseStart_2650299 baseEnd_2650299 := by
    simpa [prefixWord, tailWord_2650299, baseEnd_2650299] using wordTrace_append hprefix tailTrace_2650299
  have hstable : (prefixWord ++ tailWord_2650299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650299).length < 2 ^ (prefixWord ++ tailWord_2650299).sum := by decide
  have hdescent : baseEnd_2650299 < baseStart_2650299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650301 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2650301 : Nat := 118140960795 + 2650301 * 2 ^ 59
def prefixEnd_2650301 : Nat := 4983230072969 + 3 ^ 40 * 2650301 * 2
def baseEnd_2650301 : Nat := 302417398242608981966443

theorem tailTrace_2650301 : CollatzResearch.WordTrace tailWord_2650301 prefixEnd_2650301 302417398242608981966443 := by
  unfold tailWord_2650301
  simp only [CollatzResearch.WordTrace]
  refine ⟨96664418771419587219766757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64442945847613058146511171 96664418771419587219766757)
  ·
    refine ⟨18124578519641172603706267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96664418771419587219766757 18124578519641172603706267)
    ·
      refine ⟨27186867779461758905559401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18124578519641172603706267 27186867779461758905559401)
      ·
        refine ⟨20390150834596319179169551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27186867779461758905559401 20390150834596319179169551)
        ·
          refine ⟨30585226251894478768754327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390150834596319179169551 30585226251894478768754327)
          ·
            refine ⟨45877839377841718153131491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30585226251894478768754327 45877839377841718153131491)
            ·
              refine ⟨68816759066762577229697237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45877839377841718153131491 68816759066762577229697237)
              ·
                refine ⟨1612892790627247903821029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68816759066762577229697237 1612892790627247903821029)
                ·
                  refine ⟨302417398242608981966443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612892790627247903821029 302417398242608981966443)
                  ·
                    rfl

theorem cell22_2650301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2650301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650301 prefixEnd_2650301 := by exact prefixLift 2650301
  have htrace : WordTrace (prefixWord ++ tailWord_2650301) baseStart_2650301 baseEnd_2650301 := by
    simpa [prefixWord, tailWord_2650301, baseEnd_2650301] using wordTrace_append hprefix tailTrace_2650301
  have hstable : (prefixWord ++ tailWord_2650301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650301).length < 2 ^ (prefixWord ++ tailWord_2650301).sum := by decide
  have hdescent : baseEnd_2650301 < baseStart_2650301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650318 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_2650318 : Nat := 118140960795 + 2650318 * 2 ^ 59
def prefixEnd_2650318 : Nat := 4983230072969 + 3 ^ 40 * 2650318 * 2
def baseEnd_2650318 : Nat := 302419338058414856074759

theorem tailTrace_2650318 : CollatzResearch.WordTrace tailWord_2650318 prefixEnd_2650318 302419338058414856074759 := by
  unfold tailWord_2650318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083129851544749890391951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64443359208238666082090405 12083129851544749890391951)
  ·
    refine ⟨18124694777317124835587927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12083129851544749890391951 18124694777317124835587927)
    ·
      refine ⟨27187042165975687253381891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18124694777317124835587927 27187042165975687253381891)
      ·
        refine ⟨40780563248963530880072837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27187042165975687253381891 40780563248963530880072837)
        ·
          refine ⟨7646355609180662040013657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40780563248963530880072837 7646355609180662040013657)
          ·
            refine ⟨5734766706885496530010243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646355609180662040013657 5734766706885496530010243)
            ·
              refine ⟨8602150060328244795015365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734766706885496530010243 8602150060328244795015365)
              ·
                refine ⟨1612903136311545899065381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8602150060328244795015365 1612903136311545899065381)
                ·
                  refine ⟨302419338058414856074759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612903136311545899065381 302419338058414856074759)
                  ·
                    rfl

theorem cell22_2650318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_2650318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650318 prefixEnd_2650318 := by exact prefixLift 2650318
  have htrace : WordTrace (prefixWord ++ tailWord_2650318) baseStart_2650318 baseEnd_2650318 := by
    simpa [prefixWord, tailWord_2650318, baseEnd_2650318] using wordTrace_append hprefix tailTrace_2650318
  have hstable : (prefixWord ++ tailWord_2650318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650318).length < 2 ^ (prefixWord ++ tailWord_2650318).sum := by decide
  have hdescent : baseEnd_2650318 < baseStart_2650318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650329 : List Nat := [1, 2, 1, 2, 3, 1, 5, 7]
def baseStart_2650329 : Nat := 118140960795 + 2650329 * 2 ^ 59
def prefixEnd_2650329 : Nat := 4983230072969 + 3 ^ 40 * 2650329 * 2
def baseEnd_2650329 : Nat := 100806864411116022911027

theorem tailTrace_2650329 : CollatzResearch.WordTrace tailWord_2650329 prefixEnd_2650329 100806864411116022911027 := by
  unfold tailWord_2650329
  simp only [CollatzResearch.WordTrace]
  refine ⟨96665440015318148001786041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64443626676878765334524027 96665440015318148001786041)
  ·
    refine ⟨72499080011488611001339531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96665440015318148001786041 72499080011488611001339531)
    ·
      refine ⟨108748620017232916502009297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72499080011488611001339531 108748620017232916502009297)
      ·
        refine ⟨81561465012924687376506973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108748620017232916502009297 81561465012924687376506973)
        ·
          refine ⟨30585549379846757766190115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81561465012924687376506973 30585549379846757766190115)
          ·
            refine ⟨45878324069770136649285173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30585549379846757766190115 45878324069770136649285173)
            ·
              refine ⟨4301092881540950310870485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45878324069770136649285173 4301092881540950310870485)
              ·
                refine ⟨100806864411116022911027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4301092881540950310870485 100806864411116022911027)
                ·
                  rfl

theorem cell22_2650329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 7].length) (baseStart_2650329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650329 prefixEnd_2650329 := by exact prefixLift 2650329
  have htrace : WordTrace (prefixWord ++ tailWord_2650329) baseStart_2650329 baseEnd_2650329 := by
    simpa [prefixWord, tailWord_2650329, baseEnd_2650329] using wordTrace_append hprefix tailTrace_2650329
  have hstable : (prefixWord ++ tailWord_2650329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650329).length < 2 ^ (prefixWord ++ tailWord_2650329).sum := by decide
  have hdescent : baseEnd_2650329 < baseStart_2650329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650333 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2650333 : Nat := 118140960795 + 2650333 * 2 ^ 59
def prefixEnd_2650333 : Nat := 4983230072969 + 3 ^ 40 * 2650333 * 2
def baseEnd_2650333 : Nat := 907263148981789529099231

theorem tailTrace_2650333 : CollatzResearch.WordTrace tailWord_2650333 prefixEnd_2650333 907263148981789529099231 := by
  unfold tailWord_2650333
  simp only [CollatzResearch.WordTrace]
  refine ⟨96665585907303656684931653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64443723938202437789954435 96665585907303656684931653)
  ·
    refine ⟨18124797357619435628424685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96665585907303656684931653 18124797357619435628424685)
    ·
      refine ⟨6796799009107288360659257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18124797357619435628424685 6796799009107288360659257)
      ·
        refine ⟨5097599256830466270494443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6796799009107288360659257 5097599256830466270494443)
        ·
          refine ⟨7646398885245699405741665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097599256830466270494443 7646398885245699405741665)
          ·
            refine ⟨5734799163934274554306249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646398885245699405741665 5734799163934274554306249)
            ·
              refine ⟨4301099372950705915729687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734799163934274554306249 4301099372950705915729687)
              ·
                refine ⟨6451649059426058873594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301099372950705915729687 6451649059426058873594531)
                ·
                  refine ⟨9677473589139088310391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6451649059426058873594531 9677473589139088310391797)
                  ·
                    refine ⟨907263148981789529099231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9677473589139088310391797 907263148981789529099231)
                    ·
                      rfl

theorem cell22_2650333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2650333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650333 prefixEnd_2650333 := by exact prefixLift 2650333
  have htrace : WordTrace (prefixWord ++ tailWord_2650333) baseStart_2650333 baseEnd_2650333 := by
    simpa [prefixWord, tailWord_2650333, baseEnd_2650333] using wordTrace_append hprefix tailTrace_2650333
  have hstable : (prefixWord ++ tailWord_2650333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650333).length < 2 ^ (prefixWord ++ tailWord_2650333).sum := by decide
  have hdescent : baseEnd_2650333 < baseStart_2650333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650346 : List Nat := [3, 1, 3, 1, 1, 2, 5, 6]
def baseStart_2650346 : Nat := 118140960795 + 2650346 * 2 ^ 59
def prefixEnd_2650346 : Nat := 4983230072969 + 3 ^ 40 * 2650346 * 2
def baseEnd_2650346 : Nat := 100807511016384647613799

theorem tailTrace_2650346 : CollatzResearch.WordTrace tailWord_2650346 prefixEnd_2650346 100807511016384647613799 := by
  unfold tailWord_2650346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166515014064139976288723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64444040037504373270103261 24166515014064139976288723)
  ·
    refine ⟨36249772521096209964433085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166515014064139976288723 36249772521096209964433085)
    ·
      refine ⟨13593664695411078736662407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36249772521096209964433085 13593664695411078736662407)
      ·
        refine ⟨20390497043116618104993611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13593664695411078736662407 20390497043116618104993611)
        ·
          refine ⟨30585745564674927157490417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390497043116618104993611 30585745564674927157490417)
          ·
            refine ⟨22939309173506195368117813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30585745564674927157490417 22939309173506195368117813)
            ·
              refine ⟨2150560235016205815761045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22939309173506195368117813 2150560235016205815761045)
              ·
                refine ⟨100807511016384647613799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2150560235016205815761045 100807511016384647613799)
                ·
                  rfl

theorem cell22_2650346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_2650346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650346 prefixEnd_2650346 := by exact prefixLift 2650346
  have htrace : WordTrace (prefixWord ++ tailWord_2650346) baseStart_2650346 baseEnd_2650346 := by
    simpa [prefixWord, tailWord_2650346, baseEnd_2650346] using wordTrace_append hprefix tailTrace_2650346
  have hstable : (prefixWord ++ tailWord_2650346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650346).length < 2 ^ (prefixWord ++ tailWord_2650346).sum := by decide
  have hdescent : baseEnd_2650346 < baseStart_2650346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650451 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 6, 3]
def baseStart_2650451 : Nat := 118140960795 + 2650451 * 2 ^ 59
def prefixEnd_2650451 : Nat := 4983230072969 + 3 ^ 40 * 2650451 * 2
def baseEnd_2650451 : Nat := 907303542793276554648869

theorem tailTrace_2650451 : CollatzResearch.WordTrace tailWord_2650451 prefixEnd_2650451 907303542793276554648869 := by
  unfold tailWord_2650451
  simp only [CollatzResearch.WordTrace]
  refine ⟨96669889720876162837727207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64446593147250775225151471 96669889720876162837727207)
  ·
    refine ⟨145004834581314244256590811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96669889720876162837727207 145004834581314244256590811)
    ·
      refine ⟨217507251871971366384886217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145004834581314244256590811 217507251871971366384886217)
      ·
        refine ⟨163130438903978524788664663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217507251871971366384886217 163130438903978524788664663)
        ·
          refine ⟨244695658355967787182996995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163130438903978524788664663 244695658355967787182996995)
          ·
            refine ⟨367043487533951680774495493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244695658355967787182996995 367043487533951680774495493)
            ·
              refine ⟨68820653912615940145217905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367043487533951680774495493 68820653912615940145217905)
              ·
                refine ⟨51615490434461955108913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68820653912615940145217905 51615490434461955108913429)
                ·
                  refine ⟨2419476114115404145730317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51615490434461955108913429 2419476114115404145730317)
                  ·
                    refine ⟨907303542793276554648869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419476114115404145730317 907303542793276554648869)
                    ·
                      rfl

theorem cell22_2650451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].length) (baseStart_2650451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650451 prefixEnd_2650451 := by exact prefixLift 2650451
  have htrace : WordTrace (prefixWord ++ tailWord_2650451) baseStart_2650451 baseEnd_2650451 := by
    simpa [prefixWord, tailWord_2650451, baseEnd_2650451] using wordTrace_append hprefix tailTrace_2650451
  have hstable : (prefixWord ++ tailWord_2650451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650451).length < 2 ^ (prefixWord ++ tailWord_2650451).sum := by decide
  have hdescent : baseEnd_2650451 < baseStart_2650451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650485 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2650485 : Nat := 118140960795 + 2650485 * 2 ^ 59
def prefixEnd_2650485 : Nat := 4983230072969 + 3 ^ 40 * 2650485 * 2
def baseEnd_2650485 : Nat := 907315181688111799298765

theorem tailTrace_2650485 : CollatzResearch.WordTrace tailWord_2650485 prefixEnd_2650485 907315181688111799298765 := by
  unfold tailWord_2650485
  simp only [CollatzResearch.WordTrace]
  refine ⟨96671129802752986644464909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64447419868501991096309939 96671129802752986644464909)
  ·
    refine ⟨36251673676032369991674341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96671129802752986644464909 36251673676032369991674341)
    ·
      refine ⟨6797188814256069373438939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36251673676032369991674341 6797188814256069373438939)
      ·
        refine ⟨10195783221384104060158409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6797188814256069373438939 10195783221384104060158409)
        ·
          refine ⟨7646837416038078045118807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10195783221384104060158409 7646837416038078045118807)
          ·
            refine ⟨11470256124057117067678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646837416038078045118807 11470256124057117067678211)
            ·
              refine ⟨17205384186085675601517317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470256124057117067678211 17205384186085675601517317)
              ·
                refine ⟨3226009534891064175284497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17205384186085675601517317 3226009534891064175284497)
                ·
                  refine ⟨2419507151168298131463373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3226009534891064175284497 2419507151168298131463373)
                  ·
                    refine ⟨907315181688111799298765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419507151168298131463373 907315181688111799298765)
                    ·
                      rfl

theorem cell22_2650485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2650485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650485 prefixEnd_2650485 := by exact prefixLift 2650485
  have htrace : WordTrace (prefixWord ++ tailWord_2650485) baseStart_2650485 baseEnd_2650485 := by
    simpa [prefixWord, tailWord_2650485, baseEnd_2650485] using wordTrace_append hprefix tailTrace_2650485
  have hstable : (prefixWord ++ tailWord_2650485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650485).length < 2 ^ (prefixWord ++ tailWord_2650485).sum := by decide
  have hdescent : baseEnd_2650485 < baseStart_2650485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650558 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2650558 : Nat := 118140960795 + 2650558 * 2 ^ 59
def prefixEnd_2650558 : Nat := 4983230072969 + 3 ^ 40 * 2650558 * 2
def baseEnd_2650558 : Nat := 907340171079963942223541

theorem tailTrace_2650558 : CollatzResearch.WordTrace tailWord_2650558 prefixEnd_2650558 907340171079963942223541 := by
  unfold tailWord_2650558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084224041436065013984041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64449194887659013407914885 12084224041436065013984041)
  ·
    refine ⟨9063168031077048760488031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12084224041436065013984041 9063168031077048760488031)
    ·
      refine ⟨13594752046615573140732047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063168031077048760488031 13594752046615573140732047)
      ·
        refine ⟨20392128069923359711098071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13594752046615573140732047 20392128069923359711098071)
        ·
          refine ⟨30588192104885039566647107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20392128069923359711098071 30588192104885039566647107)
          ·
            refine ⟨45882288157327559349970661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30588192104885039566647107 45882288157327559349970661)
            ·
              refine ⟨8602929029498917378119499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45882288157327559349970661 8602929029498917378119499)
              ·
                refine ⟨12904393544248376067179249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602929029498917378119499 12904393544248376067179249)
                ·
                  refine ⟨9678295158186282050384437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12904393544248376067179249 9678295158186282050384437)
                  ·
                    refine ⟨907340171079963942223541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9678295158186282050384437 907340171079963942223541)
                    ·
                      rfl

theorem cell22_2650558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2650558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650558 prefixEnd_2650558 := by exact prefixLift 2650558
  have htrace : WordTrace (prefixWord ++ tailWord_2650558) baseStart_2650558 baseEnd_2650558 := by
    simpa [prefixWord, tailWord_2650558, baseEnd_2650558] using wordTrace_append hprefix tailTrace_2650558
  have hstable : (prefixWord ++ tailWord_2650558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650558).length < 2 ^ (prefixWord ++ tailWord_2650558).sum := by decide
  have hdescent : baseEnd_2650558 < baseStart_2650558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650601 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2650601 : Nat := 118140960795 + 2650601 * 2 ^ 59
def prefixEnd_2650601 : Nat := 4983230072969 + 3 ^ 40 * 2650601 * 2
def baseEnd_2650601 : Nat := 907354890858726163398409

theorem tailTrace_2650601 : CollatzResearch.WordTrace tailWord_2650601 prefixEnd_2650601 907354890858726163398409 := by
  unfold tailWord_2650601
  simp only [CollatzResearch.WordTrace]
  refine ⟨96675360670332738455687657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64450240446888492303791771 96675360670332738455687657)
  ·
    refine ⟨72506520502749553841765743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96675360670332738455687657 72506520502749553841765743)
    ·
      refine ⟨108759780754124330762648615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72506520502749553841765743 108759780754124330762648615)
      ·
        refine ⟨163139671131186496143972923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108759780754124330762648615 163139671131186496143972923)
        ·
          refine ⟨244709506696779744215959385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163139671131186496143972923 244709506696779744215959385)
          ·
            refine ⟨183532130022584808161969539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244709506696779744215959385 183532130022584808161969539)
            ·
              refine ⟨275298195033877212242954309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183532130022584808161969539 275298195033877212242954309)
              ·
                refine ⟨51618411568851977295553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275298195033877212242954309 51618411568851977295553933)
                ·
                  refine ⟨19356904338319491485832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51618411568851977295553933 19356904338319491485832725)
                  ·
                    refine ⟨907354890858726163398409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19356904338319491485832725 907354890858726163398409)
                    ·
                      rfl

theorem cell22_2650601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2650601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650601 prefixEnd_2650601 := by exact prefixLift 2650601
  have htrace : WordTrace (prefixWord ++ tailWord_2650601) baseStart_2650601 baseEnd_2650601 := by
    simpa [prefixWord, tailWord_2650601, baseEnd_2650601] using wordTrace_append hprefix tailTrace_2650601
  have hstable : (prefixWord ++ tailWord_2650601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650601).length < 2 ^ (prefixWord ++ tailWord_2650601).sum := by decide
  have hdescent : baseEnd_2650601 < baseStart_2650601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650603 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 4, 3]
def baseStart_2650603 : Nat := 118140960795 + 2650603 * 2 ^ 59
def prefixEnd_2650603 : Nat := 4983230072969 + 3 ^ 40 * 2650603 * 2
def baseEnd_2650603 : Nat := 907355575499598824848403

theorem tailTrace_2650603 : CollatzResearch.WordTrace tailWord_2650603 prefixEnd_2650603 907355575499598824848403 := by
  unfold tailWord_2650603
  simp only [CollatzResearch.WordTrace]
  refine ⟨96675433616325492797260463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64450289077550328531506975 96675433616325492797260463)
  ·
    refine ⟨145013150424488239195890695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96675433616325492797260463 145013150424488239195890695)
    ·
      refine ⟨217519725636732358793836043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145013150424488239195890695 217519725636732358793836043)
      ·
        refine ⟨326279588455098538190754065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217519725636732358793836043 326279588455098538190754065)
        ·
          refine ⟨244709691341323903643065549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326279588455098538190754065 244709691341323903643065549)
          ·
            refine ⟨91766134252996463866149581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244709691341323903643065549 91766134252996463866149581)
            ·
              refine ⟨34412300344873673949806093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91766134252996463866149581 34412300344873673949806093)
              ·
                refine ⟨12904612629327627731177285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34412300344873673949806093 12904612629327627731177285)
                ·
                  refine ⟨2419614867998930199595741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12904612629327627731177285 2419614867998930199595741)
                  ·
                    refine ⟨907355575499598824848403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419614867998930199595741 907355575499598824848403)
                    ·
                      rfl

theorem cell22_2650603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].length) (baseStart_2650603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650603 prefixEnd_2650603 := by exact prefixLift 2650603
  have htrace : WordTrace (prefixWord ++ tailWord_2650603) baseStart_2650603 baseEnd_2650603 := by
    simpa [prefixWord, tailWord_2650603, baseEnd_2650603] using wordTrace_append hprefix tailTrace_2650603
  have hstable : (prefixWord ++ tailWord_2650603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650603).length < 2 ^ (prefixWord ++ tailWord_2650603).sum := by decide
  have hdescent : baseEnd_2650603 < baseStart_2650603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650605 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2650605 : Nat := 118140960795 + 2650605 * 2 ^ 59
def prefixEnd_2650605 : Nat := 4983230072969 + 3 ^ 40 * 2650605 * 2
def baseEnd_2650605 : Nat := 302452086713490495432799

theorem tailTrace_2650605 : CollatzResearch.WordTrace tailWord_2650605 prefixEnd_2650605 302452086713490495432799 := by
  unfold tailWord_2650605
  simp only [CollatzResearch.WordTrace]
  refine ⟨96675506562318247138833269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64450337708212164759222179 96675506562318247138833269)
  ·
    refine ⟨9063328740217335669265619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96675506562318247138833269 9063328740217335669265619)
    ·
      refine ⟨13594993110326003503898429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063328740217335669265619 13594993110326003503898429)
      ·
        refine ⟨5098122416372251313961911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13594993110326003503898429 5098122416372251313961911)
        ·
          refine ⟨7647183624558376970942867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098122416372251313961911 7647183624558376970942867)
          ·
            refine ⟨11470775436837565456414301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7647183624558376970942867 11470775436837565456414301)
            ·
              refine ⟨4301540788814087046155363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11470775436837565456414301 4301540788814087046155363)
              ·
                refine ⟨6452311183221130569233045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301540788814087046155363 6452311183221130569233045)
                ·
                  refine ⟨302452086713490495432799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6452311183221130569233045 302452086713490495432799)
                  ·
                    rfl

theorem cell22_2650605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2650605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650605 prefixEnd_2650605 := by exact prefixLift 2650605
  have htrace : WordTrace (prefixWord ++ tailWord_2650605) baseStart_2650605 baseEnd_2650605 := by
    simpa [prefixWord, tailWord_2650605, baseEnd_2650605] using wordTrace_append hprefix tailTrace_2650605
  have hstable : (prefixWord ++ tailWord_2650605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650605).length < 2 ^ (prefixWord ++ tailWord_2650605).sum := by decide
  have hdescent : baseEnd_2650605 < baseStart_2650605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650635 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_2650635 : Nat := 118140960795 + 2650635 * 2 ^ 59
def prefixEnd_2650635 : Nat := 4983230072969 + 3 ^ 40 * 2650635 * 2
def baseEnd_2650635 : Nat := 907366529753561408048305

theorem tailTrace_2650635 : CollatzResearch.WordTrace tailWord_2650635 prefixEnd_2650635 907366529753561408048305 := by
  unfold tailWord_2650635
  simp only [CollatzResearch.WordTrace]
  refine ⟨96676600752209562262425359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64451067168139708174950239 96676600752209562262425359)
  ·
    refine ⟨145014901128314343393638039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96676600752209562262425359 145014901128314343393638039)
    ·
      refine ⟨217522351692471515090457059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145014901128314343393638039 217522351692471515090457059)
      ·
        refine ⟨326283527538707272635685589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217522351692471515090457059 326283527538707272635685589)
        ·
          refine ⟨7647270176688451702398881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 326283527538707272635685589 7647270176688451702398881)
          ·
            refine ⟨5735452632516338776799161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7647270176688451702398881 5735452632516338776799161)
            ·
              refine ⟨4301589474387254082599371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5735452632516338776799161 4301589474387254082599371)
              ·
                refine ⟨6452384211580881123899057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301589474387254082599371 6452384211580881123899057)
                ·
                  refine ⟨4839288158685660842924293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452384211580881123899057 4839288158685660842924293)
                  ·
                    refine ⟨907366529753561408048305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839288158685660842924293 907366529753561408048305)
                    ·
                      rfl

theorem cell22_2650635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_2650635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650635 prefixEnd_2650635 := by exact prefixLift 2650635
  have htrace : WordTrace (prefixWord ++ tailWord_2650635) baseStart_2650635 baseEnd_2650635 := by
    simpa [prefixWord, tailWord_2650635, baseEnd_2650635] using wordTrace_append hprefix tailTrace_2650635
  have hstable : (prefixWord ++ tailWord_2650635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650635).length < 2 ^ (prefixWord ++ tailWord_2650635).sum := by decide
  have hdescent : baseEnd_2650635 < baseStart_2650635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650637 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2650637 : Nat := 118140960795 + 2650637 * 2 ^ 59
def prefixEnd_2650637 : Nat := 4983230072969 + 3 ^ 40 * 2650637 * 2
def baseEnd_2650637 : Nat := 907367214394434069498299

theorem tailTrace_2650637 : CollatzResearch.WordTrace tailWord_2650637 prefixEnd_2650637 907367214394434069498299 := by
  unfold tailWord_2650637
  simp only [CollatzResearch.WordTrace]
  refine ⟨96676673698202316603998165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64451115798801544402665443 96676673698202316603998165)
  ·
    refine ⟨2265859539801616795406207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 96676673698202316603998165 2265859539801616795406207)
    ·
      refine ⟨3398789309702425193109311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265859539801616795406207 3398789309702425193109311)
      ·
        refine ⟨5098183964553637789663967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398789309702425193109311 5098183964553637789663967)
        ·
          refine ⟨7647275946830456684495951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098183964553637789663967 7647275946830456684495951)
          ·
            refine ⟨11470913920245685026743927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7647275946830456684495951 11470913920245685026743927)
            ·
              refine ⟨17206370880368527540115891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470913920245685026743927 17206370880368527540115891)
              ·
                refine ⟨25809556320552791310173837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17206370880368527540115891 25809556320552791310173837)
                ·
                  refine ⟨9678583620207296741315189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25809556320552791310173837 9678583620207296741315189)
                  ·
                    refine ⟨907367214394434069498299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9678583620207296741315189 907367214394434069498299)
                    ·
                      rfl

theorem cell22_2650637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2650637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650637 prefixEnd_2650637 := by exact prefixLift 2650637
  have htrace : WordTrace (prefixWord ++ tailWord_2650637) baseStart_2650637 baseEnd_2650637 := by
    simpa [prefixWord, tailWord_2650637, baseEnd_2650637] using wordTrace_append hprefix tailTrace_2650637
  have hstable : (prefixWord ++ tailWord_2650637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650637).length < 2 ^ (prefixWord ++ tailWord_2650637).sum := by decide
  have hdescent : baseEnd_2650637 < baseStart_2650637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650656 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_2650656 : Nat := 118140960795 + 2650656 * 2 ^ 59
def prefixEnd_2650656 : Nat := 4983230072969 + 3 ^ 40 * 2650656 * 2
def baseEnd_2650656 : Nat := 302457906160908117757747

theorem tailTrace_2650656 : CollatzResearch.WordTrace tailWord_2650656 prefixEnd_2650656 302457906160908117757747 := by
  unfold tailWord_2650656
  simp only [CollatzResearch.WordTrace]
  refine ⟨48338683342566741424469911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64451577790088988565959881 48338683342566741424469911)
  ·
    refine ⟨72508025013850112136704867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48338683342566741424469911 72508025013850112136704867)
    ·
      refine ⟨108762037520775168205057301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72508025013850112136704867 108762037520775168205057301)
      ·
        refine ⟨5098220508786336009612061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108762037520775168205057301 5098220508786336009612061)
        ·
          refine ⟨1911832690794876003604523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5098220508786336009612061 1911832690794876003604523)
          ·
            refine ⟨2867749036192314005406785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911832690794876003604523 2867749036192314005406785)
            ·
              refine ⟨2150811777144235504055089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867749036192314005406785 2150811777144235504055089)
              ·
                refine ⟨1613108832858176628041317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150811777144235504055089 1613108832858176628041317)
                ·
                  refine ⟨302457906160908117757747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613108832858176628041317 302457906160908117757747)
                  ·
                    rfl

theorem cell22_2650656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_2650656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650656 prefixEnd_2650656 := by exact prefixLift 2650656
  have htrace : WordTrace (prefixWord ++ tailWord_2650656) baseStart_2650656 baseEnd_2650656 := by
    simpa [prefixWord, tailWord_2650656, baseEnd_2650656] using wordTrace_append hprefix tailTrace_2650656
  have hstable : (prefixWord ++ tailWord_2650656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650656).length < 2 ^ (prefixWord ++ tailWord_2650656).sum := by decide
  have hdescent : baseEnd_2650656 < baseStart_2650656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650686 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_2650686 : Nat := 118140960795 + 2650686 * 2 ^ 59
def prefixEnd_2650686 : Nat := 4983230072969 + 3 ^ 40 * 2650686 * 2
def baseEnd_2650686 : Nat := 907383988095814275023149

theorem tailTrace_2650686 : CollatzResearch.WordTrace tailWord_2650686 prefixEnd_2650686 907383988095814275023149 := by
  unfold tailWord_2650686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084807609378099746566489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64452307250016531981687941 12084807609378099746566489)
  ·
    refine ⟨9063605707033574809924867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12084807609378099746566489 9063605707033574809924867)
    ·
      refine ⟨13595408560550362214887301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063605707033574809924867 13595408560550362214887301)
      ·
        refine ⟨2549139105103192915291369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13595408560550362214887301 2549139105103192915291369)
        ·
          refine ⟨1911854328827394686468527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2549139105103192915291369 1911854328827394686468527)
          ·
            refine ⟨2867781493241092029702791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911854328827394686468527 2867781493241092029702791)
            ·
              refine ⟨4301672239861638044554187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867781493241092029702791 4301672239861638044554187)
              ·
                refine ⟨6452508359792457066831281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301672239861638044554187 6452508359792457066831281)
                ·
                  refine ⟨4839381269844342800123461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452508359792457066831281 4839381269844342800123461)
                  ·
                    refine ⟨907383988095814275023149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839381269844342800123461 907383988095814275023149)
                    ·
                      rfl

theorem cell22_2650686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_2650686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650686 prefixEnd_2650686 := by exact prefixLift 2650686
  have htrace : WordTrace (prefixWord ++ tailWord_2650686) baseStart_2650686 baseEnd_2650686 := by
    simpa [prefixWord, tailWord_2650686, baseEnd_2650686] using wordTrace_append hprefix tailTrace_2650686
  have hstable : (prefixWord ++ tailWord_2650686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650686).length < 2 ^ (prefixWord ++ tailWord_2650686).sum := by decide
  have hdescent : baseEnd_2650686 < baseStart_2650686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650755 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 4, 3]
def baseStart_2650755 : Nat := 118140960795 + 2650755 * 2 ^ 59
def prefixEnd_2650755 : Nat := 4983230072969 + 3 ^ 40 * 2650755 * 2
def baseEnd_2650755 : Nat := 907407608205921095047937

theorem tailTrace_2650755 : CollatzResearch.WordTrace tailWord_2650755 prefixEnd_2650755 907407608205921095047937 := by
  unfold tailWord_2650755
  simp only [CollatzResearch.WordTrace]
  refine ⟨96680977511774822756793719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64453985007849881837862479 96680977511774822756793719)
  ·
    refine ⟨145021466267662234135190579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96680977511774822756793719 145021466267662234135190579)
    ·
      refine ⟨217532199401493351202785869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145021466267662234135190579 217532199401493351202785869)
      ·
        refine ⟨81574574775560006701044701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217532199401493351202785869 81574574775560006701044701)
        ·
          refine ⟨30590465540835002512891763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81574574775560006701044701 30590465540835002512891763)
          ·
            refine ⟨45885698311252503769337645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30590465540835002512891763 45885698311252503769337645)
            ·
              refine ⟨17207136866719688913501617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45885698311252503769337645 17207136866719688913501617)
              ·
                refine ⟨12905352650039766685126213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17207136866719688913501617 12905352650039766685126213)
                ·
                  refine ⟨2419753621882456253461165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12905352650039766685126213 2419753621882456253461165)
                  ·
                    refine ⟨907407608205921095047937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419753621882456253461165 907407608205921095047937)
                    ·
                      rfl

theorem cell22_2650755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].length) (baseStart_2650755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650755 prefixEnd_2650755 := by exact prefixLift 2650755
  have htrace : WordTrace (prefixWord ++ tailWord_2650755) baseStart_2650755 baseEnd_2650755 := by
    simpa [prefixWord, tailWord_2650755, baseEnd_2650755] using wordTrace_append hprefix tailTrace_2650755
  have hstable : (prefixWord ++ tailWord_2650755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650755).length < 2 ^ (prefixWord ++ tailWord_2650755).sum := by decide
  have hdescent : baseEnd_2650755 < baseStart_2650755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650757 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 4]
def baseStart_2650757 : Nat := 118140960795 + 2650757 * 2 ^ 59
def prefixEnd_2650757 : Nat := 4983230072969 + 3 ^ 40 * 2650757 * 2
def baseEnd_2650757 : Nat := 302469430948931252165977

theorem tailTrace_2650757 : CollatzResearch.WordTrace tailWord_2650757 prefixEnd_2650757 302469430948931252165977 := by
  unfold tailWord_2650757
  simp only [CollatzResearch.WordTrace]
  refine ⟨96681050457767577098366525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64454033638511718065577683 96681050457767577098366525)
  ·
    refine ⟨36255393921662841411887447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96681050457767577098366525 36255393921662841411887447)
    ·
      refine ⟨54383090882494262117831171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36255393921662841411887447 54383090882494262117831171)
      ·
        refine ⟨81574636323741393176746757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54383090882494262117831171 81574636323741393176746757)
        ·
          refine ⟨15295244310701511220640017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81574636323741393176746757 15295244310701511220640017)
          ·
            refine ⟨11471433233026133415480013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15295244310701511220640017 11471433233026133415480013)
            ·
              refine ⟨4301787462384800030805005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11471433233026133415480013 4301787462384800030805005)
              ·
                refine ⟨1613170298394300011551877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301787462384800030805005 1613170298394300011551877)
                ·
                  refine ⟨302469430948931252165977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613170298394300011551877 302469430948931252165977)
                  ·
                    rfl

theorem cell22_2650757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_2650757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650757 prefixEnd_2650757 := by exact prefixLift 2650757
  have htrace : WordTrace (prefixWord ++ tailWord_2650757) baseStart_2650757 baseEnd_2650757 := by
    simpa [prefixWord, tailWord_2650757, baseEnd_2650757] using wordTrace_append hprefix tailTrace_2650757
  have hstable : (prefixWord ++ tailWord_2650757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650757).length < 2 ^ (prefixWord ++ tailWord_2650757).sum := by decide
  have hdescent : baseEnd_2650757 < baseStart_2650757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650800 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_2650800 : Nat := 118140960795 + 2650800 * 2 ^ 59
def prefixEnd_2650800 : Nat := 4983230072969 + 3 ^ 40 * 2650800 * 2
def baseEnd_2650800 : Nat := 907423012625555977672799

theorem tailTrace_2650800 : CollatzResearch.WordTrace tailWord_2650800 prefixEnd_2650800 907423012625555977672799 := by
  unfold tailWord_2650800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48341309398305897721090927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64455079197741196961454569 48341309398305897721090927)
  ·
    refine ⟨72511964097458846581636391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48341309398305897721090927 72511964097458846581636391)
    ·
      refine ⟨108767946146188269872454587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72511964097458846581636391 108767946146188269872454587)
      ·
        refine ⟨163151919219282404808681881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108767946146188269872454587 163151919219282404808681881)
        ·
          refine ⟨122363939414461803606511411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163151919219282404808681881 122363939414461803606511411)
          ·
            refine ⟨183545909121692705409767117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122363939414461803606511411 183545909121692705409767117)
            ·
              refine ⟨68829715920634764528662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183545909121692705409767117 68829715920634764528662669)
              ·
                refine ⟨25811143470238036698248501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68829715920634764528662669 25811143470238036698248501)
                ·
                  refine ⟨2419794700334815940460797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25811143470238036698248501 2419794700334815940460797)
                  ·
                    refine ⟨907423012625555977672799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419794700334815940460797 907423012625555977672799)
                    ·
                      rfl

theorem cell22_2650800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_2650800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650800 prefixEnd_2650800 := by exact prefixLift 2650800
  have htrace : WordTrace (prefixWord ++ tailWord_2650800) baseStart_2650800 baseEnd_2650800 := by
    simpa [prefixWord, tailWord_2650800, baseEnd_2650800] using wordTrace_append hprefix tailTrace_2650800
  have hstable : (prefixWord ++ tailWord_2650800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650800).length < 2 ^ (prefixWord ++ tailWord_2650800).sum := by decide
  have hdescent : baseEnd_2650800 < baseStart_2650800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650877 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_2650877 : Nat := 118140960795 + 2650877 * 2 ^ 59
def prefixEnd_2650877 : Nat := 4983230072969 + 3 ^ 40 * 2650877 * 2
def baseEnd_2650877 : Nat := 907449371299153443497563

theorem tailTrace_2650877 : CollatzResearch.WordTrace tailWord_2650877 prefixEnd_2650877 907449371299153443497563 := by
  unfold tailWord_2650877
  simp only [CollatzResearch.WordTrace]
  refine ⟨96685427217332837592734885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64456951478221891728489923 96685427217332837592734885)
  ·
    refine ⟨18128517603249907048637791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96685427217332837592734885 18128517603249907048637791)
    ·
      refine ⟨27192776404874860572956687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18128517603249907048637791 27192776404874860572956687)
      ·
        refine ⟨40789164607312290859435031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27192776404874860572956687 40789164607312290859435031)
        ·
          refine ⟨61183746910968436289152547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40789164607312290859435031 61183746910968436289152547)
          ·
            refine ⟨91775620366452654433728821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61183746910968436289152547 91775620366452654433728821)
            ·
              refine ⟨8603964409354936353162077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91775620366452654433728821 8603964409354936353162077)
              ·
                refine ⟨3226486653508101132435779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8603964409354936353162077 3226486653508101132435779)
                ·
                  refine ⟨4839729980262151698653669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226486653508101132435779 4839729980262151698653669)
                  ·
                    refine ⟨907449371299153443497563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839729980262151698653669 907449371299153443497563)
                    ·
                      rfl

theorem cell22_2650877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_2650877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650877 prefixEnd_2650877 := by exact prefixLift 2650877
  have htrace : WordTrace (prefixWord ++ tailWord_2650877) baseStart_2650877 baseEnd_2650877 := by
    simpa [prefixWord, tailWord_2650877, baseEnd_2650877] using wordTrace_append hprefix tailTrace_2650877
  have hstable : (prefixWord ++ tailWord_2650877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650877).length < 2 ^ (prefixWord ++ tailWord_2650877).sum := by decide
  have hdescent : baseEnd_2650877 < baseStart_2650877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650905 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2650905 : Nat := 118140960795 + 2650905 * 2 ^ 59
def prefixEnd_2650905 : Nat := 4983230072969 + 3 ^ 40 * 2650905 * 2
def baseEnd_2650905 : Nat := 907458956271370703797477

theorem tailTrace_2650905 : CollatzResearch.WordTrace tailWord_2650905 prefixEnd_2650905 907458956271370703797477 := by
  unfold tailWord_2650905
  simp only [CollatzResearch.WordTrace]
  refine ⟨96686448461231398374754169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64457632307487598916502779 96686448461231398374754169)
  ·
    refine ⟨72514836345923548781065627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96686448461231398374754169 72514836345923548781065627)
    ·
      refine ⟨108772254518885323171598441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72514836345923548781065627 108772254518885323171598441)
      ·
        refine ⟨81579190889163992378698831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108772254518885323171598441 81579190889163992378698831)
        ·
          refine ⟨122368786333745988568048247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81579190889163992378698831 122368786333745988568048247)
          ·
            refine ⟨183553179500618982852072371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122368786333745988568048247 183553179500618982852072371)
            ·
              refine ⟨275329769250928474278108557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183553179500618982852072371 275329769250928474278108557)
              ·
                refine ⟨103248663469098177854290709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275329769250928474278108557 103248663469098177854290709)
                ·
                  refine ⟨4839781100113977086919877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103248663469098177854290709 4839781100113977086919877)
                  ·
                    refine ⟨907458956271370703797477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839781100113977086919877 907458956271370703797477)
                    ·
                      rfl

theorem cell22_2650905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2650905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650905 prefixEnd_2650905 := by exact prefixLift 2650905
  have htrace : WordTrace (prefixWord ++ tailWord_2650905) baseStart_2650905 baseEnd_2650905 := by
    simpa [prefixWord, tailWord_2650905, baseEnd_2650905] using wordTrace_append hprefix tailTrace_2650905
  have hstable : (prefixWord ++ tailWord_2650905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650905).length < 2 ^ (prefixWord ++ tailWord_2650905).sum := by decide
  have hdescent : baseEnd_2650905 < baseStart_2650905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2650926 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_2650926 : Nat := 118140960795 + 2650926 * 2 ^ 59
def prefixEnd_2650926 : Nat := 4983230072969 + 3 ^ 40 * 2650926 * 2
def baseEnd_2650926 : Nat := 302488715000177883007471

theorem tailTrace_2650926 : CollatzResearch.WordTrace tailWord_2650926 prefixEnd_2650926 302488715000177883007471 := by
  unfold tailWord_2650926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085901799269414870158579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64458142929436879307512421 12085901799269414870158579)
  ·
    refine ⟨18128852698904122305237869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12085901799269414870158579 18128852698904122305237869)
    ·
      refine ⟨6798319762089045864464201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18128852698904122305237869 6798319762089045864464201)
      ·
        refine ⟨5098739821566784398348151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6798319762089045864464201 5098739821566784398348151)
        ·
          refine ⟨7648109732350176597522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5098739821566784398348151 7648109732350176597522227)
          ·
            refine ⟨11472164598525264896283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648109732350176597522227 11472164598525264896283341)
            ·
              refine ⟨4302061724446974336106253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11472164598525264896283341 4302061724446974336106253)
              ·
                refine ⟨1613273146667615376039845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4302061724446974336106253 1613273146667615376039845)
                ·
                  refine ⟨302488715000177883007471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613273146667615376039845 302488715000177883007471)
                  ·
                    rfl

theorem cell22_2650926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_2650926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2650926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2650926 prefixEnd_2650926 := by exact prefixLift 2650926
  have htrace : WordTrace (prefixWord ++ tailWord_2650926) baseStart_2650926 baseEnd_2650926 := by
    simpa [prefixWord, tailWord_2650926, baseEnd_2650926] using wordTrace_append hprefix tailTrace_2650926
  have hstable : (prefixWord ++ tailWord_2650926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2650926).length < 2 ^ (prefixWord ++ tailWord_2650926).sum := by decide
  have hdescent : baseEnd_2650926 < baseStart_2650926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2650926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651059 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 2, 3]
def baseStart_2651059 : Nat := 118140960795 + 2651059 * 2 ^ 59
def prefixEnd_2651059 : Nat := 4983230072969 + 3 ^ 40 * 2651059 * 2
def baseEnd_2651059 : Nat := 907511673618565635447005

theorem tailTrace_2651059 : CollatzResearch.WordTrace tailWord_2651059 prefixEnd_2651059 907511673618565635447005 := by
  unfold tailWord_2651059
  simp only [CollatzResearch.WordTrace]
  refine ⟨96692065302673482675860231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64461376868448988450573487 96692065302673482675860231)
  ·
    refine ⟨145038097954010224013790347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96692065302673482675860231 145038097954010224013790347)
    ·
      refine ⟨217557146931015336020685521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145038097954010224013790347 217557146931015336020685521)
      ·
        refine ⟨163167860198261502015514141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217557146931015336020685521 163167860198261502015514141)
        ·
          refine ⟨61187947574348063255817803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163167860198261502015514141 61187947574348063255817803)
          ·
            refine ⟨91781921361522094883726705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61187947574348063255817803 91781921361522094883726705)
            ·
              refine ⟨68836441021141571162795029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91781921361522094883726705 68836441021141571162795029)
              ·
                refine ⟨3226708172866011148256017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68836441021141571162795029 3226708172866011148256017)
                ·
                  refine ⟨2420031129649508361192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3226708172866011148256017 2420031129649508361192013)
                  ·
                    refine ⟨907511673618565635447005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420031129649508361192013 907511673618565635447005)
                    ·
                      rfl

theorem cell22_2651059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].length) (baseStart_2651059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651059 prefixEnd_2651059 := by exact prefixLift 2651059
  have htrace : WordTrace (prefixWord ++ tailWord_2651059) baseStart_2651059 baseEnd_2651059 := by
    simpa [prefixWord, tailWord_2651059, baseEnd_2651059] using wordTrace_append hprefix tailTrace_2651059
  have hstable : (prefixWord ++ tailWord_2651059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651059).length < 2 ^ (prefixWord ++ tailWord_2651059).sum := by decide
  have hdescent : baseEnd_2651059 < baseStart_2651059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651106 : List Nat := [3, 3, 3, 1, 1, 3, 8]
def baseStart_2651106 : Nat := 118140960795 + 2651106 * 2 ^ 59
def prefixEnd_2651106 : Nat := 4983230072969 + 3 ^ 40 * 2651106 * 2
def baseEnd_2651106 : Nat := 33612139358484191834143

theorem tailTrace_2651106 : CollatzResearch.WordTrace tailWord_2651106 prefixEnd_2651106 33612139358484191834143 := by
  unfold tailWord_2651106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24173444883375802425705293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64462519689002139801880781 24173444883375802425705293)
  ·
    refine ⟨9065041831265925909639485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24173444883375802425705293 9065041831265925909639485)
    ·
      refine ⟨3399390686724722216114807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9065041831265925909639485 3399390686724722216114807)
      ·
        refine ⟨5099086030087083324172211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399390686724722216114807 5099086030087083324172211)
        ·
          refine ⟨7648629045130624986258317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099086030087083324172211 7648629045130624986258317)
          ·
            refine ⟨2868235891923984369846869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7648629045130624986258317 2868235891923984369846869)
            ·
              refine ⟨33612139358484191834143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2868235891923984369846869 33612139358484191834143)
              ·
                rfl

theorem cell22_2651106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 8].length) (baseStart_2651106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651106 prefixEnd_2651106 := by exact prefixLift 2651106
  have htrace : WordTrace (prefixWord ++ tailWord_2651106) baseStart_2651106 baseEnd_2651106 := by
    simpa [prefixWord, tailWord_2651106, baseEnd_2651106] using wordTrace_append hprefix tailTrace_2651106
  have hstable : (prefixWord ++ tailWord_2651106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651106).length < 2 ^ (prefixWord ++ tailWord_2651106).sum := by decide
  have hdescent : baseEnd_2651106 < baseStart_2651106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651121 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2651121 : Nat := 118140960795 + 2651121 * 2 ^ 59
def prefixEnd_2651121 : Nat := 4983230072969 + 3 ^ 40 * 2651121 * 2
def baseEnd_2651121 : Nat := 907532897485618140396815

theorem tailTrace_2651121 : CollatzResearch.WordTrace tailWord_2651121 prefixEnd_2651121 907532897485618140396815 := by
  unfold tailWord_2651121
  simp only [CollatzResearch.WordTrace]
  refine ⟨96694326628448867264617217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64462884418965911509744811 96694326628448867264617217)
  ·
    refine ⟨72520744971336650448462913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96694326628448867264617217 72520744971336650448462913)
    ·
      refine ⟨54390558728502487836347185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72520744971336650448462913 54390558728502487836347185)
      ·
        refine ⟨40792919046376865877260389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54390558728502487836347185 40792919046376865877260389)
        ·
          refine ⟨7648672321195662351986323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40792919046376865877260389 7648672321195662351986323)
          ·
            refine ⟨11473008481793493527979485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648672321195662351986323 11473008481793493527979485)
            ·
              refine ⟨4302378180672560072992307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11473008481793493527979485 4302378180672560072992307)
              ·
                refine ⟨6453567271008840109488461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302378180672560072992307 6453567271008840109488461)
                ·
                  refine ⟨2420087726628315041058173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453567271008840109488461 2420087726628315041058173)
                  ·
                    refine ⟨907532897485618140396815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420087726628315041058173 907532897485618140396815)
                    ·
                      rfl

theorem cell22_2651121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2651121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651121 prefixEnd_2651121 := by exact prefixLift 2651121
  have htrace : WordTrace (prefixWord ++ tailWord_2651121) baseStart_2651121 baseEnd_2651121 := by
    simpa [prefixWord, tailWord_2651121, baseEnd_2651121] using wordTrace_append hprefix tailTrace_2651121
  have hstable : (prefixWord ++ tailWord_2651121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651121).length < 2 ^ (prefixWord ++ tailWord_2651121).sum := by decide
  have hdescent : baseEnd_2651121 < baseStart_2651121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651168 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_2651168 : Nat := 118140960795 + 2651168 * 2 ^ 59
def prefixEnd_2651168 : Nat := 4983230072969 + 3 ^ 40 * 2651168 * 2
def baseEnd_2651168 : Nat := 302516328848708561490557

theorem tailTrace_2651168 : CollatzResearch.WordTrace tailWord_2651168 prefixEnd_2651168 302516328848708561490557 := by
  unfold tailWord_2651168
  simp only [CollatzResearch.WordTrace]
  refine ⟨48348020429639297145789079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64464027239519062861052105 48348020429639297145789079)
  ·
    refine ⟨72522030644458945718683619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48348020429639297145789079 72522030644458945718683619)
    ·
      refine ⟨108783045966688418578025429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72522030644458945718683619 108783045966688418578025429)
      ·
        refine ⟨2549602639844259810422471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108783045966688418578025429 2549602639844259810422471)
        ·
          refine ⟨3824403959766389715633707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549602639844259810422471 3824403959766389715633707)
          ·
            refine ⟨5736605939649584573450561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824403959766389715633707 5736605939649584573450561)
            ·
              refine ⟨4302454454737188430087921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736605939649584573450561 4302454454737188430087921)
              ·
                refine ⟨3226840841052891322565941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302454454737188430087921 3226840841052891322565941)
                ·
                  refine ⟨302516328848708561490557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3226840841052891322565941 302516328848708561490557)
                  ·
                    rfl

theorem cell22_2651168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_2651168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651168 prefixEnd_2651168 := by exact prefixLift 2651168
  have htrace : WordTrace (prefixWord ++ tailWord_2651168) baseStart_2651168 baseEnd_2651168 := by
    simpa [prefixWord, tailWord_2651168, baseEnd_2651168] using wordTrace_append hprefix tailTrace_2651168
  have hstable : (prefixWord ++ tailWord_2651168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651168).length < 2 ^ (prefixWord ++ tailWord_2651168).sum := by decide
  have hdescent : baseEnd_2651168 < baseStart_2651168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651172 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2651172 : Nat := 118140960795 + 2651172 * 2 ^ 59
def prefixEnd_2651172 : Nat := 4983230072969 + 3 ^ 40 * 2651172 * 2
def baseEnd_2651172 : Nat := 907550355827871007371659

theorem tailTrace_2651172 : CollatzResearch.WordTrace tailWord_2651172 prefixEnd_2651172 907550355827871007371659 := by
  unfold tailWord_2651172
  simp only [CollatzResearch.WordTrace]
  refine ⟨48348093375632051487361885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64464124500842735316482513 48348093375632051487361885)
  ·
    refine ⟨18130535015862019307760707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48348093375632051487361885 18130535015862019307760707)
    ·
      refine ⟨27195802523793028961641061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130535015862019307760707 27195802523793028961641061)
      ·
        refine ⟨5099212973211192930307699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27195802523793028961641061 5099212973211192930307699)
        ·
          refine ⟨7648819459816789395461549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099212973211192930307699 7648819459816789395461549)
          ·
            refine ⟨2868307297431296023298081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7648819459816789395461549 2868307297431296023298081)
            ·
              refine ⟨2151230473073472017473561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868307297431296023298081 2151230473073472017473561)
              ·
                refine ⟨1613422854805104013105171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151230473073472017473561 1613422854805104013105171)
                ·
                  refine ⟨2420134282207656019657757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613422854805104013105171 2420134282207656019657757)
                  ·
                    refine ⟨907550355827871007371659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420134282207656019657757 907550355827871007371659)
                    ·
                      rfl

theorem cell22_2651172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2651172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651172 prefixEnd_2651172 := by exact prefixLift 2651172
  have htrace : WordTrace (prefixWord ++ tailWord_2651172) baseStart_2651172 baseEnd_2651172 := by
    simpa [prefixWord, tailWord_2651172, baseEnd_2651172] using wordTrace_append hprefix tailTrace_2651172
  have hstable : (prefixWord ++ tailWord_2651172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651172).length < 2 ^ (prefixWord ++ tailWord_2651172).sum := by decide
  have hdescent : baseEnd_2651172 < baseStart_2651172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651194 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2651194 : Nat := 118140960795 + 2651194 * 2 ^ 59
def prefixEnd_2651194 : Nat := 4983230072969 + 3 ^ 40 * 2651194 * 2
def baseEnd_2651194 : Nat := 907557886877470283321591

theorem tailTrace_2651194 : CollatzResearch.WordTrace tailWord_2651194 prefixEnd_2651194 907557886877470283321591 := by
  unfold tailWord_2651194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174247289296100183006159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64464659438122933821349757 24174247289296100183006159)
  ·
    refine ⟨36261370933944150274509239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24174247289296100183006159 36261370933944150274509239)
    ·
      refine ⟨54392056400916225411763859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36261370933944150274509239 54392056400916225411763859)
      ·
        refine ⟨81588084601374338117645789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54392056400916225411763859 81588084601374338117645789)
        ·
          refine ⟨30595531725515376794117171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81588084601374338117645789 30595531725515376794117171)
          ·
            refine ⟨45893297588273065191175757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30595531725515376794117171 45893297588273065191175757)
            ·
              refine ⟨17209986595602399446690909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45893297588273065191175757 17209986595602399446690909)
              ·
                refine ⟨6453744973350899792509091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17209986595602399446690909 6453744973350899792509091)
                ·
                  refine ⟨9680617460026349688763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6453744973350899792509091 9680617460026349688763637)
                  ·
                    refine ⟨907557886877470283321591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9680617460026349688763637 907557886877470283321591)
                    ·
                      rfl

theorem cell22_2651194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2651194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651194 prefixEnd_2651194 := by exact prefixLift 2651194
  have htrace : WordTrace (prefixWord ++ tailWord_2651194) baseStart_2651194 baseEnd_2651194 := by
    simpa [prefixWord, tailWord_2651194, baseEnd_2651194] using wordTrace_append hprefix tailTrace_2651194
  have hstable : (prefixWord ++ tailWord_2651194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651194).length < 2 ^ (prefixWord ++ tailWord_2651194).sum := by decide
  have hdescent : baseEnd_2651194 < baseStart_2651194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651209 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2651209 : Nat := 118140960795 + 2651209 * 2 ^ 59
def prefixEnd_2651209 : Nat := 4983230072969 + 3 ^ 40 * 2651209 * 2
def baseEnd_2651209 : Nat := 907563021684015244196545

theorem tailTrace_2651209 : CollatzResearch.WordTrace tailWord_2651209 prefixEnd_2651209 907563021684015244196545 := by
  unfold tailWord_2651209
  simp only [CollatzResearch.WordTrace]
  refine ⟨96697536252130058293820681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64465024168086705529213787 96697536252130058293820681)
  ·
    refine ⟨72523152189097543720365511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96697536252130058293820681 72523152189097543720365511)
    ·
      refine ⟨108784728283646315580548267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72523152189097543720365511 108784728283646315580548267)
      ·
        refine ⟨163177092425469473370822401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108784728283646315580548267 163177092425469473370822401)
        ·
          refine ⟨122382819319102105028116801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163177092425469473370822401 122382819319102105028116801)
          ·
            refine ⟨91787114489326578771087601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122382819319102105028116801 91787114489326578771087601)
            ·
              refine ⟨68840335866994934078315701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91787114489326578771087601 68840335866994934078315701)
              ·
                refine ⟨6453781487530775069842097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68840335866994934078315701 6453781487530775069842097)
                ·
                  refine ⟨4840336115648081302381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6453781487530775069842097 4840336115648081302381573)
                  ·
                    refine ⟨907563021684015244196545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4840336115648081302381573 907563021684015244196545)
                    ·
                      rfl

theorem cell22_2651209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2651209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651209 prefixEnd_2651209 := by exact prefixLift 2651209
  have htrace : WordTrace (prefixWord ++ tailWord_2651209) baseStart_2651209 baseEnd_2651209 := by
    simpa [prefixWord, tailWord_2651209, baseEnd_2651209] using wordTrace_append hprefix tailTrace_2651209
  have hstable : (prefixWord ++ tailWord_2651209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651209).length < 2 ^ (prefixWord ++ tailWord_2651209).sum := by decide
  have hdescent : baseEnd_2651209 < baseStart_2651209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651213 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2651213 : Nat := 118140960795 + 2651213 * 2 ^ 59
def prefixEnd_2651213 : Nat := 4983230072969 + 3 ^ 40 * 2651213 * 2
def baseEnd_2651213 : Nat := 302521463655253522365511

theorem tailTrace_2651213 : CollatzResearch.WordTrace tailWord_2651213 prefixEnd_2651213 302521463655253522365511 := by
  unfold tailWord_2651213
  simp only [CollatzResearch.WordTrace]
  refine ⟨96697682144115566976966293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64465121429410377984644195 96697682144115566976966293)
  ·
    refine ⟨4532703850505417202045295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96697682144115566976966293 4532703850505417202045295)
    ·
      refine ⟨6799055775758125803067943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532703850505417202045295 6799055775758125803067943)
      ·
        refine ⟨10198583663637188704601915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799055775758125803067943 10198583663637188704601915)
        ·
          refine ⟨15297875495455783056902873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10198583663637188704601915 15297875495455783056902873)
          ·
            refine ⟨11473406621591837292677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15297875495455783056902873 11473406621591837292677155)
            ·
              refine ⟨17210109932387755939015733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473406621591837292677155 17210109932387755939015733)
              ·
                refine ⟨1613447806161352119282725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17210109932387755939015733 1613447806161352119282725)
                ·
                  refine ⟨302521463655253522365511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613447806161352119282725 302521463655253522365511)
                  ·
                    rfl

theorem cell22_2651213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2651213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651213 prefixEnd_2651213 := by exact prefixLift 2651213
  have htrace : WordTrace (prefixWord ++ tailWord_2651213) baseStart_2651213 baseEnd_2651213 := by
    simpa [prefixWord, tailWord_2651213, baseEnd_2651213] using wordTrace_append hprefix tailTrace_2651213
  have hstable : (prefixWord ++ tailWord_2651213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651213).length < 2 ^ (prefixWord ++ tailWord_2651213).sum := by decide
  have hdescent : baseEnd_2651213 < baseStart_2651213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651230 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2651230 : Nat := 118140960795 + 2651230 * 2 ^ 59
def prefixEnd_2651230 : Nat := 4983230072969 + 3 ^ 40 * 2651230 * 2
def baseEnd_2651230 : Nat := 302523403471059396473827

theorem tailTrace_2651230 : CollatzResearch.WordTrace tailWord_2651230 prefixEnd_2651230 302523403471059396473827 := by
  unfold tailWord_2651230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087287773131747360041893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64465534790035985920223429 12087287773131747360041893)
  ·
    refine ⟨2266366457462202630007855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12087287773131747360041893 2266366457462202630007855)
    ·
      refine ⟨3399549686193303945011783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266366457462202630007855 3399549686193303945011783)
      ·
        refine ⟨5099324529289955917517675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399549686193303945011783 5099324529289955917517675)
        ·
          refine ⟨7648986793934933876276513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099324529289955917517675 7648986793934933876276513)
          ·
            refine ⟨5736740095451200407207385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7648986793934933876276513 5736740095451200407207385)
            ·
              refine ⟨4302555071588400305405539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736740095451200407207385 4302555071588400305405539)
              ·
                refine ⟨6453832607382600458108309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302555071588400305405539 6453832607382600458108309)
                ·
                  refine ⟨302523403471059396473827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6453832607382600458108309 302523403471059396473827)
                  ·
                    rfl

theorem cell22_2651230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2651230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651230 prefixEnd_2651230 := by exact prefixLift 2651230
  have htrace : WordTrace (prefixWord ++ tailWord_2651230) baseStart_2651230 baseEnd_2651230 := by
    simpa [prefixWord, tailWord_2651230, baseEnd_2651230] using wordTrace_append hprefix tailTrace_2651230
  have hstable : (prefixWord ++ tailWord_2651230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651230).length < 2 ^ (prefixWord ++ tailWord_2651230).sum := by decide
  have hdescent : baseEnd_2651230 < baseStart_2651230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651245 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2651245 : Nat := 118140960795 + 2651245 * 2 ^ 59
def prefixEnd_2651245 : Nat := 4983230072969 + 3 ^ 40 * 2651245 * 2
def baseEnd_2651245 : Nat := 907575345219723150296435

theorem tailTrace_2651245 : CollatzResearch.WordTrace tailWord_2651245 prefixEnd_2651245 907575345219723150296435 := by
  unfold tailWord_2651245
  simp only [CollatzResearch.WordTrace]
  refine ⟨96698849279999636442131189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64465899519999757628087459 96698849279999636442131189)
  ·
    refine ⟨9065517119999965916449799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96698849279999636442131189 9065517119999965916449799)
    ·
      refine ⟨13598275679999948874674699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9065517119999965916449799 13598275679999948874674699)
      ·
        refine ⟨20397413519999923312012049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13598275679999948874674699 20397413519999923312012049)
        ·
          refine ⟨15298060139999942484009037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20397413519999923312012049 15298060139999942484009037)
          ·
            refine ⟨5736772552499978431503389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15298060139999942484009037 5736772552499978431503389)
            ·
              refine ⟨2151289707187491911813771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5736772552499978431503389 2151289707187491911813771)
              ·
                refine ⟨3226934560781237867720657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151289707187491911813771 3226934560781237867720657)
                ·
                  refine ⟨2420200920585928400790493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3226934560781237867720657 2420200920585928400790493)
                  ·
                    refine ⟨907575345219723150296435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420200920585928400790493 907575345219723150296435)
                    ·
                      rfl

theorem cell22_2651245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2651245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651245 prefixEnd_2651245 := by exact prefixLift 2651245
  have htrace : WordTrace (prefixWord ++ tailWord_2651245) baseStart_2651245 baseEnd_2651245 := by
    simpa [prefixWord, tailWord_2651245, baseEnd_2651245] using wordTrace_append hprefix tailTrace_2651245
  have hstable : (prefixWord ++ tailWord_2651245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651245).length < 2 ^ (prefixWord ++ tailWord_2651245).sum := by decide
  have hdescent : baseEnd_2651245 < baseStart_2651245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651256 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_2651256 : Nat := 118140960795 + 2651256 * 2 ^ 59
def prefixEnd_2651256 : Nat := 4983230072969 + 3 ^ 40 * 2651256 * 2
def baseEnd_2651256 : Nat := 907579110744522788271401

theorem tailTrace_2651256 : CollatzResearch.WordTrace tailWord_2651256 prefixEnd_2651256 907579110744522788271401 := by
  unfold tailWord_2651256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48349625241479892660390811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64466166988639856880521081 48349625241479892660390811)
  ·
    refine ⟨72524437862219838990586217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48349625241479892660390811 72524437862219838990586217)
    ·
      refine ⟨54393328396664879242939663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72524437862219838990586217 54393328396664879242939663)
      ·
        refine ⟨81589992594997318864409495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54393328396664879242939663 81589992594997318864409495)
        ·
          refine ⟨122384988892495978296614243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81589992594997318864409495 122384988892495978296614243)
          ·
            refine ⟨183577483338743967444921365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122384988892495978296614243 183577483338743967444921365)
            ·
              refine ⟨8605194531503623473980689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183577483338743967444921365 8605194531503623473980689)
              ·
                refine ⟨6453895898627717605485517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8605194531503623473980689 6453895898627717605485517)
                ·
                  refine ⟨2420210961985394102057069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453895898627717605485517 2420210961985394102057069)
                  ·
                    refine ⟨907579110744522788271401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420210961985394102057069 907579110744522788271401)
                    ·
                      rfl

theorem cell22_2651256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_2651256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651256 prefixEnd_2651256 := by exact prefixLift 2651256
  have htrace : WordTrace (prefixWord ++ tailWord_2651256) baseStart_2651256 baseEnd_2651256 := by
    simpa [prefixWord, tailWord_2651256, baseEnd_2651256] using wordTrace_append hprefix tailTrace_2651256
  have hstable : (prefixWord ++ tailWord_2651256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651256).length < 2 ^ (prefixWord ++ tailWord_2651256).sum := by decide
  have hdescent : baseEnd_2651256 < baseStart_2651256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651290 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_2651290 : Nat := 118140960795 + 2651290 * 2 ^ 59
def prefixEnd_2651290 : Nat := 4983230072969 + 3 ^ 40 * 2651290 * 2
def baseEnd_2651290 : Nat := 907590749639358032921297

theorem tailTrace_2651290 : CollatzResearch.WordTrace tailWord_2651290 prefixEnd_2651290 907590749639358032921297 := by
  unfold tailWord_2651290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175122641209152281879831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64466993709891072751679549 24175122641209152281879831)
  ·
    refine ⟨36262683961813728422819747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24175122641209152281879831 36262683961813728422819747)
    ·
      refine ⟨54394025942720592634229621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36262683961813728422819747 54394025942720592634229621)
      ·
        refine ⟨5099439932130055559459027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54394025942720592634229621 5099439932130055559459027)
        ·
          refine ⟨7649159898195083339188541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099439932130055559459027 7649159898195083339188541)
          ·
            refine ⟨2868434961823156252195703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7649159898195083339188541 2868434961823156252195703)
            ·
              refine ⟨4302652442734734378293555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868434961823156252195703 4302652442734734378293555)
              ·
                refine ⟨6453978664102101567440333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4302652442734734378293555 6453978664102101567440333)
                ·
                  refine ⟨2420241999038288087790125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6453978664102101567440333 2420241999038288087790125)
                  ·
                    refine ⟨907590749639358032921297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420241999038288087790125 907590749639358032921297)
                    ·
                      rfl

theorem cell22_2651290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_2651290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651290 prefixEnd_2651290 := by exact prefixLift 2651290
  have htrace : WordTrace (prefixWord ++ tailWord_2651290) baseStart_2651290 baseEnd_2651290 := by
    simpa [prefixWord, tailWord_2651290, baseEnd_2651290] using wordTrace_append hprefix tailTrace_2651290
  have hstable : (prefixWord ++ tailWord_2651290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651290).length < 2 ^ (prefixWord ++ tailWord_2651290).sum := by decide
  have hdescent : baseEnd_2651290 < baseStart_2651290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651303 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 5]
def baseStart_2651303 : Nat := 118140960795 + 2651303 * 2 ^ 59
def prefixEnd_2651303 : Nat := 4983230072969 + 3 ^ 40 * 2651303 * 2
def baseEnd_2651303 : Nat := 302531733268343444115419

theorem tailTrace_2651303 : CollatzResearch.WordTrace tailWord_2651303 prefixEnd_2651303 302531733268343444115419 := by
  unfold tailWord_2651303
  simp only [CollatzResearch.WordTrace]
  refine ⟨96700964713789512347742563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64467309809193008231828375 96700964713789512347742563)
  ·
    refine ⟨145051447070684268521613845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96700964713789512347742563 145051447070684268521613845)
    ·
      refine ⟨6799286581438325086950649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145051447070684268521613845 6799286581438325086950649)
      ·
        refine ⟨5099464936078743815212987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6799286581438325086950649 5099464936078743815212987)
        ·
          refine ⟨7649197404118115722819481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099464936078743815212987 7649197404118115722819481)
          ·
            refine ⟨5736898053088586792114611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7649197404118115722819481 5736898053088586792114611)
            ·
              refine ⟨8605347079632880188171917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736898053088586792114611 8605347079632880188171917)
              ·
                refine ⟨3227005154862330070564469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8605347079632880188171917 3227005154862330070564469)
                ·
                  refine ⟨302531733268343444115419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227005154862330070564469 302531733268343444115419)
                  ·
                    rfl

theorem cell22_2651303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].length) (baseStart_2651303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651303 prefixEnd_2651303 := by exact prefixLift 2651303
  have htrace : WordTrace (prefixWord ++ tailWord_2651303) baseStart_2651303 baseEnd_2651303 := by
    simpa [prefixWord, tailWord_2651303, baseEnd_2651303] using wordTrace_append hprefix tailTrace_2651303
  have hstable : (prefixWord ++ tailWord_2651303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651303).length < 2 ^ (prefixWord ++ tailWord_2651303).sum := by decide
  have hdescent : baseEnd_2651303 < baseStart_2651303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651346 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2651346 : Nat := 118140960795 + 2651346 * 2 ^ 59
def prefixEnd_2651346 : Nat := 4983230072969 + 3 ^ 40 * 2651346 * 2
def baseEnd_2651346 : Nat := 907609919583792553521125

theorem tailTrace_2651346 : CollatzResearch.WordTrace tailWord_2651346 prefixEnd_2651346 907609919583792553521125 := by
  unfold tailWord_2651346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175633263158432672889473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64468355368422487127705261 24175633263158432672889473)
  ·
    refine ⟨18131724947368824504667105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24175633263158432672889473 18131724947368824504667105)
    ·
      refine ⟨13598793710526618378500329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18131724947368824504667105 13598793710526618378500329)
      ·
        refine ⟨10199095282894963783875247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13598793710526618378500329 10199095282894963783875247)
        ·
          refine ⟨15298642924342445675812871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199095282894963783875247 15298642924342445675812871)
          ·
            refine ⟨22947964386513668513719307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15298642924342445675812871 22947964386513668513719307)
            ·
              refine ⟨34421946579770502770578961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22947964386513668513719307 34421946579770502770578961)
              ·
                refine ⟨25816459934827877077934221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34421946579770502770578961 25816459934827877077934221)
                ·
                  refine ⟨9681172475560453904225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25816459934827877077934221 9681172475560453904225333)
                  ·
                    refine ⟨907609919583792553521125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9681172475560453904225333 907609919583792553521125)
                    ·
                      rfl

theorem cell22_2651346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2651346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651346 prefixEnd_2651346 := by exact prefixLift 2651346
  have htrace : WordTrace (prefixWord ++ tailWord_2651346) baseStart_2651346 baseEnd_2651346 := by
    simpa [prefixWord, tailWord_2651346, baseEnd_2651346] using wordTrace_append hprefix tailTrace_2651346
  have hstable : (prefixWord ++ tailWord_2651346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651346).length < 2 ^ (prefixWord ++ tailWord_2651346).sum := by decide
  have hdescent : baseEnd_2651346 < baseStart_2651346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651378 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2651378 : Nat := 118140960795 + 2651378 * 2 ^ 59
def prefixEnd_2651378 : Nat := 4983230072969 + 3 ^ 40 * 2651378 * 2
def baseEnd_2651378 : Nat := 907620873837755136721027

theorem tailTrace_2651378 : CollatzResearch.WordTrace tailWord_2651378 prefixEnd_2651378 907620873837755136721027 := by
  unfold tailWord_2651378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175925047129450039180697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64469133459011866771148525 24175925047129450039180697)
  ·
    refine ⟨18131943785347087529385523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24175925047129450039180697 18131943785347087529385523)
    ·
      refine ⟨27197915678020631294078285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18131943785347087529385523 27197915678020631294078285)
      ·
        refine ⟨10199218379257736735279357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27197915678020631294078285 10199218379257736735279357)
        ·
          refine ⟨3824706892221651275729759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10199218379257736735279357 3824706892221651275729759)
          ·
            refine ⟨5737060338332476913594639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824706892221651275729759 5737060338332476913594639)
            ·
              refine ⟨8605590507498715370391959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737060338332476913594639 8605590507498715370391959)
              ·
                refine ⟨12908385761248073055587939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8605590507498715370391959 12908385761248073055587939)
                ·
                  refine ⟨19362578641872109583381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12908385761248073055587939 19362578641872109583381909)
                  ·
                    refine ⟨907620873837755136721027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19362578641872109583381909 907620873837755136721027)
                    ·
                      rfl

theorem cell22_2651378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2651378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651378 prefixEnd_2651378 := by exact prefixLift 2651378
  have htrace : WordTrace (prefixWord ++ tailWord_2651378) baseStart_2651378 baseEnd_2651378 := by
    simpa [prefixWord, tailWord_2651378, baseEnd_2651378] using wordTrace_append hprefix tailTrace_2651378
  have hstable : (prefixWord ++ tailWord_2651378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651378).length < 2 ^ (prefixWord ++ tailWord_2651378).sum := by decide
  have hdescent : baseEnd_2651378 < baseStart_2651378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651442 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_2651442 : Nat := 118140960795 + 2651442 * 2 ^ 59
def prefixEnd_2651442 : Nat := 4983230072969 + 3 ^ 40 * 2651442 * 2
def baseEnd_2651442 : Nat := 907642782345680303120831

theorem tailTrace_2651442 : CollatzResearch.WordTrace tailWord_2651442 prefixEnd_2651442 907642782345680303120831 := by
  unfold tailWord_2651442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24176508615071484771763145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64470689640190626058035053 24176508615071484771763145)
  ·
    refine ⟨18132381461303613578822359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24176508615071484771763145 18132381461303613578822359)
    ·
      refine ⟨27198572191955420368233539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18132381461303613578822359 27198572191955420368233539)
      ·
        refine ⟨40797858287933130552350309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27198572191955420368233539 40797858287933130552350309)
        ·
          refine ⟨7649598428987461978565683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40797858287933130552350309 7649598428987461978565683)
          ·
            refine ⟨11474397643481192967848525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649598428987461978565683 11474397643481192967848525)
            ·
              refine ⟨4302899116305447362943197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11474397643481192967848525 4302899116305447362943197)
              ·
                refine ⟨1613587168614542761103699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4302899116305447362943197 1613587168614542761103699)
                ·
                  refine ⟨2420380752921814141655549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613587168614542761103699 2420380752921814141655549)
                  ·
                    refine ⟨907642782345680303120831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420380752921814141655549 907642782345680303120831)
                    ·
                      rfl

theorem cell22_2651442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_2651442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651442 prefixEnd_2651442 := by exact prefixLift 2651442
  have htrace : WordTrace (prefixWord ++ tailWord_2651442) baseStart_2651442 baseEnd_2651442 := by
    simpa [prefixWord, tailWord_2651442, baseEnd_2651442] using wordTrace_append hprefix tailTrace_2651442
  have hstable : (prefixWord ++ tailWord_2651442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651442).length < 2 ^ (prefixWord ++ tailWord_2651442).sum := by decide
  have hdescent : baseEnd_2651442 < baseStart_2651442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651513 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_2651513 : Nat := 118140960795 + 2651513 * 2 ^ 59
def prefixEnd_2651513 : Nat := 4983230072969 + 3 ^ 40 * 2651513 * 2
def baseEnd_2651513 : Nat := 907667087096659784595613

theorem tailTrace_2651513 : CollatzResearch.WordTrace tailWord_2651513 prefixEnd_2651513 907667087096659784595613 := by
  unfold tailWord_2651513
  simp only [CollatzResearch.WordTrace]
  refine ⟨96708624043028718212887193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64472416028685812141924795 96708624043028718212887193)
  ·
    refine ⟨72531468032271538659665395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96708624043028718212887193 72531468032271538659665395)
    ·
      refine ⟨108797202048407307989498093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72531468032271538659665395 108797202048407307989498093)
      ·
        refine ⟨40798950768152740496061785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108797202048407307989498093 40798950768152740496061785)
        ·
          refine ⟨30599213076114555372046339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40798950768152740496061785 30599213076114555372046339)
          ·
            refine ⟨45898819614171833058069509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30599213076114555372046339 45898819614171833058069509)
            ·
              refine ⟨8606028677657218698388033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45898819614171833058069509 8606028677657218698388033)
              ·
                refine ⟨6454521508242914023791025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8606028677657218698388033 6454521508242914023791025)
                ·
                  refine ⟨4840891131182185517843269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6454521508242914023791025 4840891131182185517843269)
                  ·
                    refine ⟨907667087096659784595613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4840891131182185517843269 907667087096659784595613)
                    ·
                      rfl

theorem cell22_2651513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_2651513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651513 prefixEnd_2651513 := by exact prefixLift 2651513
  have htrace : WordTrace (prefixWord ++ tailWord_2651513) baseStart_2651513 baseEnd_2651513 := by
    simpa [prefixWord, tailWord_2651513, baseEnd_2651513] using wordTrace_append hprefix tailTrace_2651513
  have hstable : (prefixWord ++ tailWord_2651513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651513).length < 2 ^ (prefixWord ++ tailWord_2651513).sum := by decide
  have hdescent : baseEnd_2651513 < baseStart_2651513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651515 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 2, 3]
def baseStart_2651515 : Nat := 118140960795 + 2651515 * 2 ^ 59
def prefixEnd_2651515 : Nat := 4983230072969 + 3 ^ 40 * 2651515 * 2
def baseEnd_2651515 : Nat := 907667771737532446045607

theorem tailTrace_2651515 : CollatzResearch.WordTrace tailWord_2651515 prefixEnd_2651515 907667771737532446045607 := by
  unfold tailWord_2651515
  simp only [CollatzResearch.WordTrace]
  refine ⟨96708696989021472554459999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64472464659347648369639999 96708696989021472554459999)
  ·
    refine ⟨145063045483532208831689999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96708696989021472554459999 145063045483532208831689999)
    ·
      refine ⟨217594568225298313247534999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145063045483532208831689999 217594568225298313247534999)
      ·
        refine ⟨326391852337947469871302499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217594568225298313247534999 326391852337947469871302499)
        ·
          refine ⟨489587778506921204806953749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326391852337947469871302499 489587778506921204806953749)
          ·
            refine ⟨22949427117511931475325957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 489587778506921204806953749 22949427117511931475325957)
            ·
              refine ⟨4303017584533487151623617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22949427117511931475325957 4303017584533487151623617)
              ·
                refine ⟨3227263188400115363717713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303017584533487151623617 3227263188400115363717713)
                ·
                  refine ⟨2420447391300086522788285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227263188400115363717713 2420447391300086522788285)
                  ·
                    refine ⟨907667771737532446045607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420447391300086522788285 907667771737532446045607)
                    ·
                      rfl

theorem cell22_2651515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].length) (baseStart_2651515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651515 prefixEnd_2651515 := by exact prefixLift 2651515
  have htrace : WordTrace (prefixWord ++ tailWord_2651515) baseStart_2651515 baseEnd_2651515 := by
    simpa [prefixWord, tailWord_2651515, baseEnd_2651515] using wordTrace_append hprefix tailTrace_2651515
  have hstable : (prefixWord ++ tailWord_2651515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651515).length < 2 ^ (prefixWord ++ tailWord_2651515).sum := by decide
  have hdescent : baseEnd_2651515 < baseStart_2651515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651528 : List Nat := [2, 1, 3, 3, 1, 2, 3, 7]
def baseStart_2651528 : Nat := 118140960795 + 2651528 * 2 ^ 59
def prefixEnd_2651528 : Nat := 4983230072969 + 3 ^ 40 * 2651528 * 2
def baseEnd_2651528 : Nat := 100852469100356082830063

theorem tailTrace_2651528 : CollatzResearch.WordTrace tailWord_2651528 prefixEnd_2651528 100852469100356082830063 := by
  unfold tailWord_2651528
  simp only [CollatzResearch.WordTrace]
  refine ⟨48354585568987187887341619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64472780758649583849788825 48354585568987187887341619)
  ·
    refine ⟨72531878353480781831012429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48354585568987187887341619 72531878353480781831012429)
    ·
      refine ⟨27199454382555293186629661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72531878353480781831012429 27199454382555293186629661)
      ·
        refine ⟨10199795393458234944986123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27199454382555293186629661 10199795393458234944986123)
        ·
          refine ⟨15299693090187352417479185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199795393458234944986123 15299693090187352417479185)
          ·
            refine ⟨11474769817640514313109389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15299693090187352417479185 11474769817640514313109389)
            ·
              refine ⟨4303038681615192867416021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11474769817640514313109389 4303038681615192867416021)
              ·
                refine ⟨100852469100356082830063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4303038681615192867416021 100852469100356082830063)
                ·
                  rfl

theorem cell22_2651528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_2651528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651528 prefixEnd_2651528 := by exact prefixLift 2651528
  have htrace : WordTrace (prefixWord ++ tailWord_2651528) baseStart_2651528 baseEnd_2651528 := by
    simpa [prefixWord, tailWord_2651528, baseEnd_2651528] using wordTrace_append hprefix tailTrace_2651528
  have hstable : (prefixWord ++ tailWord_2651528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651528).length < 2 ^ (prefixWord ++ tailWord_2651528).sum := by decide
  have hdescent : baseEnd_2651528 < baseStart_2651528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651577 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_2651577 : Nat := 118140960795 + 2651577 * 2 ^ 59
def prefixEnd_2651577 : Nat := 4983230072969 + 3 ^ 40 * 2651577 * 2
def baseEnd_2651577 : Nat := 907688995604584950995417

theorem tailTrace_2651577 : CollatzResearch.WordTrace tailWord_2651577 prefixEnd_2651577 907688995604584950995417 := by
  unfold tailWord_2651577
  simp only [CollatzResearch.WordTrace]
  refine ⟨96710958314796857143216985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64473972209864571428811323 96710958314796857143216985)
  ·
    refine ⟨72533218736097642857412739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96710958314796857143216985 72533218736097642857412739)
    ·
      refine ⟨108799828104146464286119109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72533218736097642857412739 108799828104146464286119109)
      ·
        refine ⟨20399967769527462053647333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108799828104146464286119109 20399967769527462053647333)
        ·
          refine ⟨3824993956786399135058875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20399967769527462053647333 3824993956786399135058875)
          ·
            refine ⟨5737490935179598702588313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824993956786399135058875 5737490935179598702588313)
            ·
              refine ⟨4303118201384699026941235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5737490935179598702588313 4303118201384699026941235)
              ·
                refine ⟨6454677302077048540411853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303118201384699026941235 6454677302077048540411853)
                ·
                  refine ⟨2420503988278893202654445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6454677302077048540411853 2420503988278893202654445)
                  ·
                    refine ⟨907688995604584950995417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420503988278893202654445 907688995604584950995417)
                    ·
                      rfl

theorem cell22_2651577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_2651577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651577 prefixEnd_2651577 := by exact prefixLift 2651577
  have htrace : WordTrace (prefixWord ++ tailWord_2651577) baseStart_2651577 baseEnd_2651577 := by
    simpa [prefixWord, tailWord_2651577, baseEnd_2651577] using wordTrace_append hprefix tailTrace_2651577
  have hstable : (prefixWord ++ tailWord_2651577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651577).length < 2 ^ (prefixWord ++ tailWord_2651577).sum := by decide
  have hdescent : baseEnd_2651577 < baseStart_2651577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651665 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2651665 : Nat := 118140960795 + 2651665 * 2 ^ 59
def prefixEnd_2651665 : Nat := 4983230072969 + 3 ^ 40 * 2651665 * 2
def baseEnd_2651665 : Nat := 907719119802982054795147

theorem tailTrace_2651665 : CollatzResearch.WordTrace tailWord_2651665 prefixEnd_2651665 907719119802982054795147 := by
  unfold tailWord_2651665
  simp only [CollatzResearch.WordTrace]
  refine ⟨96714167938478048172420449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64476111958985365448280299 96714167938478048172420449)
  ·
    refine ⟨72535625953858536129315337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96714167938478048172420449 72535625953858536129315337)
    ·
      refine ⟨54401719465393902096986503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72535625953858536129315337 54401719465393902096986503)
      ·
        refine ⟨81602579198090853145479755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54401719465393902096986503 81602579198090853145479755)
        ·
          refine ⟨122403868797136279718219633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81602579198090853145479755 122403868797136279718219633)
          ·
            refine ⟨91802901597852209788664725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122403868797136279718219633 91802901597852209788664725)
            ·
              refine ⟨4303261012399322333843659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91802901597852209788664725 4303261012399322333843659)
              ·
                refine ⟨6454891518598983500765489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303261012399322333843659 6454891518598983500765489)
                ·
                  refine ⟨4841168638949237625574117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6454891518598983500765489 4841168638949237625574117)
                  ·
                    refine ⟨907719119802982054795147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4841168638949237625574117 907719119802982054795147)
                    ·
                      rfl

theorem cell22_2651665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2651665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651665 prefixEnd_2651665 := by exact prefixLift 2651665
  have htrace : WordTrace (prefixWord ++ tailWord_2651665) baseStart_2651665 baseEnd_2651665 := by
    simpa [prefixWord, tailWord_2651665, baseEnd_2651665] using wordTrace_append hprefix tailTrace_2651665
  have hstable : (prefixWord ++ tailWord_2651665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651665).length < 2 ^ (prefixWord ++ tailWord_2651665).sum := by decide
  have hdescent : baseEnd_2651665 < baseStart_2651665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_2651723 : Nat := 118140960795 + 2651723 * 2 ^ 59
def prefixEnd_2651723 : Nat := 4983230072969 + 3 ^ 40 * 2651723 * 2
def baseEnd_2651723 : Nat := 907738974388289236844969

theorem tailTrace_2651723 : CollatzResearch.WordTrace tailWord_2651723 prefixEnd_2651723 907738974388289236844969 := by
  unfold tailWord_2651723
  simp only [CollatzResearch.WordTrace]
  refine ⟨96716283372267924078031823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64477522248178616052021215 96716283372267924078031823)
  ·
    refine ⟨145074425058401886117047735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96716283372267924078031823 145074425058401886117047735)
    ·
      refine ⟨217611637587602829175571603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145074425058401886117047735 217611637587602829175571603)
      ·
        refine ⟨326417456381404243763357405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217611637587602829175571603 326417456381404243763357405)
        ·
          refine ⟨122406546143026591411259027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326417456381404243763357405 122406546143026591411259027)
          ·
            refine ⟨183609819214539887116888541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122406546143026591411259027 183609819214539887116888541)
            ·
              refine ⟨68853682205452457668833203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183609819214539887116888541 68853682205452457668833203)
              ·
                refine ⟨103280523308178686503249805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68853682205452457668833203 103280523308178686503249805)
                ·
                  refine ⟨38730196240567007438718677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103280523308178686503249805 38730196240567007438718677)
                  ·
                    refine ⟨907738974388289236844969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38730196240567007438718677 907738974388289236844969)
                    ·
                      rfl

theorem cell22_2651723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_2651723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651723 prefixEnd_2651723 := by exact prefixLift 2651723
  have htrace : WordTrace (prefixWord ++ tailWord_2651723) baseStart_2651723 baseEnd_2651723 := by
    simpa [prefixWord, tailWord_2651723, baseEnd_2651723] using wordTrace_append hprefix tailTrace_2651723
  have hstable : (prefixWord ++ tailWord_2651723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651723).length < 2 ^ (prefixWord ++ tailWord_2651723).sum := by decide
  have hdescent : baseEnd_2651723 < baseStart_2651723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651729 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_2651729 : Nat := 118140960795 + 2651729 * 2 ^ 59
def prefixEnd_2651729 : Nat := 4983230072969 + 3 ^ 40 * 2651729 * 2
def baseEnd_2651729 : Nat := 907741028310907221194951

theorem tailTrace_2651729 : CollatzResearch.WordTrace tailWord_2651729 prefixEnd_2651729 907741028310907221194951 := by
  unfold tailWord_2651729
  simp only [CollatzResearch.WordTrace]
  refine ⟨96716502210246187102750241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64477668140164124735166827 96716502210246187102750241)
  ·
    refine ⟨72537376657684640327062681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96716502210246187102750241 72537376657684640327062681)
    ·
      refine ⟨54403032493263480245297011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72537376657684640327062681 54403032493263480245297011)
      ·
        refine ⟨81604548739895220367945517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54403032493263480245297011 81604548739895220367945517)
        ·
          refine ⟨30601705777460707637979569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81604548739895220367945517 30601705777460707637979569)
          ·
            refine ⟨22951279333095530728484677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30601705777460707637979569 22951279333095530728484677)
            ·
              refine ⟨4303364874955412011590877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22951279333095530728484677 4303364874955412011590877)
              ·
                refine ⟨1613761828108279504346579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4303364874955412011590877 1613761828108279504346579)
                ·
                  refine ⟨2420642742162419256519869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613761828108279504346579 2420642742162419256519869)
                  ·
                    refine ⟨907741028310907221194951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420642742162419256519869 907741028310907221194951)
                    ·
                      rfl

theorem cell22_2651729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_2651729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651729 prefixEnd_2651729 := by exact prefixLift 2651729
  have htrace : WordTrace (prefixWord ++ tailWord_2651729) baseStart_2651729 baseEnd_2651729 := by
    simpa [prefixWord, tailWord_2651729, baseEnd_2651729] using wordTrace_append hprefix tailTrace_2651729
  have hstable : (prefixWord ++ tailWord_2651729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651729).length < 2 ^ (prefixWord ++ tailWord_2651729).sum := by decide
  have hdescent : baseEnd_2651729 < baseStart_2651729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651785 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2651785 : Nat := 118140960795 + 2651785 * 2 ^ 59
def prefixEnd_2651785 : Nat := 4983230072969 + 3 ^ 40 * 2651785 * 2
def baseEnd_2651785 : Nat := 907760198255341741794779

theorem tailTrace_2651785 : CollatzResearch.WordTrace tailWord_2651785 prefixEnd_2651785 907760198255341741794779 := by
  unfold tailWord_2651785
  simp only [CollatzResearch.WordTrace]
  refine ⟨96718544698043308666788809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64479029798695539111192539 96718544698043308666788809)
  ·
    refine ⟨72538908523532481500091607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96718544698043308666788809 72538908523532481500091607)
    ·
      refine ⟨108808362785298722250137411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72538908523532481500091607 108808362785298722250137411)
      ·
        refine ⟨163212544177948083375206117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108808362785298722250137411 163212544177948083375206117)
        ·
          refine ⟨30602352033365265632851147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163212544177948083375206117 30602352033365265632851147)
          ·
            refine ⟨45903528050047898449276721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30602352033365265632851147 45903528050047898449276721)
            ·
              refine ⟨34427646037535923836957541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45903528050047898449276721 34427646037535923836957541)
              ·
                refine ⟨6455183632037985719429539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34427646037535923836957541 6455183632037985719429539)
                ·
                  refine ⟨9682775448056978579144309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455183632037985719429539 9682775448056978579144309)
                  ·
                    refine ⟨907760198255341741794779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9682775448056978579144309 907760198255341741794779)
                    ·
                      rfl

theorem cell22_2651785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2651785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651785 prefixEnd_2651785 := by exact prefixLift 2651785
  have htrace : WordTrace (prefixWord ++ tailWord_2651785) baseStart_2651785 baseEnd_2651785 := by
    simpa [prefixWord, tailWord_2651785, baseEnd_2651785] using wordTrace_append hprefix tailTrace_2651785
  have hstable : (prefixWord ++ tailWord_2651785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651785).length < 2 ^ (prefixWord ++ tailWord_2651785).sum := by decide
  have hdescent : baseEnd_2651785 < baseStart_2651785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651804 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_2651804 : Nat := 118140960795 + 2651804 * 2 ^ 59
def prefixEnd_2651804 : Nat := 4983230072969 + 3 ^ 40 * 2651804 * 2
def baseEnd_2651804 : Nat := 302588900781210675189907

theorem tailTrace_2651804 : CollatzResearch.WordTrace tailWord_2651804 prefixEnd_2651804 302588900781210675189907 := by
  unfold tailWord_2651804
  simp only [CollatzResearch.WordTrace]
  refine ⟨48359618842487237455865233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64479491789982983274486977 48359618842487237455865233)
  ·
    refine ⟨36269714131865428091898925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48359618842487237455865233 36269714131865428091898925)
    ·
      refine ⟨13601142799449535534462097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36269714131865428091898925 13601142799449535534462097)
      ·
        refine ⟨10200857099587151650846573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13601142799449535534462097 10200857099587151650846573)
        ·
          refine ⟨3825321412345181869067465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10200857099587151650846573 3825321412345181869067465)
          ·
            refine ⟨2868991059258886401800599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825321412345181869067465 2868991059258886401800599)
            ·
              refine ⟨4303486588888329602700899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868991059258886401800599 4303486588888329602700899)
              ·
                refine ⟨6455229883332494404051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303486588888329602700899 6455229883332494404051349)
                ·
                  refine ⟨302588900781210675189907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6455229883332494404051349 302588900781210675189907)
                  ·
                    rfl

theorem cell22_2651804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_2651804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651804 prefixEnd_2651804 := by exact prefixLift 2651804
  have htrace : WordTrace (prefixWord ++ tailWord_2651804) baseStart_2651804 baseEnd_2651804 := by
    simpa [prefixWord, tailWord_2651804, baseEnd_2651804] using wordTrace_append hprefix tailTrace_2651804
  have hstable : (prefixWord ++ tailWord_2651804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651804).length < 2 ^ (prefixWord ++ tailWord_2651804).sum := by decide
  have hdescent : baseEnd_2651804 < baseStart_2651804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651853 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2651853 : Nat := 118140960795 + 2651853 * 2 ^ 59
def prefixEnd_2651853 : Nat := 4983230072969 + 3 ^ 40 * 2651853 * 2
def baseEnd_2651853 : Nat := 907783476045012231094571

theorem tailTrace_2651853 : CollatzResearch.WordTrace tailWord_2651853 prefixEnd_2651853 907783476045012231094571 := by
  unfold tailWord_2651853
  simp only [CollatzResearch.WordTrace]
  refine ⟨96721024861796956280264213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64480683241197970853509475 96721024861796956280264213)
  ·
    refine ⟨4533798040396732325637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96721024861796956280264213 4533798040396732325637385)
    ·
      refine ⟨3400348530297549244228039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4533798040396732325637385 3400348530297549244228039)
      ·
        refine ⟨5100522795446323866342059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400348530297549244228039 5100522795446323866342059)
        ·
          refine ⟨7650784193169485799513089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100522795446323866342059 7650784193169485799513089)
          ·
            refine ⟨5738088144877114349634817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7650784193169485799513089 5738088144877114349634817)
            ·
              refine ⟨4303566108657835762226113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738088144877114349634817 4303566108657835762226113)
              ·
                refine ⟨3227674581493376821669585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303566108657835762226113 3227674581493376821669585)
                ·
                  refine ⟨2420755936120032616252189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227674581493376821669585 2420755936120032616252189)
                  ·
                    refine ⟨907783476045012231094571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420755936120032616252189 907783476045012231094571)
                    ·
                      rfl

theorem cell22_2651853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2651853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651853 prefixEnd_2651853 := by exact prefixLift 2651853
  have htrace : WordTrace (prefixWord ++ tailWord_2651853) baseStart_2651853 baseEnd_2651853 := by
    simpa [prefixWord, tailWord_2651853, baseEnd_2651853] using wordTrace_append hprefix tailTrace_2651853
  have hstable : (prefixWord ++ tailWord_2651853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651853).length < 2 ^ (prefixWord ++ tailWord_2651853).sum := by decide
  have hdescent : baseEnd_2651853 < baseStart_2651853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651877 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 5]
def baseStart_2651877 : Nat := 118140960795 + 2651877 * 2 ^ 59
def prefixEnd_2651877 : Nat := 4983230072969 + 3 ^ 40 * 2651877 * 2
def baseEnd_2651877 : Nat := 302597230578494722831499

theorem tailTrace_2651877 : CollatzResearch.WordTrace tailWord_2651877 prefixEnd_2651877 302597230578494722831499 := by
  unfold tailWord_2651877
  simp only [CollatzResearch.WordTrace]
  refine ⟨96721900213710008379137885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64481266809140005586091923 96721900213710008379137885)
  ·
    refine ⟨36270712580141253142176707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96721900213710008379137885 36270712580141253142176707)
    ·
      refine ⟨54406068870211879713265061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36270712580141253142176707 54406068870211879713265061)
      ·
        refine ⟨10201137913164727446237199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54406068870211879713265061 10201137913164727446237199)
        ·
          refine ⟨15301706869747091169355799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201137913164727446237199 15301706869747091169355799)
          ·
            refine ⟨22952560304620636754033699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15301706869747091169355799 22952560304620636754033699)
            ·
              refine ⟨34428840456930955131050549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22952560304620636754033699 34428840456930955131050549)
              ·
                refine ⟨3227703792837277043535989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34428840456930955131050549 3227703792837277043535989)
                ·
                  refine ⟨302597230578494722831499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227703792837277043535989 302597230578494722831499)
                  ·
                    rfl

theorem cell22_2651877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_2651877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651877 prefixEnd_2651877 := by exact prefixLift 2651877
  have htrace : WordTrace (prefixWord ++ tailWord_2651877) baseStart_2651877 baseEnd_2651877 := by
    simpa [prefixWord, tailWord_2651877, baseEnd_2651877] using wordTrace_append hprefix tailTrace_2651877
  have hstable : (prefixWord ++ tailWord_2651877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651877).length < 2 ^ (prefixWord ++ tailWord_2651877).sum := by decide
  have hdescent : baseEnd_2651877 < baseStart_2651877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651911 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 5]
def baseStart_2651911 : Nat := 118140960795 + 2651911 * 2 ^ 59
def prefixEnd_2651911 : Nat := 4983230072969 + 3 ^ 40 * 2651911 * 2
def baseEnd_2651911 : Nat := 302601110210106471048131

theorem tailTrace_2651911 : CollatzResearch.WordTrace tailWord_2651911 prefixEnd_2651911 302601110210106471048131 := by
  unfold tailWord_2651911
  simp only [CollatzResearch.WordTrace]
  refine ⟨96723140295586832185875587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64482093530391221457250391 96723140295586832185875587)
  ·
    refine ⟨145084710443380248278813381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96723140295586832185875587 145084710443380248278813381)
    ·
      refine ⟨27203383208133796552277509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145084710443380248278813381 27203383208133796552277509)
      ·
        refine ⟨5100634351525086853552033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27203383208133796552277509 5100634351525086853552033)
        ·
          refine ⟨3825475763643815140164025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100634351525086853552033 3825475763643815140164025)
          ·
            refine ⟨2869106822732861355123019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825475763643815140164025 2869106822732861355123019)
            ·
              refine ⟨4303660234099292032684529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869106822732861355123019 4303660234099292032684529)
              ·
                refine ⟨3227745175574469024513397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303660234099292032684529 3227745175574469024513397)
                ·
                  refine ⟨302601110210106471048131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227745175574469024513397 302601110210106471048131)
                  ·
                    rfl

theorem cell22_2651911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].length) (baseStart_2651911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651911 prefixEnd_2651911 := by exact prefixLift 2651911
  have htrace : WordTrace (prefixWord ++ tailWord_2651911) baseStart_2651911 baseEnd_2651911 := by
    simpa [prefixWord, tailWord_2651911, baseEnd_2651911] using wordTrace_append hprefix tailTrace_2651911
  have hstable : (prefixWord ++ tailWord_2651911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651911).length < 2 ^ (prefixWord ++ tailWord_2651911).sum := by decide
  have hdescent : baseEnd_2651911 < baseStart_2651911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651954 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_2651954 : Nat := 118140960795 + 2651954 * 2 ^ 59
def prefixEnd_2651954 : Nat := 4983230072969 + 3 ^ 40 * 2651954 * 2
def baseEnd_2651954 : Nat := 907818050409081634319261

theorem tailTrace_2651954 : CollatzResearch.WordTrace tailWord_2651954 prefixEnd_2651954 907818050409081634319261 := by
  unfold tailWord_2651954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24181177158607762632422729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64483139089620700353127277 24181177158607762632422729)
  ·
    refine ⟨18135882868955821974317047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24181177158607762632422729 18135882868955821974317047)
    ·
      refine ⟨27203824303433732961475571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135882868955821974317047 27203824303433732961475571)
      ·
        refine ⟨40805736455150599442213357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27203824303433732961475571 40805736455150599442213357)
        ·
          refine ⟨15302151170681474790830009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40805736455150599442213357 15302151170681474790830009)
          ·
            refine ⟨11476613378011106093122507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15302151170681474790830009 11476613378011106093122507)
            ·
              refine ⟨17214920067016659139683761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11476613378011106093122507 17214920067016659139683761)
              ·
                refine ⟨12911190050262494354762821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17214920067016659139683761 12911190050262494354762821)
                ·
                  refine ⟨2420848134424217691518029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12911190050262494354762821 2420848134424217691518029)
                  ·
                    refine ⟨907818050409081634319261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420848134424217691518029 907818050409081634319261)
                    ·
                      rfl

theorem cell22_2651954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_2651954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651954 prefixEnd_2651954 := by exact prefixLift 2651954
  have htrace : WordTrace (prefixWord ++ tailWord_2651954) baseStart_2651954 baseEnd_2651954 := by
    simpa [prefixWord, tailWord_2651954, baseEnd_2651954] using wordTrace_append hprefix tailTrace_2651954
  have hstable : (prefixWord ++ tailWord_2651954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651954).length < 2 ^ (prefixWord ++ tailWord_2651954).sum := by decide
  have hdescent : baseEnd_2651954 < baseStart_2651954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2651988 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2651988 : Nat := 118140960795 + 2651988 * 2 ^ 59
def prefixEnd_2651988 : Nat := 4983230072969 + 3 ^ 40 * 2651988 * 2
def baseEnd_2651988 : Nat := 907829689303916878969157

theorem tailTrace_2651988 : CollatzResearch.WordTrace tailWord_2651988 prefixEnd_2651988 907829689303916878969157 := by
  unfold tailWord_2651988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48362974358153937168214309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64483965810871916224285745 48362974358153937168214309)
  ·
    refine ⟨9068057692153863219040183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48362974358153937168214309 9068057692153863219040183)
    ·
      refine ⟨13602086538230794828560275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9068057692153863219040183 13602086538230794828560275)
      ·
        refine ⟨20403129807346192242840413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13602086538230794828560275 20403129807346192242840413)
        ·
          refine ⟨7651173677754822091065155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20403129807346192242840413 7651173677754822091065155)
          ·
            refine ⟨11476760516632233136597733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651173677754822091065155 11476760516632233136597733)
            ·
              refine ⟨2151892596868543713112075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11476760516632233136597733 2151892596868543713112075)
              ·
                refine ⟨3227838895302815569668113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151892596868543713112075 3227838895302815569668113)
                ·
                  refine ⟨2420879171477111677251085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227838895302815569668113 2420879171477111677251085)
                  ·
                    refine ⟨907829689303916878969157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420879171477111677251085 907829689303916878969157)
                    ·
                      rfl

theorem cell22_2651988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2651988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2651988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2651988 prefixEnd_2651988 := by exact prefixLift 2651988
  have htrace : WordTrace (prefixWord ++ tailWord_2651988) baseStart_2651988 baseEnd_2651988 := by
    simpa [prefixWord, tailWord_2651988, baseEnd_2651988] using wordTrace_append hprefix tailTrace_2651988
  have hstable : (prefixWord ++ tailWord_2651988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2651988).length < 2 ^ (prefixWord ++ tailWord_2651988).sum := by decide
  have hdescent : baseEnd_2651988 < baseStart_2651988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2651988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652016 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_2652016 : Nat := 118140960795 + 2652016 * 2 ^ 59
def prefixEnd_2652016 : Nat := 4983230072969 + 3 ^ 40 * 2652016 * 2
def baseEnd_2652016 : Nat := 907839274276134139269071

theorem tailTrace_2652016 : CollatzResearch.WordTrace tailWord_2652016 prefixEnd_2652016 907839274276134139269071 := by
  unfold tailWord_2652016
  simp only [CollatzResearch.WordTrace]
  refine ⟨48363484980103217559223951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64484646640137623412298601 48363484980103217559223951)
  ·
    refine ⟨72545227470154826338835927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48363484980103217559223951 72545227470154826338835927)
    ·
      refine ⟨108817841205232239508253891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72545227470154826338835927 108817841205232239508253891)
      ·
        refine ⟨163226761807848359262380837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108817841205232239508253891 163226761807848359262380837)
        ·
          refine ⟨30605017838971567361696407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163226761807848359262380837 30605017838971567361696407)
          ·
            refine ⟨45907526758457351042544611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30605017838971567361696407 45907526758457351042544611)
            ·
              refine ⟨68861290137686026563816917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45907526758457351042544611 68861290137686026563816917)
              ·
                refine ⟨1613936487602016247589459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68861290137686026563816917 1613936487602016247589459)
                ·
                  refine ⟨2420904731403024371384189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613936487602016247589459 2420904731403024371384189)
                  ·
                    refine ⟨907839274276134139269071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420904731403024371384189 907839274276134139269071)
                    ·
                      rfl

theorem cell22_2652016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_2652016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652016 prefixEnd_2652016 := by exact prefixLift 2652016
  have htrace : WordTrace (prefixWord ++ tailWord_2652016) baseStart_2652016 baseEnd_2652016 := by
    simpa [prefixWord, tailWord_2652016, baseEnd_2652016] using wordTrace_append hprefix tailTrace_2652016
  have hstable : (prefixWord ++ tailWord_2652016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652016).length < 2 ^ (prefixWord ++ tailWord_2652016).sum := by decide
  have hdescent : baseEnd_2652016 < baseStart_2652016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_2652027 : Nat := 118140960795 + 2652027 * 2 ^ 59
def prefixEnd_2652027 : Nat := 4983230072969 + 3 ^ 40 * 2652027 * 2
def baseEnd_2652027 : Nat := 907843039800933777244037

theorem tailTrace_2652027 : CollatzResearch.WordTrace tailWord_2652027 prefixEnd_2652027 907843039800933777244037 := by
  unfold tailWord_2652027
  simp only [CollatzResearch.WordTrace]
  refine ⟨96727371163166583997098335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64484914108777722664732223 96727371163166583997098335)
  ·
    refine ⟨145091056744749875995647503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96727371163166583997098335 145091056744749875995647503)
    ·
      refine ⟨217636585117124813993471255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145091056744749875995647503 217636585117124813993471255)
      ·
        refine ⟨326454877675687220990206883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217636585117124813993471255 326454877675687220990206883)
        ·
          refine ⟨489682316513530831485310325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326454877675687220990206883 489682316513530831485310325)
          ·
            refine ⟨45907717173143515451747843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 489682316513530831485310325 45907717173143515451747843)
            ·
              refine ⟨68861575759715273177621765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45907717173143515451747843 68861575759715273177621765)
              ·
                refine ⟨12911545454946613720804081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68861575759715273177621765 12911545454946613720804081)
                ·
                  refine ⟨9683659091209960290603061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12911545454946613720804081 9683659091209960290603061)
                  ·
                    refine ⟨907843039800933777244037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9683659091209960290603061 907843039800933777244037)
                    ·
                      rfl

theorem cell22_2652027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_2652027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652027 prefixEnd_2652027 := by exact prefixLift 2652027
  have htrace : WordTrace (prefixWord ++ tailWord_2652027) baseStart_2652027 baseEnd_2652027 := by
    simpa [prefixWord, tailWord_2652027, baseEnd_2652027] using wordTrace_append hprefix tailTrace_2652027
  have hstable : (prefixWord ++ tailWord_2652027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652027).length < 2 ^ (prefixWord ++ tailWord_2652027).sum := by decide
  have hdescent : baseEnd_2652027 < baseStart_2652027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652057 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 8]
def baseStart_2652057 : Nat := 118140960795 + 2652057 * 2 ^ 59
def prefixEnd_2652057 : Nat := 4983230072969 + 3 ^ 40 * 2652057 * 2
def baseEnd_2652057 : Nat := 302617769804674566331315

theorem tailTrace_2652057 : CollatzResearch.WordTrace tailWord_2652057 prefixEnd_2652057 302617769804674566331315 := by
  unfold tailWord_2652057
  simp only [CollatzResearch.WordTrace]
  refine ⟨96728465353057899120690425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64485643568705266080460283 96728465353057899120690425)
  ·
    refine ⟨72546349014793424340517819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96728465353057899120690425 72546349014793424340517819)
    ·
      refine ⟨108819523522190136510776729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72546349014793424340517819 108819523522190136510776729)
      ·
        refine ⟨81614642641642602383082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108819523522190136510776729 81614642641642602383082547)
        ·
          refine ⟨122421963962463903574623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81614642641642602383082547 122421963962463903574623821)
          ·
            refine ⟨45908236485923963840483933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122421963962463903574623821 45908236485923963840483933)
            ·
              refine ⟨17215588682221486440181475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45908236485923963840483933 17215588682221486440181475)
              ·
                refine ⟨25823383023332229660272213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215588682221486440181475 25823383023332229660272213)
                ·
                  refine ⟨302617769804674566331315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25823383023332229660272213 302617769804674566331315)
                  ·
                    rfl

theorem cell22_2652057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_2652057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652057 prefixEnd_2652057 := by exact prefixLift 2652057
  have htrace : WordTrace (prefixWord ++ tailWord_2652057) baseStart_2652057 baseEnd_2652057 := by
    simpa [prefixWord, tailWord_2652057, baseEnd_2652057] using wordTrace_append hprefix tailTrace_2652057
  have hstable : (prefixWord ++ tailWord_2652057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652057).length < 2 ^ (prefixWord ++ tailWord_2652057).sum := by decide
  have hdescent : baseEnd_2652057 < baseStart_2652057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652104 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2652104 : Nat := 118140960795 + 2652104 * 2 ^ 59
def prefixEnd_2652104 : Nat := 4983230072969 + 3 ^ 40 * 2652104 * 2
def baseEnd_2652104 : Nat := 907869398474531243068801

theorem tailTrace_2652104 : CollatzResearch.WordTrace tailWord_2652104 prefixEnd_2652104 907869398474531243068801 := by
  unfold tailWord_2652104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48365089791943813073825683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64486786389258417431767577 48365089791943813073825683)
  ·
    refine ⟨72547634687915719610738525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48365089791943813073825683 72547634687915719610738525)
    ·
      refine ⟨27205363007968394854026947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72547634687915719610738525 27205363007968394854026947)
      ·
        refine ⟨40808044511952592281040421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27205363007968394854026947 40808044511952592281040421)
        ·
          refine ⟨7651508345991111052695079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40808044511952592281040421 7651508345991111052695079)
          ·
            refine ⟨11477262518986666579042619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651508345991111052695079 11477262518986666579042619)
            ·
              refine ⟨17215893778479999868563929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11477262518986666579042619 17215893778479999868563929)
              ·
                refine ⟨12911920333859999901422947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17215893778479999868563929 12911920333859999901422947)
                ·
                  refine ⟨19367880500789999852134421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12911920333859999901422947 19367880500789999852134421)
                  ·
                    refine ⟨907869398474531243068801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19367880500789999852134421 907869398474531243068801)
                    ·
                      rfl

theorem cell22_2652104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2652104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652104 prefixEnd_2652104 := by exact prefixLift 2652104
  have htrace : WordTrace (prefixWord ++ tailWord_2652104) baseStart_2652104 baseEnd_2652104 := by
    simpa [prefixWord, tailWord_2652104, baseEnd_2652104] using wordTrace_append hprefix tailTrace_2652104
  have hstable : (prefixWord ++ tailWord_2652104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652104).length < 2 ^ (prefixWord ++ tailWord_2652104).sum := by decide
  have hdescent : baseEnd_2652104 < baseStart_2652104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652106 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2652106 : Nat := 118140960795 + 2652106 * 2 ^ 59
def prefixEnd_2652106 : Nat := 4983230072969 + 3 ^ 40 * 2652106 * 2
def baseEnd_2652106 : Nat := 907870083115403904518795

theorem tailTrace_2652106 : CollatzResearch.WordTrace tailWord_2652106 prefixEnd_2652106 907870083115403904518795 := by
  unfold tailWord_2652106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24182563132470095122306043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64486835019920253659482781 24182563132470095122306043)
  ·
    refine ⟨36273844698705142683459065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24182563132470095122306043 36273844698705142683459065)
    ·
      refine ⟨27205383524028857012594299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36273844698705142683459065 27205383524028857012594299)
      ·
        refine ⟨40808075286043285518891449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27205383524028857012594299 40808075286043285518891449)
        ·
          refine ⟨30606056464532464139168587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40808075286043285518891449 30606056464532464139168587)
          ·
            refine ⟨45909084696798696208752881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30606056464532464139168587 45909084696798696208752881)
            ·
              refine ⟨34431813522599022156564661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45909084696798696208752881 34431813522599022156564661)
              ·
                refine ⟨3227982517743658327177937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34431813522599022156564661 3227982517743658327177937)
                ·
                  refine ⟨2420986888307743745383453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227982517743658327177937 2420986888307743745383453)
                  ·
                    refine ⟨907870083115403904518795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2420986888307743745383453 907870083115403904518795)
                    ·
                      rfl

theorem cell22_2652106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2652106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652106 prefixEnd_2652106 := by exact prefixLift 2652106
  have htrace : WordTrace (prefixWord ++ tailWord_2652106) baseStart_2652106 baseEnd_2652106 := by
    simpa [prefixWord, tailWord_2652106, baseEnd_2652106] using wordTrace_append hprefix tailTrace_2652106
  have hstable : (prefixWord ++ tailWord_2652106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652106).length < 2 ^ (prefixWord ++ tailWord_2652106).sum := by decide
  have hdescent : baseEnd_2652106 < baseStart_2652106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652125 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 4]
def baseStart_2652125 : Nat := 118140960795 + 2652125 * 2 ^ 59
def prefixEnd_2652125 : Nat := 4983230072969 + 3 ^ 40 * 2652125 * 2
def baseEnd_2652125 : Nat := 302625529067898062764579

theorem tailTrace_2652125 : CollatzResearch.WordTrace tailWord_2652125 prefixEnd_2652125 302625529067898062764579 := by
  unfold tailWord_2652125
  simp only [CollatzResearch.WordTrace]
  refine ⟨96730945516811546734165829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64487297011207697822777219 96730945516811546734165829)
  ·
    refine ⟨18137052284402165012656093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96730945516811546734165829 18137052284402165012656093)
    ·
      refine ⟨6801394606650811879746035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18137052284402165012656093 6801394606650811879746035)
      ·
        refine ⟨10202091909976217819619053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801394606650811879746035 10202091909976217819619053)
        ·
          refine ⟨3825784466241081682357145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10202091909976217819619053 3825784466241081682357145)
          ·
            refine ⟨2869338349680811261767859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825784466241081682357145 2869338349680811261767859)
            ·
              refine ⟨4304007524521216892651789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869338349680811261767859 4304007524521216892651789)
              ·
                refine ⟨1614002821695456334744421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4304007524521216892651789 1614002821695456334744421)
                ·
                  refine ⟨302625529067898062764579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614002821695456334744421 302625529067898062764579)
                  ·
                    rfl

theorem cell22_2652125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_2652125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652125 prefixEnd_2652125 := by exact prefixLift 2652125
  have htrace : WordTrace (prefixWord ++ tailWord_2652125) baseStart_2652125 baseEnd_2652125 := by
    simpa [prefixWord, tailWord_2652125, baseEnd_2652125] using wordTrace_append hprefix tailTrace_2652125
  have hstable : (prefixWord ++ tailWord_2652125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652125).length < 2 ^ (prefixWord ++ tailWord_2652125).sum := by decide
  have hdescent : baseEnd_2652125 < baseStart_2652125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652202 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2652202 : Nat := 118140960795 + 2652202 * 2 ^ 59
def prefixEnd_2652202 : Nat := 4983230072969 + 3 ^ 40 * 2652202 * 2
def baseEnd_2652202 : Nat := 907902945877291654118501

theorem tailTrace_2652202 : CollatzResearch.WordTrace tailWord_2652202 prefixEnd_2652202 907902945877291654118501 := by
  unfold tailWord_2652202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24183438484383147221179715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64489169291688392589812573 24183438484383147221179715)
  ·
    refine ⟨36275157726574720831769573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24183438484383147221179715 36275157726574720831769573)
    ·
      refine ⟨6801592073732760155956795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36275157726574720831769573 6801592073732760155956795)
      ·
        refine ⟨10202388110599140233935193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801592073732760155956795 10202388110599140233935193)
        ·
          refine ⟨7651791082949355175451395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202388110599140233935193 7651791082949355175451395)
          ·
            refine ⟨11477686624424032763177093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651791082949355175451395 11477686624424032763177093)
            ·
              refine ⟨2152066242079506143095705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11477686624424032763177093 2152066242079506143095705)
              ·
                refine ⟨1614049681559629607321779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152066242079506143095705 1614049681559629607321779)
                ·
                  refine ⟨2421074522339444410982669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614049681559629607321779 2421074522339444410982669)
                  ·
                    refine ⟨907902945877291654118501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421074522339444410982669 907902945877291654118501)
                    ·
                      rfl

theorem cell22_2652202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2652202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652202 prefixEnd_2652202 := by exact prefixLift 2652202
  have htrace : WordTrace (prefixWord ++ tailWord_2652202) baseStart_2652202 baseEnd_2652202 := by
    simpa [prefixWord, tailWord_2652202, baseEnd_2652202] using wordTrace_append hprefix tailTrace_2652202
  have hstable : (prefixWord ++ tailWord_2652202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652202).length < 2 ^ (prefixWord ++ tailWord_2652202).sum := by decide
  have hdescent : baseEnd_2652202 < baseStart_2652202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652239 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2652239 : Nat := 118140960795 + 2652239 * 2 ^ 59
def prefixEnd_2652239 : Nat := 4983230072969 + 3 ^ 40 * 2652239 * 2
def baseEnd_2652239 : Nat := 907915611733435890943387

theorem tailTrace_2652239 : CollatzResearch.WordTrace tailWord_2652239 prefixEnd_2652239 907915611733435890943387 := by
  unfold tailWord_2652239
  simp only [CollatzResearch.WordTrace]
  refine ⟨96735103438398544203815771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64490068958932362802543847 96735103438398544203815771)
  ·
    refine ⟨145102655157597816305723657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96735103438398544203815771 145102655157597816305723657)
    ·
      refine ⟨108826991368198362229292743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145102655157597816305723657 108826991368198362229292743)
      ·
        refine ⟨163240487052297543343939115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108826991368198362229292743 163240487052297543343939115)
        ·
          refine ⟨244860730578446315015908673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163240487052297543343939115 244860730578446315015908673)
          ·
            refine ⟨183645547933834736261931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244860730578446315015908673 183645547933834736261931505)
            ·
              refine ⟨137734160950376052196448629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183645547933834736261931505 137734160950376052196448629)
              ·
                refine ⟨12912577589097754893417059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137734160950376052196448629 12912577589097754893417059)
                ·
                  refine ⟨19368866383646632340125589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12912577589097754893417059 19368866383646632340125589)
                  ·
                    refine ⟨907915611733435890943387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19368866383646632340125589 907915611733435890943387)
                    ·
                      rfl

theorem cell22_2652239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2652239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652239 prefixEnd_2652239 := by exact prefixLift 2652239
  have htrace : WordTrace (prefixWord ++ tailWord_2652239) baseStart_2652239 baseEnd_2652239 := by
    simpa [prefixWord, tailWord_2652239, baseEnd_2652239] using wordTrace_append hprefix tailTrace_2652239
  have hstable : (prefixWord ++ tailWord_2652239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652239).length < 2 ^ (prefixWord ++ tailWord_2652239).sum := by decide
  have hdescent : baseEnd_2652239 < baseStart_2652239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652241 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_2652241 : Nat := 118140960795 + 2652241 * 2 ^ 59
def prefixEnd_2652241 : Nat := 4983230072969 + 3 ^ 40 * 2652241 * 2
def baseEnd_2652241 : Nat := 907916296374308552393381

theorem tailTrace_2652241 : CollatzResearch.WordTrace tailWord_2652241 prefixEnd_2652241 907916296374308552393381 := by
  unfold tailWord_2652241
  simp only [CollatzResearch.WordTrace]
  refine ⟨96735176384391298545388577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64490117589594199030259051 96735176384391298545388577)
  ·
    refine ⟨72551382288293473909041433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96735176384391298545388577 72551382288293473909041433)
    ·
      refine ⟨54413536716220105431781075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72551382288293473909041433 54413536716220105431781075)
      ·
        refine ⟨81620305074330158147671613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54413536716220105431781075 81620305074330158147671613)
        ·
          refine ⟨30607614402873809305376855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81620305074330158147671613 30607614402873809305376855)
          ·
            refine ⟨45911421604310713958065283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30607614402873809305376855 45911421604310713958065283)
            ·
              refine ⟨68867132406466070937097925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45911421604310713958065283 68867132406466070937097925)
              ·
                refine ⟨12912587326212388300705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68867132406466070937097925 12912587326212388300705861)
                ·
                  refine ⟨2421110123664822806382349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12912587326212388300705861 2421110123664822806382349)
                  ·
                    refine ⟨907916296374308552393381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421110123664822806382349 907916296374308552393381)
                    ·
                      rfl

theorem cell22_2652241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_2652241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652241 prefixEnd_2652241 := by exact prefixLift 2652241
  have htrace : WordTrace (prefixWord ++ tailWord_2652241) baseStart_2652241 baseEnd_2652241 := by
    simpa [prefixWord, tailWord_2652241, baseEnd_2652241] using wordTrace_append hprefix tailTrace_2652241
  have hstable : (prefixWord ++ tailWord_2652241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652241).length < 2 ^ (prefixWord ++ tailWord_2652241).sum := by decide
  have hdescent : baseEnd_2652241 < baseStart_2652241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652245 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2652245 : Nat := 118140960795 + 2652245 * 2 ^ 59
def prefixEnd_2652245 : Nat := 4983230072969 + 3 ^ 40 * 2652245 * 2
def baseEnd_2652245 : Nat := 907917665656053875293369

theorem tailTrace_2652245 : CollatzResearch.WordTrace tailWord_2652245 prefixEnd_2652245 907917665656053875293369 := by
  unfold tailWord_2652245
  simp only [CollatzResearch.WordTrace]
  refine ⟨96735322276376807228534189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64490214850917871485689459 96735322276376807228534189)
  ·
    refine ⟨36275745853641302710700321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96735322276376807228534189 36275745853641302710700321)
    ·
      refine ⟨27206809390230977033025241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36275745853641302710700321 27206809390230977033025241)
      ·
        refine ⟨20405107042673232774768931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27206809390230977033025241 20405107042673232774768931)
        ·
          refine ⟨30607660564009849162153397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20405107042673232774768931 30607660564009849162153397)
          ·
            refine ⟨2869468177875923358951881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30607660564009849162153397 2869468177875923358951881)
            ·
              refine ⟨2152101133406942519213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869468177875923358951881 2152101133406942519213911)
              ·
                refine ⟨3228151700110413778820867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152101133406942519213911 3228151700110413778820867)
                ·
                  refine ⟨4842227550165620668231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228151700110413778820867 4842227550165620668231301)
                  ·
                    refine ⟨907917665656053875293369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4842227550165620668231301 907917665656053875293369)
                    ·
                      rfl

theorem cell22_2652245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2652245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652245 prefixEnd_2652245 := by exact prefixLift 2652245
  have htrace : WordTrace (prefixWord ++ tailWord_2652245) baseStart_2652245 baseEnd_2652245 := by
    simpa [prefixWord, tailWord_2652245, baseEnd_2652245] using wordTrace_append hprefix tailTrace_2652245
  have hstable : (prefixWord ++ tailWord_2652245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652245).length < 2 ^ (prefixWord ++ tailWord_2652245).sum := by decide
  have hdescent : baseEnd_2652245 < baseStart_2652245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652316 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_2652316 : Nat := 118140960795 + 2652316 * 2 ^ 59
def prefixEnd_2652316 : Nat := 4983230072969 + 3 ^ 40 * 2652316 * 2
def baseEnd_2652316 : Nat := 302647323469011118922717

theorem tailTrace_2652316 : CollatzResearch.WordTrace tailWord_2652316 prefixEnd_2652316 302647323469011118922717 := by
  unfold tailWord_2652316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48368955929559793177184401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64491941239413057569579201 48368955929559793177184401)
  ·
    refine ⟨36276716947169844882888301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48368955929559793177184401 36276716947169844882888301)
    ·
      refine ⟨13603768855188691831083113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36276716947169844882888301 13603768855188691831083113)
      ·
        refine ⟨10202826641391518873312335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13603768855188691831083113 10202826641391518873312335)
        ·
          refine ⟨15304239962087278309968503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10202826641391518873312335 15304239962087278309968503)
          ·
            refine ⟨22956359943130917464952755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15304239962087278309968503 22956359943130917464952755)
            ·
              refine ⟨34434539914696376197429133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22956359943130917464952755 34434539914696376197429133)
              ·
                refine ⟨12912952468011141074035925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34434539914696376197429133 12912952468011141074035925)
                ·
                  refine ⟨302647323469011118922717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12912952468011141074035925 302647323469011118922717)
                  ·
                    rfl

theorem cell22_2652316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_2652316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652316 prefixEnd_2652316 := by exact prefixLift 2652316
  have htrace : WordTrace (prefixWord ++ tailWord_2652316) baseStart_2652316 baseEnd_2652316 := by
    simpa [prefixWord, tailWord_2652316, baseEnd_2652316] using wordTrace_append hprefix tailTrace_2652316
  have hstable : (prefixWord ++ tailWord_2652316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652316).length < 2 ^ (prefixWord ++ tailWord_2652316).sum := by decide
  have hdescent : baseEnd_2652316 < baseStart_2652316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652320 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_2652320 : Nat := 118140960795 + 2652320 * 2 ^ 59
def prefixEnd_2652320 : Nat := 4983230072969 + 3 ^ 40 * 2652320 * 2
def baseEnd_2652320 : Nat := 907943339688778679668139

theorem tailTrace_2652320 : CollatzResearch.WordTrace tailWord_2652320 prefixEnd_2652320 907943339688778679668139 := by
  unfold tailWord_2652320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48369028875552547518757207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64492038500736730025009609 48369028875552547518757207)
  ·
    refine ⟨72553543313328821278135811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48369028875552547518757207 72553543313328821278135811)
    ·
      refine ⟨108830314969993231917203717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72553543313328821278135811 108830314969993231917203717)
      ·
        refine ⟨20405684056873730984475697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108830314969993231917203717 20405684056873730984475697)
        ·
          refine ⟨15304263042655298238356773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20405684056873730984475697 15304263042655298238356773)
          ·
            refine ⟨2869549320497868419691895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15304263042655298238356773 2869549320497868419691895)
            ·
              refine ⟨4304323980746802629537843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869549320497868419691895 4304323980746802629537843)
              ·
                refine ⟨6456485971120203944306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304323980746802629537843 6456485971120203944306765)
                ·
                  refine ⟨2421182239170076479115037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6456485971120203944306765 2421182239170076479115037)
                  ·
                    refine ⟨907943339688778679668139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421182239170076479115037 907943339688778679668139)
                    ·
                      rfl

theorem cell22_2652320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_2652320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652320 prefixEnd_2652320 := by exact prefixLift 2652320
  have htrace : WordTrace (prefixWord ++ tailWord_2652320) baseStart_2652320 baseEnd_2652320 := by
    simpa [prefixWord, tailWord_2652320, baseEnd_2652320] using wordTrace_append hprefix tailTrace_2652320
  have hstable : (prefixWord ++ tailWord_2652320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652320).length < 2 ^ (prefixWord ++ tailWord_2652320).sum := by decide
  have hdescent : baseEnd_2652320 < baseStart_2652320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652472 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_2652472 : Nat := 118140960795 + 2652472 * 2 ^ 59
def prefixEnd_2652472 : Nat := 4983230072969 + 3 ^ 40 * 2652472 * 2
def baseEnd_2652472 : Nat := 907995372395100949867673

theorem tailTrace_2652472 : CollatzResearch.WordTrace tailWord_2652472 prefixEnd_2652472 907995372395100949867673 := by
  unfold tailWord_2652472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48371800823277212498523835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64495734431036283331365113 48371800823277212498523835)
  ·
    refine ⟨72557701234915818747785753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48371800823277212498523835 72557701234915818747785753)
    ·
      refine ⟨54418275926186864060839315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72557701234915818747785753 54418275926186864060839315)
      ·
        refine ⟨81627413889280296091258973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54418275926186864060839315 81627413889280296091258973)
        ·
          refine ⟨30610280208480111034222115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81627413889280296091258973 30610280208480111034222115)
          ·
            refine ⟨45915420312720166551333173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30610280208480111034222115 45915420312720166551333173)
            ·
              refine ⟨4304570654317515614187485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45915420312720166551333173 4304570654317515614187485)
              ·
                refine ⟨1614213995369068355320307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4304570654317515614187485 1614213995369068355320307)
                ·
                  refine ⟨2421320993053602532980461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614213995369068355320307 2421320993053602532980461)
                  ·
                    refine ⟨907995372395100949867673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421320993053602532980461 907995372395100949867673)
                    ·
                      rfl

theorem cell22_2652472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_2652472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652472 prefixEnd_2652472 := by exact prefixLift 2652472
  have htrace : WordTrace (prefixWord ++ tailWord_2652472) baseStart_2652472 baseEnd_2652472 := by
    simpa [prefixWord, tailWord_2652472, baseEnd_2652472] using wordTrace_append hprefix tailTrace_2652472
  have hstable : (prefixWord ++ tailWord_2652472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652472).length < 2 ^ (prefixWord ++ tailWord_2652472).sum := by decide
  have hdescent : baseEnd_2652472 < baseStart_2652472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652528 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_2652528 : Nat := 118140960795 + 2652528 * 2 ^ 59
def prefixEnd_2652528 : Nat := 4983230072969 + 3 ^ 40 * 2652528 * 2
def baseEnd_2652528 : Nat := 908014542339535470467501

theorem tailTrace_2652528 : CollatzResearch.WordTrace tailWord_2652528 prefixEnd_2652528 908014542339535470467501 := by
  unfold tailWord_2652528
  simp only [CollatzResearch.WordTrace]
  refine ⟨48372822067175773280543119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64497096089567697707390825 48372822067175773280543119)
  ·
    refine ⟨72559233100763659920814679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48372822067175773280543119 72559233100763659920814679)
    ·
      refine ⟨108838849651145489881222019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72559233100763659920814679 108838849651145489881222019)
      ·
        refine ⟨163258274476718234821833029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108838849651145489881222019 163258274476718234821833029)
        ·
          refine ⟨30610926464384669029093693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163258274476718234821833029 30610926464384669029093693)
          ·
            refine ⟨11479097424144250885910135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30610926464384669029093693 11479097424144250885910135)
            ·
              refine ⟨17218646136216376328865203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11479097424144250885910135 17218646136216376328865203)
              ·
                refine ⟨25827969204324564493297805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17218646136216376328865203 25827969204324564493297805)
                ·
                  refine ⟨9685488451621711684986677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25827969204324564493297805 9685488451621711684986677)
                  ·
                    refine ⟨908014542339535470467501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9685488451621711684986677 908014542339535470467501)
                    ·
                      rfl

theorem cell22_2652528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_2652528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652528 prefixEnd_2652528 := by exact prefixLift 2652528
  have htrace : WordTrace (prefixWord ++ tailWord_2652528) baseStart_2652528 baseEnd_2652528 := by
    simpa [prefixWord, tailWord_2652528, baseEnd_2652528] using wordTrace_append hprefix tailTrace_2652528
  have hstable : (prefixWord ++ tailWord_2652528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652528).length < 2 ^ (prefixWord ++ tailWord_2652528).sum := by decide
  have hdescent : baseEnd_2652528 < baseStart_2652528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652547 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 4]
def baseStart_2652547 : Nat := 118140960795 + 2652547 * 2 ^ 59
def prefixEnd_2652547 : Nat := 4983230072969 + 3 ^ 40 * 2652547 * 2
def baseEnd_2652547 : Nat := 302673682142608584747481

theorem tailTrace_2652547 : CollatzResearch.WordTrace tailWord_2652547 prefixEnd_2652547 302673682142608584747481 := by
  unfold tailWord_2652547
  simp only [CollatzResearch.WordTrace]
  refine ⟨96746337121282712806027895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64497558080855141870685263 96746337121282712806027895)
  ·
    refine ⟨145119505681924069209041843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96746337121282712806027895 145119505681924069209041843)
    ·
      refine ⟨217679258522886103813562765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145119505681924069209041843 217679258522886103813562765)
      ·
        refine ⟨81629721946082288930086037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217679258522886103813562765 81629721946082288930086037)
        ·
          refine ⟨3826393216222607293597783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81629721946082288930086037 3826393216222607293597783)
          ·
            refine ⟨5739589824333910940396675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826393216222607293597783 5739589824333910940396675)
            ·
              refine ⟨8609384736500866410595013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739589824333910940396675 8609384736500866410595013)
              ·
                refine ⟨1614259638093912451986565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8609384736500866410595013 1614259638093912451986565)
                ·
                  refine ⟨302673682142608584747481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614259638093912451986565 302673682142608584747481)
                  ·
                    rfl

theorem cell22_2652547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 4].length) (baseStart_2652547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652547 prefixEnd_2652547 := by exact prefixLift 2652547
  have htrace : WordTrace (prefixWord ++ tailWord_2652547) baseStart_2652547 baseEnd_2652547 := by
    simpa [prefixWord, tailWord_2652547, baseEnd_2652547] using wordTrace_append hprefix tailTrace_2652547
  have hstable : (prefixWord ++ tailWord_2652547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652547).length < 2 ^ (prefixWord ++ tailWord_2652547).sum := by decide
  have hdescent : baseEnd_2652547 < baseStart_2652547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652575 : List Nat := [1, 1, 2, 5, 1, 1, 5, 6]
def baseStart_2652575 : Nat := 118140960795 + 2652575 * 2 ^ 59
def prefixEnd_2652575 : Nat := 4983230072969 + 3 ^ 40 * 2652575 * 2
def baseEnd_2652575 : Nat := 100892292377782557171373

theorem tailTrace_2652575 : CollatzResearch.WordTrace tailWord_2652575 prefixEnd_2652575 100892292377782557171373 := by
  unfold tailWord_2652575
  simp only [CollatzResearch.WordTrace]
  refine ⟨96747358365181273588047179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64498238910120849058698119 96747358365181273588047179)
  ·
    refine ⟨145121037547771910382070769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96747358365181273588047179 145121037547771910382070769)
    ·
      refine ⟨108840778160828932786553077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145121037547771910382070769 108840778160828932786553077)
      ·
        refine ⟨10203822952577712448739351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108840778160828932786553077 10203822952577712448739351)
        ·
          refine ⟨15305734428866568673109027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203822952577712448739351 15305734428866568673109027)
          ·
            refine ⟨22958601643299853009663541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15305734428866568673109027 22958601643299853009663541)
            ·
              refine ⟨2152368904059361219655957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22958601643299853009663541 2152368904059361219655957)
              ·
                refine ⟨100892292377782557171373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2152368904059361219655957 100892292377782557171373)
                ·
                  rfl

theorem cell22_2652575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 6].length) (baseStart_2652575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652575 prefixEnd_2652575 := by exact prefixLift 2652575
  have htrace : WordTrace (prefixWord ++ tailWord_2652575) baseStart_2652575 baseEnd_2652575 := by
    simpa [prefixWord, tailWord_2652575, baseEnd_2652575] using wordTrace_append hprefix tailTrace_2652575
  have hstable : (prefixWord ++ tailWord_2652575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652575).length < 2 ^ (prefixWord ++ tailWord_2652575).sum := by decide
  have hdescent : baseEnd_2652575 < baseStart_2652575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652577 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2652577 : Nat := 118140960795 + 2652577 * 2 ^ 59
def prefixEnd_2652577 : Nat := 4983230072969 + 3 ^ 40 * 2652577 * 2
def baseEnd_2652577 : Nat := 908031316040915675992351

theorem tailTrace_2652577 : CollatzResearch.WordTrace tailWord_2652577 prefixEnd_2652577 908031316040915675992351 := by
  unfold tailWord_2652577
  simp only [CollatzResearch.WordTrace]
  refine ⟨96747431311174027929619985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64498287540782685286413323 96747431311174027929619985)
  ·
    refine ⟨72560573483380520947214989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96747431311174027929619985 72560573483380520947214989)
    ·
      refine ⟨27210215056267695355205621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72560573483380520947214989 27210215056267695355205621)
      ·
        refine ⟨2550957661525096439550527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27210215056267695355205621 2550957661525096439550527)
        ·
          refine ⟨3826436492287644659325791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550957661525096439550527 3826436492287644659325791)
          ·
            refine ⟨5739654738431466988988687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826436492287644659325791 5739654738431466988988687)
            ·
              refine ⟨8609482107647200483483031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739654738431466988988687 8609482107647200483483031)
              ·
                refine ⟨12914223161470800725224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609482107647200483483031 12914223161470800725224547)
                ·
                  refine ⟨19371334742206201087836821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12914223161470800725224547 19371334742206201087836821)
                  ·
                    refine ⟨908031316040915675992351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19371334742206201087836821 908031316040915675992351)
                    ·
                      rfl

theorem cell22_2652577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2652577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652577 prefixEnd_2652577 := by exact prefixLift 2652577
  have htrace : WordTrace (prefixWord ++ tailWord_2652577) baseStart_2652577 baseEnd_2652577 := by
    simpa [prefixWord, tailWord_2652577, baseEnd_2652577] using wordTrace_append hprefix tailTrace_2652577
  have hstable : (prefixWord ++ tailWord_2652577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652577).length < 2 ^ (prefixWord ++ tailWord_2652577).sum := by decide
  have hdescent : baseEnd_2652577 < baseStart_2652577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652596 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2652596 : Nat := 118140960795 + 2652596 * 2 ^ 59
def prefixEnd_2652596 : Nat := 4983230072969 + 3 ^ 40 * 2652596 * 2
def baseEnd_2652596 : Nat := 908037820129205959767293

theorem tailTrace_2652596 : CollatzResearch.WordTrace tailWord_2652596 prefixEnd_2652596 908037820129205959767293 := by
  unfold tailWord_2652596
  simp only [CollatzResearch.WordTrace]
  refine ⟨48374062149052597087280821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64498749532070129449707761 48374062149052597087280821)
  ·
    refine ⟨4535068326473680976932577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48374062149052597087280821 4535068326473680976932577)
    ·
      refine ⟨3401301244855260732699433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535068326473680976932577 3401301244855260732699433)
      ·
        refine ⟨2550975933641445549524575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3401301244855260732699433 2550975933641445549524575)
        ·
          refine ⟨3826463900462168324286863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550975933641445549524575 3826463900462168324286863)
          ·
            refine ⟨5739695850693252486430295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826463900462168324286863 5739695850693252486430295)
            ·
              refine ⟨8609543776039878729645443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739695850693252486430295 8609543776039878729645443)
              ·
                refine ⟨12914315664059818094468165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609543776039878729645443 12914315664059818094468165)
                ·
                  refine ⟨2421434187011215892712781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12914315664059818094468165 2421434187011215892712781)
                  ·
                    refine ⟨908037820129205959767293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421434187011215892712781 908037820129205959767293)
                    ·
                      rfl

theorem cell22_2652596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2652596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652596 prefixEnd_2652596 := by exact prefixLift 2652596
  have htrace : WordTrace (prefixWord ++ tailWord_2652596) baseStart_2652596 baseEnd_2652596 := by
    simpa [prefixWord, tailWord_2652596, baseEnd_2652596] using wordTrace_append hprefix tailTrace_2652596
  have hstable : (prefixWord ++ tailWord_2652596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652596).length < 2 ^ (prefixWord ++ tailWord_2652596).sum := by decide
  have hdescent : baseEnd_2652596 < baseStart_2652596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652626 : List Nat := [3, 2, 2, 4, 2, 1, 2, 6]
def baseStart_2652626 : Nat := 118140960795 + 2652626 * 2 ^ 59
def prefixEnd_2652626 : Nat := 4983230072969 + 3 ^ 40 * 2652626 * 2
def baseEnd_2652626 : Nat := 100894232193588431279689

theorem tailTrace_2652626 : CollatzResearch.WordTrace tailWord_2652626 prefixEnd_2652626 100894232193588431279689 := by
  unfold tailWord_2652626
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187304621999127324538433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64499478991997672865435821 24187304621999127324538433)
  ·
    refine ⟨18140478466499345493403825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24187304621999127324538433 18140478466499345493403825)
    ·
      refine ⟨13605358849874509120052869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18140478466499345493403825 13605358849874509120052869)
      ·
        refine ⟨2551004784351470460009913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13605358849874509120052869 2551004784351470460009913)
        ·
          refine ⟨1913253588263602845007435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551004784351470460009913 1913253588263602845007435)
          ·
            refine ⟨2869880382395404267511153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913253588263602845007435 2869880382395404267511153)
            ·
              refine ⟨2152410286796553200633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869880382395404267511153 2152410286796553200633365)
              ·
                refine ⟨100894232193588431279689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2152410286796553200633365 100894232193588431279689)
                ·
                  rfl

theorem cell22_2652626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_2652626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652626 prefixEnd_2652626 := by exact prefixLift 2652626
  have htrace : WordTrace (prefixWord ++ tailWord_2652626) baseStart_2652626 baseEnd_2652626 := by
    simpa [prefixWord, tailWord_2652626, baseEnd_2652626] using wordTrace_append hprefix tailTrace_2652626
  have hstable : (prefixWord ++ tailWord_2652626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652626).length < 2 ^ (prefixWord ++ tailWord_2652626).sum := by decide
  have hdescent : baseEnd_2652626 < baseStart_2652626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652658 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_2652658 : Nat := 118140960795 + 2652658 * 2 ^ 59
def prefixEnd_2652658 : Nat := 4983230072969 + 3 ^ 40 * 2652658 * 2
def baseEnd_2652658 : Nat := 908059043996258464717103

theorem tailTrace_2652658 : CollatzResearch.WordTrace tailWord_2652658 prefixEnd_2652658 908059043996258464717103 := by
  unfold tailWord_2652658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187596405970144690829657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64500257082587052508879085 24187596405970144690829657)
  ·
    refine ⟨18140697304477608518122243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24187596405970144690829657 18140697304477608518122243)
    ·
      refine ⟨27211045956716412777183365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18140697304477608518122243 27211045956716412777183365)
      ·
        refine ⟨5102071116884327395721881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27211045956716412777183365 5102071116884327395721881)
        ·
          refine ⟨3826553337663245546791411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102071116884327395721881 3826553337663245546791411)
          ·
            refine ⟨5739830006494868320187117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826553337663245546791411 5739830006494868320187117)
            ·
              refine ⟨2152436252435575620070169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5739830006494868320187117 2152436252435575620070169)
              ·
                refine ⟨1614327189326681715052627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152436252435575620070169 1614327189326681715052627)
                ·
                  refine ⟨2421490783990022572578941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614327189326681715052627 2421490783990022572578941)
                  ·
                    refine ⟨908059043996258464717103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421490783990022572578941 908059043996258464717103)
                    ·
                      rfl

theorem cell22_2652658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_2652658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652658 prefixEnd_2652658 := by exact prefixLift 2652658
  have htrace : WordTrace (prefixWord ++ tailWord_2652658) baseStart_2652658 baseEnd_2652658 := by
    simpa [prefixWord, tailWord_2652658, baseEnd_2652658] using wordTrace_append hprefix tailTrace_2652658
  have hstable : (prefixWord ++ tailWord_2652658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652658).length < 2 ^ (prefixWord ++ tailWord_2652658).sum := by decide
  have hdescent : baseEnd_2652658 < baseStart_2652658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652665 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 6]
def baseStart_2652665 : Nat := 118140960795 + 2652665 * 2 ^ 59
def prefixEnd_2652665 : Nat := 4983230072969 + 3 ^ 40 * 2652665 * 2
def baseEnd_2652665 : Nat := 302687146746437593264027

theorem tailTrace_2652665 : CollatzResearch.WordTrace tailWord_2652665 prefixEnd_2652665 302687146746437593264027 := by
  unfold tailWord_2652665
  simp only [CollatzResearch.WordTrace]
  refine ⟨96750640934855218958823449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64500427289903479305882299 96750640934855218958823449)
  ·
    refine ⟨72562980701141414219117587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96750640934855218958823449 72562980701141414219117587)
    ·
      refine ⟨108844471051712121328676381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72562980701141414219117587 108844471051712121328676381)
      ·
        refine ⟨40816676644392045498253643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108844471051712121328676381 40816676644392045498253643)
        ·
          refine ⟨61225014966588068247380465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40816676644392045498253643 61225014966588068247380465)
          ·
            refine ⟨45918761224941051185535349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61225014966588068247380465 45918761224941051185535349)
            ·
              refine ⟨4304883864838223548643939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45918761224941051185535349 4304883864838223548643939)
              ·
                refine ⟨6457325797257335322965909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304883864838223548643939 6457325797257335322965909)
                ·
                  refine ⟨302687146746437593264027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6457325797257335322965909 302687146746437593264027)
                  ·
                    rfl

theorem cell22_2652665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_2652665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652665 prefixEnd_2652665 := by exact prefixLift 2652665
  have htrace : WordTrace (prefixWord ++ tailWord_2652665) baseStart_2652665 baseEnd_2652665 := by
    simpa [prefixWord, tailWord_2652665, baseEnd_2652665] using wordTrace_append hprefix tailTrace_2652665
  have hstable : (prefixWord ++ tailWord_2652665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652665).length < 2 ^ (prefixWord ++ tailWord_2652665).sum := by decide
  have hdescent : baseEnd_2652665 < baseStart_2652665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652680 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2652680 : Nat := 118140960795 + 2652680 * 2 ^ 59
def prefixEnd_2652680 : Nat := 4983230072969 + 3 ^ 40 * 2652680 * 2
def baseEnd_2652680 : Nat := 908066575045857740667035

theorem tailTrace_2652680 : CollatzResearch.WordTrace tailWord_2652680 prefixEnd_2652680 908066575045857740667035 := by
  unfold tailWord_2652680
  simp only [CollatzResearch.WordTrace]
  refine ⟨48375594014900438260309747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64500792019867251013746329 48375594014900438260309747)
  ·
    refine ⟨72563391022350657390464621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48375594014900438260309747 72563391022350657390464621)
    ·
      refine ⟨27211271633381496521424233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72563391022350657390464621 27211271633381496521424233)
      ·
        refine ⟨20408453725036122391068175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27211271633381496521424233 20408453725036122391068175)
        ·
          refine ⟨30612680587554183586602263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20408453725036122391068175 30612680587554183586602263)
          ·
            refine ⟨45919020881331275379903395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30612680587554183586602263 45919020881331275379903395)
            ·
              refine ⟨68878531321996913069855093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45919020881331275379903395 68878531321996913069855093)
              ·
                refine ⟨6457362311437210600298915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68878531321996913069855093 6457362311437210600298915)
                ·
                  refine ⟨9686043467155815900448373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457362311437210600298915 9686043467155815900448373)
                  ·
                    refine ⟨908066575045857740667035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9686043467155815900448373 908066575045857740667035)
                    ·
                      rfl

theorem cell22_2652680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2652680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652680 prefixEnd_2652680 := by exact prefixLift 2652680
  have htrace : WordTrace (prefixWord ++ tailWord_2652680) baseStart_2652680 baseEnd_2652680 := by
    simpa [prefixWord, tailWord_2652680, baseEnd_2652680] using wordTrace_append hprefix tailTrace_2652680
  have hstable : (prefixWord ++ tailWord_2652680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652680).length < 2 ^ (prefixWord ++ tailWord_2652680).sum := by decide
  have hdescent : baseEnd_2652680 < baseStart_2652680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652684 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_2652684 : Nat := 118140960795 + 2652684 * 2 ^ 59
def prefixEnd_2652684 : Nat := 4983230072969 + 3 ^ 40 * 2652684 * 2
def baseEnd_2652684 : Nat := 908067944327603063567023

theorem tailTrace_2652684 : CollatzResearch.WordTrace tailWord_2652684 prefixEnd_2652684 908067944327603063567023 := by
  unfold tailWord_2652684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48375666960893192601882553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64500889281190923469176737 48375666960893192601882553)
  ·
    refine ⟨36281750220669894451411915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48375666960893192601882553 36281750220669894451411915)
    ·
      refine ⟨54422625331004841677117873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36281750220669894451411915 54422625331004841677117873)
      ·
        refine ⟨40816968998253631257838405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54422625331004841677117873 40816968998253631257838405)
        ·
          refine ⟨7653181687172555860844701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40816968998253631257838405 7653181687172555860844701)
          ·
            refine ⟨2869943132689708447816763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7653181687172555860844701 2869943132689708447816763)
            ·
              refine ⟨4304914699034562671725145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869943132689708447816763 4304914699034562671725145)
              ·
                refine ⟨3228686024275922003793859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304914699034562671725145 3228686024275922003793859)
                ·
                  refine ⟨4843029036413883005690789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228686024275922003793859 4843029036413883005690789)
                  ·
                    refine ⟨908067944327603063567023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843029036413883005690789 908067944327603063567023)
                    ·
                      rfl

theorem cell22_2652684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_2652684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652684 prefixEnd_2652684 := by exact prefixLift 2652684
  have htrace : WordTrace (prefixWord ++ tailWord_2652684) baseStart_2652684 baseEnd_2652684 := by
    simpa [prefixWord, tailWord_2652684, baseEnd_2652684] using wordTrace_append hprefix tailTrace_2652684
  have hstable : (prefixWord ++ tailWord_2652684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652684).length < 2 ^ (prefixWord ++ tailWord_2652684).sum := by decide
  have hdescent : baseEnd_2652684 < baseStart_2652684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652714 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2652714 : Nat := 118140960795 + 2652714 * 2 ^ 59
def prefixEnd_2652714 : Nat := 4983230072969 + 3 ^ 40 * 2652714 * 2
def baseEnd_2652714 : Nat := 908078213940692985316931

theorem tailTrace_2652714 : CollatzResearch.WordTrace tailWord_2652714 prefixEnd_2652714 908078213940692985316931 := by
  unfold tailWord_2652714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188107027919425081839299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64501618741118466884904797 24188107027919425081839299)
  ·
    refine ⟨36282160541879137622758949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24188107027919425081839299 36282160541879137622758949)
    ·
      refine ⟨6802905101602338304267303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36282160541879137622758949 6802905101602338304267303)
      ·
        refine ⟨10204357652403507456400955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802905101602338304267303 10204357652403507456400955)
        ·
          refine ⟨15306536478605261184601433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10204357652403507456400955 15306536478605261184601433)
          ·
            refine ⟨11479902358953945888451075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15306536478605261184601433 11479902358953945888451075)
            ·
              refine ⟨17219853538430918832676613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11479902358953945888451075 17219853538430918832676613)
              ·
                refine ⟨3228722538455797281126865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17219853538430918832676613 3228722538455797281126865)
                ·
                  refine ⟨2421541903841847960845149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228722538455797281126865 2421541903841847960845149)
                  ·
                    refine ⟨908078213940692985316931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421541903841847960845149 908078213940692985316931)
                    ·
                      rfl

theorem cell22_2652714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2652714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652714 prefixEnd_2652714 := by exact prefixLift 2652714
  have htrace : WordTrace (prefixWord ++ tailWord_2652714) baseStart_2652714 baseEnd_2652714 := by
    simpa [prefixWord, tailWord_2652714, baseEnd_2652714] using wordTrace_append hprefix tailTrace_2652714
  have hstable : (prefixWord ++ tailWord_2652714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652714).length < 2 ^ (prefixWord ++ tailWord_2652714).sum := by decide
  have hdescent : baseEnd_2652714 < baseStart_2652714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652776 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2652776 : Nat := 118140960795 + 2652776 * 2 ^ 59
def prefixEnd_2652776 : Nat := 4983230072969 + 3 ^ 40 * 2652776 * 2
def baseEnd_2652776 : Nat := 908099437807745490266741

theorem tailTrace_2652776 : CollatzResearch.WordTrace tailWord_2652776 prefixEnd_2652776 908099437807745490266741 := by
  unfold tailWord_2652776
  simp only [CollatzResearch.WordTrace]
  refine ⟨48377344718726542458057091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64503126291635389944076121 48377344718726542458057091)
  ·
    refine ⟨72566017078089813687085637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48377344718726542458057091 72566017078089813687085637)
    ·
      refine ⟨13606128202141840066328557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72566017078089813687085637 13606128202141840066328557)
      ·
        refine ⟨5102298075803190024873209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13606128202141840066328557 5102298075803190024873209)
        ·
          refine ⟨3826723556852392518654907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102298075803190024873209 3826723556852392518654907)
          ·
            refine ⟨5740085335278588777982361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826723556852392518654907 5740085335278588777982361)
            ·
              refine ⟨4305064001458941583486771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740085335278588777982361 4305064001458941583486771)
              ·
                refine ⟨6457596002188412375230157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305064001458941583486771 6457596002188412375230157)
                ·
                  refine ⟨2421598500820654640711309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6457596002188412375230157 2421598500820654640711309)
                  ·
                    refine ⟨908099437807745490266741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421598500820654640711309 908099437807745490266741)
                    ·
                      rfl

theorem cell22_2652776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2652776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652776 prefixEnd_2652776 := by exact prefixLift 2652776
  have htrace : WordTrace (prefixWord ++ tailWord_2652776) baseStart_2652776 baseEnd_2652776 := by
    simpa [prefixWord, tailWord_2652776, baseEnd_2652776] using wordTrace_append hprefix tailTrace_2652776
  have hstable : (prefixWord ++ tailWord_2652776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652776).length < 2 ^ (prefixWord ++ tailWord_2652776).sum := by decide
  have hdescent : baseEnd_2652776 < baseStart_2652776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652810 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2652810 : Nat := 118140960795 + 2652810 * 2 ^ 59
def prefixEnd_2652810 : Nat := 4983230072969 + 3 ^ 40 * 2652810 * 2
def baseEnd_2652810 : Nat := 908111076702580734916637

theorem tailTrace_2652810 : CollatzResearch.WordTrace tailWord_2652810 prefixEnd_2652810 908111076702580734916637 := by
  unfold tailWord_2652810
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188982379832477180712971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64503953012886605815234589 24188982379832477180712971)
  ·
    refine ⟨36283473569748715771069457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24188982379832477180712971 36283473569748715771069457)
    ·
      refine ⟨27212605177311536828302093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36283473569748715771069457 27212605177311536828302093)
      ·
        refine ⟨10204726941491826310613285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27212605177311536828302093 10204726941491826310613285)
        ·
          refine ⟨1913386301529717433239991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10204726941491826310613285 1913386301529717433239991)
          ·
            refine ⟨2870079452294576149859987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913386301529717433239991 2870079452294576149859987)
            ·
              refine ⟨4305119178441864224789981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870079452294576149859987 4305119178441864224789981)
              ·
                refine ⟨1614419691915699084296243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4305119178441864224789981 1614419691915699084296243)
                ·
                  refine ⟨2421629537873548626444365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614419691915699084296243 2421629537873548626444365)
                  ·
                    refine ⟨908111076702580734916637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421629537873548626444365 908111076702580734916637)
                    ·
                      rfl

theorem cell22_2652810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2652810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652810 prefixEnd_2652810 := by exact prefixLift 2652810
  have htrace : WordTrace (prefixWord ++ tailWord_2652810) baseStart_2652810 baseEnd_2652810 := by
    simpa [prefixWord, tailWord_2652810, baseEnd_2652810] using wordTrace_append hprefix tailTrace_2652810
  have hstable : (prefixWord ++ tailWord_2652810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652810).length < 2 ^ (prefixWord ++ tailWord_2652810).sum := by decide
  have hdescent : baseEnd_2652810 < baseStart_2652810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652862 : List Nat := [4, 2, 1, 1, 2, 1, 1, 10]
def baseStart_2652862 : Nat := 118140960795 + 2652862 * 2 ^ 59
def prefixEnd_2652862 : Nat := 4983230072969 + 3 ^ 40 * 2652862 * 2
def baseEnd_2652862 : Nat := 100903208596141103624053

theorem tailTrace_2652862 : CollatzResearch.WordTrace tailWord_2652862 prefixEnd_2652862 100903208596141103624053 := by
  unfold tailWord_2652862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094728264392690200468105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64505217410094347735829893 12094728264392690200468105)
  ·
    refine ⟨9071046198294517650351079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12094728264392690200468105 9071046198294517650351079)
    ·
      refine ⟨13606569297441776475526619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071046198294517650351079 13606569297441776475526619)
      ·
        refine ⟨20409853946162664713289929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606569297441776475526619 20409853946162664713289929)
        ·
          refine ⟨15307390459621998534967447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20409853946162664713289929 15307390459621998534967447)
          ·
            refine ⟨22961085689432997802451171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307390459621998534967447 22961085689432997802451171)
            ·
              refine ⟨34441628534149496703676757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22961085689432997802451171 34441628534149496703676757)
              ·
                refine ⟨100903208596141103624053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34441628534149496703676757 100903208596141103624053)
                ·
                  rfl

theorem cell22_2652862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_2652862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652862 prefixEnd_2652862 := by exact prefixLift 2652862
  have htrace : WordTrace (prefixWord ++ tailWord_2652862) baseStart_2652862 baseEnd_2652862 := by
    simpa [prefixWord, tailWord_2652862, baseEnd_2652862] using wordTrace_append hprefix tailTrace_2652862
  have hstable : (prefixWord ++ tailWord_2652862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652862).length < 2 ^ (prefixWord ++ tailWord_2652862).sum := by decide
  have hdescent : baseEnd_2652862 < baseStart_2652862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652864 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_2652864 : Nat := 118140960795 + 2652864 * 2 ^ 59
def prefixEnd_2652864 : Nat := 4983230072969 + 3 ^ 40 * 2652864 * 2
def baseEnd_2652864 : Nat := 908129562006142594066471

theorem tailTrace_2652864 : CollatzResearch.WordTrace tailWord_2652864 prefixEnd_2652864 908129562006142594066471 := by
  unfold tailWord_2652864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48378949530567137972658823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64505266040756183963545097 48378949530567137972658823)
  ·
    refine ⟨72568424295850706958988235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48378949530567137972658823 72568424295850706958988235)
    ·
      refine ⟨108852636443776060438482353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72568424295850706958988235 108852636443776060438482353)
      ·
        refine ⟨81639477332832045328861765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108852636443776060438482353 81639477332832045328861765)
        ·
          refine ⟨15307401999906008499161581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81639477332832045328861765 15307401999906008499161581)
          ·
            refine ⟨5740275749964753187185593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15307401999906008499161581 5740275749964753187185593)
            ·
              refine ⟨4305206812473564890389195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740275749964753187185593 4305206812473564890389195)
              ·
                refine ⟨6457810218710347335583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305206812473564890389195 6457810218710347335583793)
                ·
                  refine ⟨4843357664032760501687845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457810218710347335583793 4843357664032760501687845)
                  ·
                    refine ⟨908129562006142594066471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843357664032760501687845 908129562006142594066471)
                    ·
                      rfl

theorem cell22_2652864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_2652864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652864 prefixEnd_2652864 := by exact prefixLift 2652864
  have htrace : WordTrace (prefixWord ++ tailWord_2652864) baseStart_2652864 baseEnd_2652864 := by
    simpa [prefixWord, tailWord_2652864, baseEnd_2652864] using wordTrace_append hprefix tailTrace_2652864
  have hstable : (prefixWord ++ tailWord_2652864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652864).length < 2 ^ (prefixWord ++ tailWord_2652864).sum := by decide
  have hdescent : baseEnd_2652864 < baseStart_2652864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652885 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 4]
def baseStart_2652885 : Nat := 118140960795 + 2652885 * 2 ^ 59
def prefixEnd_2652885 : Nat := 4983230072969 + 3 ^ 40 * 2652885 * 2
def baseEnd_2652885 : Nat := 302712250245101846430469

theorem tailTrace_2652885 : CollatzResearch.WordTrace tailWord_2652885 prefixEnd_2652885 302712250245101846430469 := by
  unfold tailWord_2652885
  simp only [CollatzResearch.WordTrace]
  refine ⟨96758664994058196531832109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64505776662705464354554739 96758664994058196531832109)
  ·
    refine ⟨36284499372771823699437041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96758664994058196531832109 36284499372771823699437041)
    ·
      refine ⟨27213374529578867774577781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36284499372771823699437041 27213374529578867774577781)
      ·
        refine ⟨2551253862148018853866667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27213374529578867774577781 2551253862148018853866667)
        ·
          refine ⟨3826880793222028280800001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551253862148018853866667 3826880793222028280800001)
          ·
            refine ⟨2870160594916521210600001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3826880793222028280800001 2870160594916521210600001)
            ·
              refine ⟨2152620446187390907950001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870160594916521210600001 2152620446187390907950001)
              ·
                refine ⟨1614465334640543180962501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152620446187390907950001 1614465334640543180962501)
                ·
                  refine ⟨302712250245101846430469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614465334640543180962501 302712250245101846430469)
                  ·
                    rfl

theorem cell22_2652885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_2652885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652885 prefixEnd_2652885 := by exact prefixLift 2652885
  have htrace : WordTrace (prefixWord ++ tailWord_2652885) baseStart_2652885 baseEnd_2652885 := by
    simpa [prefixWord, tailWord_2652885, baseEnd_2652885] using wordTrace_append hprefix tailTrace_2652885
  have hstable : (prefixWord ++ tailWord_2652885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652885).length < 2 ^ (prefixWord ++ tailWord_2652885).sum := by decide
  have hdescent : baseEnd_2652885 < baseStart_2652885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2652984 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_2652984 : Nat := 118140960795 + 2652984 * 2 ^ 59
def prefixEnd_2652984 : Nat := 4983230072969 + 3 ^ 40 * 2652984 * 2
def baseEnd_2652984 : Nat := 908170640458502281066103

theorem tailTrace_2652984 : CollatzResearch.WordTrace tailWord_2652984 prefixEnd_2652984 908170640458502281066103 := by
  unfold tailWord_2652984
  simp only [CollatzResearch.WordTrace]
  refine ⟨48381137910349768219843003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64508183880466357626457337 48381137910349768219843003)
  ·
    refine ⟨72571706865524652329764505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48381137910349768219843003 72571706865524652329764505)
    ·
      refine ⟨54428780149143489247323379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72571706865524652329764505 54428780149143489247323379)
      ·
        refine ⟨81643170223715233870985069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54428780149143489247323379 81643170223715233870985069)
        ·
          refine ⟨30616188833893212701619401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81643170223715233870985069 30616188833893212701619401)
          ·
            refine ⟨22962141625419909526214551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30616188833893212701619401 22962141625419909526214551)
            ·
              refine ⟨34443212438129864289321827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22962141625419909526214551 34443212438129864289321827)
              ·
                refine ⟨51664818657194796433982741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34443212438129864289321827 51664818657194796433982741)
                ·
                  refine ⟨2421788374556006082842941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51664818657194796433982741 2421788374556006082842941)
                  ·
                    refine ⟨908170640458502281066103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421788374556006082842941 908170640458502281066103)
                    ·
                      rfl

theorem cell22_2652984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_2652984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2652984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2652984 prefixEnd_2652984 := by exact prefixLift 2652984
  have htrace : WordTrace (prefixWord ++ tailWord_2652984) baseStart_2652984 baseEnd_2652984 := by
    simpa [prefixWord, tailWord_2652984, baseEnd_2652984] using wordTrace_append hprefix tailTrace_2652984
  have hstable : (prefixWord ++ tailWord_2652984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2652984).length < 2 ^ (prefixWord ++ tailWord_2652984).sum := by decide
  have hdescent : baseEnd_2652984 < baseStart_2652984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2652984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653018 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_2653018 : Nat := 118140960795 + 2653018 * 2 ^ 59
def prefixEnd_2653018 : Nat := 4983230072969 + 3 ^ 40 * 2653018 * 2
def baseEnd_2653018 : Nat := 908182279353337525715999

theorem tailTrace_2653018 : CollatzResearch.WordTrace tailWord_2653018 prefixEnd_2653018 908182279353337525715999 := by
  unfold tailWord_2653018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24190878975644090061605927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64509010601717573497615805 24190878975644090061605927)
  ·
    refine ⟨36286318463466135092408891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24190878975644090061605927 36286318463466135092408891)
    ·
      refine ⟨54429477695199202638613337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36286318463466135092408891 54429477695199202638613337)
      ·
        refine ⟨40822108271399401978960003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54429477695199202638613337 40822108271399401978960003)
        ·
          refine ⟨61233162407099102968440005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40822108271399401978960003 61233162407099102968440005)
          ·
            refine ⟨11481217951331081806582501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61233162407099102968440005 11481217951331081806582501)
            ·
              refine ⟨2152728365874577838734219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11481217951331081806582501 2152728365874577838734219)
              ·
                refine ⟨3229092548811866758101329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152728365874577838734219 3229092548811866758101329)
                ·
                  refine ⟨2421819411608900068575997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229092548811866758101329 2421819411608900068575997)
                  ·
                    refine ⟨908182279353337525715999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421819411608900068575997 908182279353337525715999)
                    ·
                      rfl

theorem cell22_2653018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_2653018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653018 prefixEnd_2653018 := by exact prefixLift 2653018
  have htrace : WordTrace (prefixWord ++ tailWord_2653018) baseStart_2653018 baseEnd_2653018 := by
    simpa [prefixWord, tailWord_2653018, baseEnd_2653018] using wordTrace_append hprefix tailTrace_2653018
  have hstable : (prefixWord ++ tailWord_2653018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653018).length < 2 ^ (prefixWord ++ tailWord_2653018).sum := by decide
  have hdescent : baseEnd_2653018 < baseStart_2653018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653054 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2653054 : Nat := 118140960795 + 2653054 * 2 ^ 59
def prefixEnd_2653054 : Nat := 4983230072969 + 3 ^ 40 * 2653054 * 2
def baseEnd_2653054 : Nat := 302731534296348477271963

theorem tailTrace_2653054 : CollatzResearch.WordTrace tailWord_2653054 prefixEnd_2653054 302731534296348477271963 := by
  unfold tailWord_2653054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095603616305742299341777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64509885953630625596489477 12095603616305742299341777)
  ·
    refine ⟨9071702712229306724506333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12095603616305742299341777 9071702712229306724506333)
    ·
      refine ⟨3401888517085990021689875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9071702712229306724506333 3401888517085990021689875)
      ·
        refine ⟨5102832775628985032534813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401888517085990021689875 5102832775628985032534813)
        ·
          refine ⟨1913562290860869387200555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5102832775628985032534813 1913562290860869387200555)
          ·
            refine ⟨2870343436291304080800833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913562290860869387200555 2870343436291304080800833)
            ·
              refine ⟨2152757577218478060600625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870343436291304080800833 2152757577218478060600625)
              ·
                refine ⟨1614568182913858545450469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152757577218478060600625 1614568182913858545450469)
                ·
                  refine ⟨302731534296348477271963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614568182913858545450469 302731534296348477271963)
                  ·
                    rfl

theorem cell22_2653054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2653054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653054 prefixEnd_2653054 := by exact prefixLift 2653054
  have htrace : WordTrace (prefixWord ++ tailWord_2653054) baseStart_2653054 baseEnd_2653054 := by
    simpa [prefixWord, tailWord_2653054, baseEnd_2653054] using wordTrace_append hprefix tailTrace_2653054
  have hstable : (prefixWord ++ tailWord_2653054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653054).length < 2 ^ (prefixWord ++ tailWord_2653054).sum := by decide
  have hdescent : baseEnd_2653054 < baseStart_2653054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653076 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2653076 : Nat := 118140960795 + 2653076 * 2 ^ 59
def prefixEnd_2653076 : Nat := 4983230072969 + 3 ^ 40 * 2653076 * 2
def baseEnd_2653076 : Nat := 302734044646214902588607

theorem tailTrace_2653076 : CollatzResearch.WordTrace tailWord_2653076 prefixEnd_2653076 302734044646214902588607 := by
  unfold tailWord_2653076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382815668183118076017541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64510420890910824101356721 48382815668183118076017541)
  ·
    refine ⟨9071777937784334639253289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48382815668183118076017541 9071777937784334639253289)
    ·
      refine ⟨6803833453338250979439967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9071777937784334639253289 6803833453338250979439967)
      ·
        refine ⟨10205750180007376469159951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803833453338250979439967 10205750180007376469159951)
        ·
          refine ⟨15308625270011064703739927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205750180007376469159951 15308625270011064703739927)
          ·
            refine ⟨22962937905016597055609891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15308625270011064703739927 22962937905016597055609891)
            ·
              refine ⟨34444406857524895583414837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22962937905016597055609891 34444406857524895583414837)
              ·
                refine ⟨3229163142892958960945141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34444406857524895583414837 3229163142892958960945141)
                ·
                  refine ⟨302734044646214902588607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3229163142892958960945141 302734044646214902588607)
                  ·
                    rfl

theorem cell22_2653076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2653076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653076 prefixEnd_2653076 := by exact prefixLift 2653076
  have htrace : WordTrace (prefixWord ++ tailWord_2653076) baseStart_2653076 baseEnd_2653076 := by
    simpa [prefixWord, tailWord_2653076, baseEnd_2653076] using wordTrace_append hprefix tailTrace_2653076
  have hstable : (prefixWord ++ tailWord_2653076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653076).length < 2 ^ (prefixWord ++ tailWord_2653076).sum := by decide
  have hdescent : baseEnd_2653076 < baseStart_2653076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653108 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2653108 : Nat := 118140960795 + 2653108 * 2 ^ 59
def prefixEnd_2653108 : Nat := 4983230072969 + 3 ^ 40 * 2653108 * 2
def baseEnd_2653108 : Nat := 908213088192607290965723

theorem tailTrace_2653108 : CollatzResearch.WordTrace tailWord_2653108 prefixEnd_2653108 908213088192607290965723 := by
  unfold tailWord_2653108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48383399236125152808599989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64511198981500203744799985 48383399236125152808599989)
  ·
    refine ⟨4535943678386733075806249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48383399236125152808599989 4535943678386733075806249)
    ·
      refine ⟨3401957758790049806854687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535943678386733075806249 3401957758790049806854687)
      ·
        refine ⟨5102936638185074710282031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401957758790049806854687 5102936638185074710282031)
        ·
          refine ⟨7654404957277612065423047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102936638185074710282031 7654404957277612065423047)
          ·
            refine ⟨11481607435916418098134571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654404957277612065423047 11481607435916418098134571)
            ·
              refine ⟨17222411153874627147201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11481607435916418098134571 17222411153874627147201857)
              ·
                refine ⟨12916808365405970360401393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17222411153874627147201857 12916808365405970360401393)
                ·
                  refine ⟨9687606274054477770301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12916808365405970360401393 9687606274054477770301045)
                  ·
                    refine ⟨908213088192607290965723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9687606274054477770301045 908213088192607290965723)
                    ·
                      rfl

theorem cell22_2653108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2653108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653108 prefixEnd_2653108 := by exact prefixLift 2653108
  have htrace : WordTrace (prefixWord ++ tailWord_2653108) baseStart_2653108 baseEnd_2653108 := by
    simpa [prefixWord, tailWord_2653108, baseEnd_2653108] using wordTrace_append hprefix tailTrace_2653108
  have hstable : (prefixWord ++ tailWord_2653108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653108).length < 2 ^ (prefixWord ++ tailWord_2653108).sum := by decide
  have hdescent : baseEnd_2653108 < baseStart_2653108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653179 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_2653179 : Nat := 118140960795 + 2653179 * 2 ^ 59
def prefixEnd_2653179 : Nat := 4983230072969 + 3 ^ 40 * 2653179 * 2
def baseEnd_2653179 : Nat := 908237392943586772440505

theorem tailTrace_2653179 : CollatzResearch.WordTrace tailWord_2653179 prefixEnd_2653179 908237392943586772440505 := by
  unfold tailWord_2653179
  simp only [CollatzResearch.WordTrace]
  refine ⟨96769388054993084743034591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64512925369995389828689727 96769388054993084743034591)
  ·
    refine ⟨145154082082489627114551887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96769388054993084743034591 145154082082489627114551887)
    ·
      refine ⟨217731123123734440671827831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145154082082489627114551887 217731123123734440671827831)
      ·
        refine ⟨326596684685601661007741747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217731123123734440671827831 326596684685601661007741747)
        ·
          refine ⟨489895027028402491511612621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326596684685601661007741747 489895027028402491511612621)
          ·
            refine ⟨183710635135650934316854733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489895027028402491511612621 183710635135650934316854733)
            ·
              refine ⟨68891488175869100368820525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183710635135650934316854733 68891488175869100368820525)
              ·
                refine ⟨25834308065950912638307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68891488175869100368820525 25834308065950912638307697)
                ·
                  refine ⟨19375731049463184478730773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25834308065950912638307697 19375731049463184478730773)
                  ·
                    refine ⟨908237392943586772440505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19375731049463184478730773 908237392943586772440505)
                    ·
                      rfl

theorem cell22_2653179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_2653179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653179 prefixEnd_2653179 := by exact prefixLift 2653179
  have htrace : WordTrace (prefixWord ++ tailWord_2653179) baseStart_2653179 baseEnd_2653179 := by
    simpa [prefixWord, tailWord_2653179, baseEnd_2653179] using wordTrace_append hprefix tailTrace_2653179
  have hstable : (prefixWord ++ tailWord_2653179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653179).length < 2 ^ (prefixWord ++ tailWord_2653179).sum := by decide
  have hdescent : baseEnd_2653179 < baseStart_2653179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653256 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_2653256 : Nat := 118140960795 + 2653256 * 2 ^ 59
def prefixEnd_2653256 : Nat := 4983230072969 + 3 ^ 40 * 2653256 * 2
def baseEnd_2653256 : Nat := 302754583872394746088423

theorem tailTrace_2653256 : CollatzResearch.WordTrace tailWord_2653256 prefixEnd_2653256 302754583872394746088423 := by
  unfold tailWord_2653256
  simp only [CollatzResearch.WordTrace]
  refine ⟨48386098237857063446793811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64514797650476084595725081 48386098237857063446793811)
  ·
    refine ⟨72579147356785595170190717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48386098237857063446793811 72579147356785595170190717)
    ·
      refine ⟨27217180258794598188821519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72579147356785595170190717 27217180258794598188821519)
      ·
        refine ⟨40825770388191897283232279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27217180258794598188821519 40825770388191897283232279)
        ·
          refine ⟨61238655582287845924848419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40825770388191897283232279 61238655582287845924848419)
          ·
            refine ⟨91857983373431768887272629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61238655582287845924848419 91857983373431768887272629)
            ·
              refine ⟨8611685941259228333181809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91857983373431768887272629 8611685941259228333181809)
              ·
                refine ⟨6458764455944421249886357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611685941259228333181809 6458764455944421249886357)
                ·
                  refine ⟨302754583872394746088423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6458764455944421249886357 302754583872394746088423)
                  ·
                    rfl

theorem cell22_2653256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_2653256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653256 prefixEnd_2653256 := by exact prefixLift 2653256
  have htrace : WordTrace (prefixWord ++ tailWord_2653256) baseStart_2653256 baseEnd_2653256 := by
    simpa [prefixWord, tailWord_2653256, baseEnd_2653256] using wordTrace_append hprefix tailTrace_2653256
  have hstable : (prefixWord ++ tailWord_2653256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653256).length < 2 ^ (prefixWord ++ tailWord_2653256).sum := by decide
  have hdescent : baseEnd_2653256 < baseStart_2653256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653290 : List Nat := [3, 1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_2653290 : Nat := 118140960795 + 2653290 * 2 ^ 59
def prefixEnd_2653290 : Nat := 4983230072969 + 3 ^ 40 * 2653290 * 2
def baseEnd_2653290 : Nat := 302758463504006494305055

theorem tailTrace_2653290 : CollatzResearch.WordTrace tailWord_2653290 prefixEnd_2653290 302758463504006494305055 := by
  unfold tailWord_2653290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24193359139397737675081331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64515624371727300466883549 24193359139397737675081331)
  ·
    refine ⟨36290038709096606512621997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24193359139397737675081331 36290038709096606512621997)
    ·
      refine ⟨13608764515911227442233249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36290038709096606512621997 13608764515911227442233249)
      ·
        refine ⟨10206573386933420581674937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13608764515911227442233249 10206573386933420581674937)
        ·
          refine ⟨7654930040200065436256203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10206573386933420581674937 7654930040200065436256203)
          ·
            refine ⟨11482395060300098154384305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654930040200065436256203 11482395060300098154384305)
            ·
              refine ⟨8611796295225073615788229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11482395060300098154384305 8611796295225073615788229)
              ·
                refine ⟨1614711805354701302960293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8611796295225073615788229 1614711805354701302960293)
                ·
                  refine ⟨302758463504006494305055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614711805354701302960293 302758463504006494305055)
                  ·
                    rfl

theorem cell22_2653290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_2653290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653290 prefixEnd_2653290 := by exact prefixLift 2653290
  have htrace : WordTrace (prefixWord ++ tailWord_2653290) baseStart_2653290 baseEnd_2653290 := by
    simpa [prefixWord, tailWord_2653290, baseEnd_2653290] using wordTrace_append hprefix tailTrace_2653290
  have hstable : (prefixWord ++ tailWord_2653290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653290).length < 2 ^ (prefixWord ++ tailWord_2653290).sum := by decide
  have hdescent : baseEnd_2653290 < baseStart_2653290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653305 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_2653305 : Nat := 118140960795 + 2653305 * 2 ^ 59
def prefixEnd_2653305 : Nat := 4983230072969 + 3 ^ 40 * 2653305 * 2
def baseEnd_2653305 : Nat := 908280525318564443790119

theorem tailTrace_2653305 : CollatzResearch.WordTrace tailWord_2653305 prefixEnd_2653305 908280525318564443790119 := by
  unfold tailWord_2653305
  simp only [CollatzResearch.WordTrace]
  refine ⟨96773983652536608262121369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64515989101691072174747579 96773983652536608262121369)
  ·
    refine ⟨72580487739402456196591027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96773983652536608262121369 72580487739402456196591027)
    ·
      refine ⟨108870731609103684294886541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72580487739402456196591027 108870731609103684294886541)
      ·
        refine ⟨40826524353413881610582453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108870731609103684294886541 40826524353413881610582453)
        ·
          refine ⟨3827486658132551400992105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40826524353413881610582453 3827486658132551400992105)
          ·
            refine ⟨2870614993599413550744079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3827486658132551400992105 2870614993599413550744079)
            ·
              refine ⟨4305922490399120326116119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870614993599413550744079 4305922490399120326116119)
              ·
                refine ⟨6458883735598680489174179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305922490399120326116119 6458883735598680489174179)
                ·
                  refine ⟨9688325603398020733761269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458883735598680489174179 9688325603398020733761269)
                  ·
                    refine ⟨908280525318564443790119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9688325603398020733761269 908280525318564443790119)
                    ·
                      rfl

theorem cell22_2653305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_2653305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653305 prefixEnd_2653305 := by exact prefixLift 2653305
  have htrace : WordTrace (prefixWord ++ tailWord_2653305) baseStart_2653305 baseEnd_2653305 := by
    simpa [prefixWord, tailWord_2653305, baseEnd_2653305] using wordTrace_append hprefix tailTrace_2653305
  have hstable : (prefixWord ++ tailWord_2653305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653305).length < 2 ^ (prefixWord ++ tailWord_2653305).sum := by decide
  have hdescent : baseEnd_2653305 < baseStart_2653305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653391 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 10]
def baseStart_2653391 : Nat := 118140960795 + 2653391 * 2 ^ 59
def prefixEnd_2653391 : Nat := 4983230072969 + 3 ^ 40 * 2653391 * 2
def baseEnd_2653391 : Nat := 302769988292029628713285

theorem tailTrace_2653391 : CollatzResearch.WordTrace tailWord_2653391 prefixEnd_2653391 302769988292029628713285 := by
  unfold tailWord_2653391
  simp only [CollatzResearch.WordTrace]
  refine ⟨96777120330225044949752027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64518080220150029966501351 96777120330225044949752027)
  ·
    refine ⟨145165680495337567424628041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96777120330225044949752027 145165680495337567424628041)
    ·
      refine ⟨108874260371503175568471031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145165680495337567424628041 108874260371503175568471031)
      ·
        refine ⟨163311390557254763352706547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108874260371503175568471031 163311390557254763352706547)
        ·
          refine ⟨244967085835882145029059821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163311390557254763352706547 244967085835882145029059821)
          ·
            refine ⟨91862657188455804385897433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244967085835882145029059821 91862657188455804385897433)
            ·
              refine ⟨68896992891341853289423075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91862657188455804385897433 68896992891341853289423075)
              ·
                refine ⟨103345489337012779934134613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68896992891341853289423075 103345489337012779934134613)
                ·
                  refine ⟨302769988292029628713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103345489337012779934134613 302769988292029628713285)
                  ·
                    rfl

theorem cell22_2653391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_2653391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653391 prefixEnd_2653391 := by exact prefixLift 2653391
  have htrace : WordTrace (prefixWord ++ tailWord_2653391) baseStart_2653391 baseEnd_2653391 := by
    simpa [prefixWord, tailWord_2653391, baseEnd_2653391] using wordTrace_append hprefix tailTrace_2653391
  have hstable : (prefixWord ++ tailWord_2653391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653391).length < 2 ^ (prefixWord ++ tailWord_2653391).sum := by decide
  have hdescent : baseEnd_2653391 < baseStart_2653391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653444 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2653444 : Nat := 118140960795 + 2653444 * 2 ^ 59
def prefixEnd_2653444 : Nat := 4983230072969 + 3 ^ 40 * 2653444 * 2
def baseEnd_2653444 : Nat := 908328107859214414564693

theorem tailTrace_2653444 : CollatzResearch.WordTrace tailWord_2653444 prefixEnd_2653444 908328107859214414564693 := by
  unfold tailWord_2653444
  simp only [CollatzResearch.WordTrace]
  refine ⟨48389526699516517500715693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64519368932688690000954257 48389526699516517500715693)
  ·
    refine ⟨18146072512318694062768385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48389526699516517500715693 18146072512318694062768385)
    ·
      refine ⟨13609554384239020547076289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18146072512318694062768385 13609554384239020547076289)
      ·
        refine ⟨10207165788179265410307217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13609554384239020547076289 10207165788179265410307217)
        ·
          refine ⟨7655374341134449057730413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10207165788179265410307217 7655374341134449057730413)
          ·
            refine ⟨2870765377925418396648905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7655374341134449057730413 2870765377925418396648905)
            ·
              refine ⟨2153074033444063797486679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870765377925418396648905 2153074033444063797486679)
              ·
                refine ⟨3229611050166095696230019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153074033444063797486679 3229611050166095696230019)
                ·
                  refine ⟨4844416575249143544345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229611050166095696230019 4844416575249143544345029)
                  ·
                    refine ⟨908328107859214414564693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844416575249143544345029 908328107859214414564693)
                    ·
                      rfl

theorem cell22_2653444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2653444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653444 prefixEnd_2653444 := by exact prefixLift 2653444
  have htrace : WordTrace (prefixWord ++ tailWord_2653444) baseStart_2653444 baseEnd_2653444 := by
    simpa [prefixWord, tailWord_2653444, baseEnd_2653444] using wordTrace_append hprefix tailTrace_2653444
  have hstable : (prefixWord ++ tailWord_2653444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653444).length < 2 ^ (prefixWord ++ tailWord_2653444).sum := by decide
  have hdescent : baseEnd_2653444 < baseStart_2653444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653474 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2653474 : Nat := 118140960795 + 2653474 * 2 ^ 59
def prefixEnd_2653474 : Nat := 4983230072969 + 3 ^ 40 * 2653474 * 2
def baseEnd_2653474 : Nat := 908338377472304336314601

theorem tailTrace_2653474 : CollatzResearch.WordTrace tailWord_2653474 prefixEnd_2653474 908338377472304336314601 := by
  unfold tailWord_2653474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24195036897231087531255869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64520098392616233416682317 24195036897231087531255869)
  ·
    refine ⟨9073138836461657824220951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24195036897231087531255869 9073138836461657824220951)
    ·
      refine ⟨13609708254692486736331427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073138836461657824220951 13609708254692486736331427)
      ·
        refine ⟨20414562382038730104497141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609708254692486736331427 20414562382038730104497141)
        ·
          refine ⟨1913865223316130947296607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20414562382038730104497141 1913865223316130947296607)
          ·
            refine ⟨2870797834974196420944911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913865223316130947296607 2870797834974196420944911)
            ·
              refine ⟨4306196752461294631417367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870797834974196420944911 4306196752461294631417367)
              ·
                refine ⟨6459295128691941947126051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306196752461294631417367 6459295128691941947126051)
                ·
                  refine ⟨9688942693037912920689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459295128691941947126051 9688942693037912920689077)
                  ·
                    refine ⟨908338377472304336314601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9688942693037912920689077 908338377472304336314601)
                    ·
                      rfl

theorem cell22_2653474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2653474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653474 prefixEnd_2653474 := by exact prefixLift 2653474
  have htrace : WordTrace (prefixWord ++ tailWord_2653474) baseStart_2653474 baseEnd_2653474 := by
    simpa [prefixWord, tailWord_2653474, baseEnd_2653474] using wordTrace_append hprefix tailTrace_2653474
  have hstable : (prefixWord ++ tailWord_2653474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653474).length < 2 ^ (prefixWord ++ tailWord_2653474).sum := by decide
  have hdescent : baseEnd_2653474 < baseStart_2653474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653498 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_2653498 : Nat := 118140960795 + 2653498 * 2 ^ 59
def prefixEnd_2653498 : Nat := 4983230072969 + 3 ^ 40 * 2653498 * 2
def baseEnd_2653498 : Nat := 302782197720925424571509

theorem tailTrace_2653498 : CollatzResearch.WordTrace tailWord_2653498 prefixEnd_2653498 302782197720925424571509 := by
  unfold tailWord_2653498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24195255735209350555974287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64520681960558268149264765 24195255735209350555974287)
  ·
    refine ⟨36292883602814025833961431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24195255735209350555974287 36292883602814025833961431)
    ·
      refine ⟨54439325404221038750942147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36292883602814025833961431 54439325404221038750942147)
      ·
        refine ⟨81658988106331558126413221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54439325404221038750942147 81658988106331558126413221)
        ·
          refine ⟨15311060269937167148702479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81658988106331558126413221 15311060269937167148702479)
          ·
            refine ⟨22966590404905750723053719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15311060269937167148702479 22966590404905750723053719)
            ·
              refine ⟨34449885607358626084580579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22966590404905750723053719 34449885607358626084580579)
              ·
                refine ⟨51674828411037939126870869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34449885607358626084580579 51674828411037939126870869)
                ·
                  refine ⟨302782197720925424571509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51674828411037939126870869 302782197720925424571509)
                  ·
                    rfl

theorem cell22_2653498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_2653498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653498 prefixEnd_2653498 := by exact prefixLift 2653498
  have htrace : WordTrace (prefixWord ++ tailWord_2653498) baseStart_2653498 baseEnd_2653498 := by
    simpa [prefixWord, tailWord_2653498, baseEnd_2653498] using wordTrace_append hprefix tailTrace_2653498
  have hstable : (prefixWord ++ tailWord_2653498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653498).length < 2 ^ (prefixWord ++ tailWord_2653498).sum := by decide
  have hdescent : baseEnd_2653498 < baseStart_2653498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653513 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2653513 : Nat := 118140960795 + 2653513 * 2 ^ 59
def prefixEnd_2653513 : Nat := 4983230072969 + 3 ^ 40 * 2653513 * 2
def baseEnd_2653513 : Nat := 908351727969321234589481

theorem tailTrace_2653513 : CollatzResearch.WordTrace tailWord_2653513 prefixEnd_2653513 908351727969321234589481 := by
  unfold tailWord_2653513
  simp only [CollatzResearch.WordTrace]
  refine ⟨96781570035783059785693193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64521046690522039857128795 96781570035783059785693193)
  ·
    refine ⟨72586177526837294839269895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96781570035783059785693193 72586177526837294839269895)
    ·
      refine ⟨108879266290255942258904843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72586177526837294839269895 108879266290255942258904843)
      ·
        refine ⟨163318899435383913388357265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108879266290255942258904843 163318899435383913388357265)
        ·
          refine ⟨122489174576537935041267949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163318899435383913388357265 122489174576537935041267949)
          ·
            refine ⟨45933440466201725640475481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122489174576537935041267949 45933440466201725640475481)
            ·
              refine ⟨34450080349651294230356611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45933440466201725640475481 34450080349651294230356611)
              ·
                refine ⟨51675120524476941345534917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34450080349651294230356611 51675120524476941345534917)
                ·
                  refine ⟨9689085098339426502287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51675120524476941345534917 9689085098339426502287797)
                  ·
                    refine ⟨908351727969321234589481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9689085098339426502287797 908351727969321234589481)
                    ·
                      rfl

theorem cell22_2653513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2653513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653513 prefixEnd_2653513 := by exact prefixLift 2653513
  have htrace : WordTrace (prefixWord ++ tailWord_2653513) baseStart_2653513 baseEnd_2653513 := by
    simpa [prefixWord, tailWord_2653513, baseEnd_2653513] using wordTrace_append hprefix tailTrace_2653513
  have hstable : (prefixWord ++ tailWord_2653513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653513).length < 2 ^ (prefixWord ++ tailWord_2653513).sum := by decide
  have hdescent : baseEnd_2653513 < baseStart_2653513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653545 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_2653545 : Nat := 118140960795 + 2653545 * 2 ^ 59
def prefixEnd_2653545 : Nat := 4983230072969 + 3 ^ 40 * 2653545 * 2
def baseEnd_2653545 : Nat := 908362682223283817789383

theorem tailTrace_2653545 : CollatzResearch.WordTrace tailWord_2653545 prefixEnd_2653545 908362682223283817789383 := by
  unfold tailWord_2653545
  simp only [CollatzResearch.WordTrace]
  refine ⟨96782737171667129250858089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64521824781111419500572059 96782737171667129250858089)
  ·
    refine ⟨72587052878750346938143567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96782737171667129250858089 72587052878750346938143567)
    ·
      refine ⟨108880579318125520407215351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72587052878750346938143567 108880579318125520407215351)
      ·
        refine ⟨163320868977188280610823027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108880579318125520407215351 163320868977188280610823027)
        ·
          refine ⟨244981303465782420916234541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163320868977188280610823027 244981303465782420916234541)
          ·
            refine ⟨91867988799668407843587953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244981303465782420916234541 91867988799668407843587953)
            ·
              refine ⟨68900991599751305882690965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91867988799668407843587953 68900991599751305882690965)
              ·
                refine ⟨3229733981238342463251139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68900991599751305882690965 3229733981238342463251139)
                ·
                  refine ⟨4844600971857513694876709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229733981238342463251139 4844600971857513694876709)
                  ·
                    refine ⟨908362682223283817789383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844600971857513694876709 908362682223283817789383)
                    ·
                      rfl

theorem cell22_2653545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_2653545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653545 prefixEnd_2653545 := by exact prefixLift 2653545
  have htrace : WordTrace (prefixWord ++ tailWord_2653545) baseStart_2653545 baseEnd_2653545 := by
    simpa [prefixWord, tailWord_2653545, baseEnd_2653545] using wordTrace_append hprefix tailTrace_2653545
  have hstable : (prefixWord ++ tailWord_2653545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653545).length < 2 ^ (prefixWord ++ tailWord_2653545).sum := by decide
  have hdescent : baseEnd_2653545 < baseStart_2653545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653566 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_2653566 : Nat := 118140960795 + 2653566 * 2 ^ 59
def prefixEnd_2653566 : Nat := 4983230072969 + 3 ^ 40 * 2653566 * 2
def baseEnd_2653566 : Nat := 302789956984148921004773

theorem tailTrace_2653566 : CollatzResearch.WordTrace tailWord_2653566 prefixEnd_2653566 302789956984148921004773 := by
  unfold tailWord_2653566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097937888073881229671569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64522335403060699891581701 12097937888073881229671569)
  ·
    refine ⟨9073453416055410922253677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12097937888073881229671569 9073453416055410922253677)
    ·
      refine ⟨3402545031020779095845129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9073453416055410922253677 3402545031020779095845129)
      ·
        refine ⟨2551908773265584321883847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402545031020779095845129 2551908773265584321883847)
        ·
          refine ⟨3827863159898376482825771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551908773265584321883847 3827863159898376482825771)
          ·
            refine ⟨5741794739847564724238657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827863159898376482825771 5741794739847564724238657)
            ·
              refine ⟨4306346054885673543178993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741794739847564724238657 4306346054885673543178993)
              ·
                refine ⟨3229759541164255157384245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306346054885673543178993 3229759541164255157384245)
                ·
                  refine ⟨302789956984148921004773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3229759541164255157384245 302789956984148921004773)
                  ·
                    rfl

theorem cell22_2653566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_2653566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653566 prefixEnd_2653566 := by exact prefixLift 2653566
  have htrace : WordTrace (prefixWord ++ tailWord_2653566) baseStart_2653566 baseEnd_2653566 := by
    simpa [prefixWord, tailWord_2653566, baseEnd_2653566] using wordTrace_append hprefix tailTrace_2653566
  have hstable : (prefixWord ++ tailWord_2653566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653566).length < 2 ^ (prefixWord ++ tailWord_2653566).sum := by decide
  have hdescent : baseEnd_2653566 < baseStart_2653566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653570 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2653570 : Nat := 118140960795 + 2653570 * 2 ^ 59
def prefixEnd_2653570 : Nat := 4983230072969 + 3 ^ 40 * 2653570 * 2
def baseEnd_2653570 : Nat := 908371240234192085914307

theorem tailTrace_2653570 : CollatzResearch.WordTrace tailWord_2653570 prefixEnd_2653570 908371240234192085914307 := by
  unfold tailWord_2653570
  simp only [CollatzResearch.WordTrace]
  refine ⟨24195912249144139630129541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64522432664384372347012109 24195912249144139630129541)
  ·
    refine ⟨4536733546714526180649289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24195912249144139630129541 4536733546714526180649289)
    ·
      refine ⟨3402550160035894635486967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536733546714526180649289 3402550160035894635486967)
      ·
        refine ⟨5103825240053841953230451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402550160035894635486967 5103825240053841953230451)
        ·
          refine ⟨7655737860080762929845677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103825240053841953230451 7655737860080762929845677)
          ·
            refine ⟨2870901697530286098692129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7655737860080762929845677 2870901697530286098692129)
            ·
              refine ⟨2153176273147714574019097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870901697530286098692129 2153176273147714574019097)
              ·
                refine ⟨1614882204860785930514323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153176273147714574019097 1614882204860785930514323)
                ·
                  refine ⟨2422323307291178895771485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614882204860785930514323 2422323307291178895771485)
                  ·
                    refine ⟨908371240234192085914307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422323307291178895771485 908371240234192085914307)
                    ·
                      rfl

theorem cell22_2653570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2653570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653570 prefixEnd_2653570 := by exact prefixLift 2653570
  have htrace : WordTrace (prefixWord ++ tailWord_2653570) baseStart_2653570 baseEnd_2653570 := by
    simpa [prefixWord, tailWord_2653570, baseEnd_2653570] using wordTrace_append hprefix tailTrace_2653570
  have hstable : (prefixWord ++ tailWord_2653570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653570).length < 2 ^ (prefixWord ++ tailWord_2653570).sum := by decide
  have hdescent : baseEnd_2653570 < baseStart_2653570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653671 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2653671 : Nat := 118140960795 + 2653671 * 2 ^ 59
def prefixEnd_2653671 : Nat := 4983230072969 + 3 ^ 40 * 2653671 * 2
def baseEnd_2653671 : Nat := 908405814598261489138997

theorem tailTrace_2653671 : CollatzResearch.WordTrace tailWord_2653671 prefixEnd_2653671 908405814598261489138997 := by
  unfold tailWord_2653671
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787332769210652769944867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64524888512807101846629911 96787332769210652769944867)
  ·
    refine ⟨145180999153815979154917301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96787332769210652769944867 145180999153815979154917301)
    ·
      refine ⟨13610718670670248045773497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145180999153815979154917301 13610718670670248045773497)
      ·
        refine ⟨10208039003002686034330123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13610718670670248045773497 10208039003002686034330123)
        ·
          refine ⟨15312058504504029051495185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208039003002686034330123 15312058504504029051495185)
          ·
            refine ⟨11484043878378021788621389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15312058504504029051495185 11484043878378021788621389)
            ·
              refine ⟨4306516454391758170733021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11484043878378021788621389 4306516454391758170733021)
              ·
                refine ⟨1614943670396909314024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4306516454391758170733021 1614943670396909314024883)
                ·
                  refine ⟨2422415505595363971037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614943670396909314024883 2422415505595363971037325)
                  ·
                    refine ⟨908405814598261489138997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422415505595363971037325 908405814598261489138997)
                    ·
                      rfl

theorem cell22_2653671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2653671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653671 prefixEnd_2653671 := by exact prefixLift 2653671
  have htrace : WordTrace (prefixWord ++ tailWord_2653671) baseStart_2653671 baseEnd_2653671 := by
    simpa [prefixWord, tailWord_2653671, baseEnd_2653671] using wordTrace_append hprefix tailTrace_2653671
  have hstable : (prefixWord ++ tailWord_2653671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653671).length < 2 ^ (prefixWord ++ tailWord_2653671).sum := by decide
  have hdescent : baseEnd_2653671 < baseStart_2653671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653695 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 6]
def baseStart_2653695 : Nat := 118140960795 + 2653695 * 2 ^ 59
def prefixEnd_2653695 : Nat := 4983230072969 + 3 ^ 40 * 2653695 * 2
def baseEnd_2653695 : Nat := 302804676762911142179641

theorem tailTrace_2653695 : CollatzResearch.WordTrace tailWord_2653695 prefixEnd_2653695 302804676762911142179641 := by
  unfold tailWord_2653695
  simp only [CollatzResearch.WordTrace]
  refine ⟨96788208121123704868818539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64525472080749136579212359 96788208121123704868818539)
  ·
    refine ⟨145182312181685557303227809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96788208121123704868818539 145182312181685557303227809)
    ·
      refine ⟨108886734136264167977420857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145182312181685557303227809 108886734136264167977420857)
      ·
        refine ⟨81665050602198125983065643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108886734136264167977420857 81665050602198125983065643)
        ·
          refine ⟨122497575903297188974598465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81665050602198125983065643 122497575903297188974598465)
          ·
            refine ⟨91873181927472891730948849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122497575903297188974598465 91873181927472891730948849)
            ·
              refine ⟨68904886445604668798211637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91873181927472891730948849 68904886445604668798211637)
              ·
                refine ⟨6459833104275437699832341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68904886445604668798211637 6459833104275437699832341)
                ·
                  refine ⟨302804676762911142179641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6459833104275437699832341 302804676762911142179641)
                  ·
                    rfl

theorem cell22_2653695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_2653695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653695 prefixEnd_2653695 := by exact prefixLift 2653695
  have htrace : WordTrace (prefixWord ++ tailWord_2653695) baseStart_2653695 baseEnd_2653695 := by
    simpa [prefixWord, tailWord_2653695, baseEnd_2653695] using wordTrace_append hprefix tailTrace_2653695
  have hstable : (prefixWord ++ tailWord_2653695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653695).length < 2 ^ (prefixWord ++ tailWord_2653695).sum := by decide
  have hdescent : baseEnd_2653695 < baseStart_2653695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653727 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 6, 3]
def baseStart_2653727 : Nat := 118140960795 + 2653727 * 2 ^ 59
def prefixEnd_2653727 : Nat := 4983230072969 + 3 ^ 40 * 2653727 * 2
def baseEnd_2653727 : Nat := 908424984542696009738825

theorem tailTrace_2653727 : CollatzResearch.WordTrace tailWord_2653727 prefixEnd_2653727 908424984542696009738825 := by
  unfold tailWord_2653727
  simp only [CollatzResearch.WordTrace]
  refine ⟨96789375257007774333983435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64526250171338516222655623 96789375257007774333983435)
  ·
    refine ⟨145184062885511661500975153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96789375257007774333983435 145184062885511661500975153)
    ·
      refine ⟨108888047164133746125731365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145184062885511661500975153 108888047164133746125731365)
      ·
        refine ⟨20416508843275077398574631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108888047164133746125731365 20416508843275077398574631)
        ·
          refine ⟨30624763264912616097861947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416508843275077398574631 30624763264912616097861947)
          ·
            refine ⟨45937144897368924146792921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30624763264912616097861947 45937144897368924146792921)
            ·
              refine ⟨34452858673026693110094691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45937144897368924146792921 34452858673026693110094691)
              ·
                refine ⟨51679288009540039665142037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34452858673026693110094691 51679288009540039665142037)
                ·
                  refine ⟨2422466625447189359303533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51679288009540039665142037 2422466625447189359303533)
                  ·
                    refine ⟨908424984542696009738825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422466625447189359303533 908424984542696009738825)
                    ·
                      rfl

theorem cell22_2653727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_2653727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653727 prefixEnd_2653727 := by exact prefixLift 2653727
  have htrace : WordTrace (prefixWord ++ tailWord_2653727) baseStart_2653727 baseEnd_2653727 := by
    simpa [prefixWord, tailWord_2653727, baseEnd_2653727] using wordTrace_append hprefix tailTrace_2653727
  have hstable : (prefixWord ++ tailWord_2653727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653727).length < 2 ^ (prefixWord ++ tailWord_2653727).sum := by decide
  have hdescent : baseEnd_2653727 < baseStart_2653727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653731 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 1, 4]
def baseStart_2653731 : Nat := 118140960795 + 2653731 * 2 ^ 59
def prefixEnd_2653731 : Nat := 4983230072969 + 3 ^ 40 * 2653731 * 2
def baseEnd_2653731 : Nat := 908426353824441332638813

theorem tailTrace_2653731 : CollatzResearch.WordTrace tailWord_2653731 prefixEnd_2653731 908426353824441332638813 := by
  unfold tailWord_2653731
  simp only [CollatzResearch.WordTrace]
  refine ⟨96789521148993283017129047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64526347432662188678086031 96789521148993283017129047)
  ·
    refine ⟨145184281723489924525693571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96789521148993283017129047 145184281723489924525693571)
    ·
      refine ⟨217776422585234886788540357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145184281723489924525693571 217776422585234886788540357)
      ·
        refine ⟨40833079234731541272851317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217776422585234886788540357 40833079234731541272851317)
        ·
          refine ⟨3828101178256081994329811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40833079234731541272851317 3828101178256081994329811)
          ·
            refine ⟨5742151767384122991494717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828101178256081994329811 5742151767384122991494717)
            ·
              refine ⟨2153306912769046121810519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5742151767384122991494717 2153306912769046121810519)
              ·
                refine ⟨3229960369153569182715779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153306912769046121810519 3229960369153569182715779)
                ·
                  refine ⟨4844940553730353774073669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229960369153569182715779 4844940553730353774073669)
                  ·
                    refine ⟨908426353824441332638813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844940553730353774073669 908426353824441332638813)
                    ·
                      rfl

theorem cell22_2653731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 4].length) (baseStart_2653731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653731 prefixEnd_2653731 := by exact prefixLift 2653731
  have htrace : WordTrace (prefixWord ++ tailWord_2653731) baseStart_2653731 baseEnd_2653731 := by
    simpa [prefixWord, tailWord_2653731, baseEnd_2653731] using wordTrace_append hprefix tailTrace_2653731
  have hstable : (prefixWord ++ tailWord_2653731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653731).length < 2 ^ (prefixWord ++ tailWord_2653731).sum := by decide
  have hdescent : baseEnd_2653731 < baseStart_2653731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653782 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2653782 : Nat := 118140960795 + 2653782 * 2 ^ 59
def prefixEnd_2653782 : Nat := 4983230072969 + 3 ^ 40 * 2653782 * 2
def baseEnd_2653782 : Nat := 908443812166694199613657

theorem tailTrace_2653782 : CollatzResearch.WordTrace tailWord_2653782 prefixEnd_2653782 908443812166694199613657 := by
  unfold tailWord_2653782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049461329488032420452225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64527587514539012484823733 6049461329488032420452225)
  ·
    refine ⟨4537095997116024315339169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6049461329488032420452225 4537095997116024315339169)
    ·
      refine ⟨3402821997837018236504377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4537095997116024315339169 3402821997837018236504377)
      ·
        refine ⟨2552116498377763677378283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402821997837018236504377 2552116498377763677378283)
        ·
          refine ⟨3828174747566645516067425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552116498377763677378283 3828174747566645516067425)
          ·
            refine ⟨2871131060674984137050569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828174747566645516067425 2871131060674984137050569)
            ·
              refine ⟨2153348295506238102787927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871131060674984137050569 2153348295506238102787927)
              ·
                refine ⟨3230022443259357154181891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153348295506238102787927 3230022443259357154181891)
                ·
                  refine ⟨4845033664889035731272837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230022443259357154181891 4845033664889035731272837)
                  ·
                    refine ⟨908443812166694199613657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845033664889035731272837 908443812166694199613657)
                    ·
                      rfl

theorem cell22_2653782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2653782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653782 prefixEnd_2653782 := by exact prefixLift 2653782
  have htrace : WordTrace (prefixWord ++ tailWord_2653782) baseStart_2653782 baseEnd_2653782 := by
    simpa [prefixWord, tailWord_2653782, baseEnd_2653782] using wordTrace_append hprefix tailTrace_2653782
  have hstable : (prefixWord ++ tailWord_2653782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653782).length < 2 ^ (prefixWord ++ tailWord_2653782).sum := by decide
  have hdescent : baseEnd_2653782 < baseStart_2653782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653817 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_2653817 : Nat := 118140960795 + 2653817 * 2 ^ 59
def prefixEnd_2653817 : Nat := 4983230072969 + 3 ^ 40 * 2653817 * 2
def baseEnd_2653817 : Nat := 908455793381965774988549

theorem tailTrace_2653817 : CollatzResearch.WordTrace tailWord_2653817 prefixEnd_2653817 908455793381965774988549 := by
  unfold tailWord_2653817
  simp only [CollatzResearch.WordTrace]
  refine ⟨96792657826681719704759705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64528438551121146469839803 96792657826681719704759705)
  ·
    refine ⟨72594493370011289778569779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96792657826681719704759705 72594493370011289778569779)
    ·
      refine ⟨108891740055016934667854669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72594493370011289778569779 108891740055016934667854669)
      ·
        refine ⟨40834402520631350500445501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108891740055016934667854669 40834402520631350500445501)
        ·
          refine ⟨15312900945236756437667063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40834402520631350500445501 15312900945236756437667063)
          ·
            refine ⟨22969351417855134656500595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15312900945236756437667063 22969351417855134656500595)
            ·
              refine ⟨34454027126782701984750893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22969351417855134656500595 34454027126782701984750893)
              ·
                refine ⟨12920260172543513244281585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34454027126782701984750893 12920260172543513244281585)
                ·
                  refine ⟨9690195129407634933211189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12920260172543513244281585 9690195129407634933211189)
                  ·
                    refine ⟨908455793381965774988549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9690195129407634933211189 908455793381965774988549)
                    ·
                      rfl

theorem cell22_2653817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_2653817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653817 prefixEnd_2653817 := by exact prefixLift 2653817
  have htrace : WordTrace (prefixWord ++ tailWord_2653817) baseStart_2653817 baseEnd_2653817 := by
    simpa [prefixWord, tailWord_2653817, baseEnd_2653817] using wordTrace_append hprefix tailTrace_2653817
  have hstable : (prefixWord ++ tailWord_2653817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653817).length < 2 ^ (prefixWord ++ tailWord_2653817).sum := by decide
  have hdescent : baseEnd_2653817 < baseStart_2653817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653819 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 5]
def baseStart_2653819 : Nat := 118140960795 + 2653819 * 2 ^ 59
def prefixEnd_2653819 : Nat := 4983230072969 + 3 ^ 40 * 2653819 * 2
def baseEnd_2653819 : Nat := 302818826007612812146181

theorem tailTrace_2653819 : CollatzResearch.WordTrace tailWord_2653819 prefixEnd_2653819 302818826007612812146181 := by
  unfold tailWord_2653819
  simp only [CollatzResearch.WordTrace]
  refine ⟨96792730772674474046332511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64528487181782982697555007 96792730772674474046332511)
  ·
    refine ⟨145189096159011711069498767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96792730772674474046332511 145189096159011711069498767)
    ·
      refine ⟨217783644238517566604248151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145189096159011711069498767 217783644238517566604248151)
      ·
        refine ⟨326675466357776349906372227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217783644238517566604248151 326675466357776349906372227)
        ·
          refine ⟨490013199536664524859558341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326675466357776349906372227 490013199536664524859558341)
          ·
            refine ⟨91877474913124598411167189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490013199536664524859558341 91877474913124598411167189)
            ·
              refine ⟨2153378318276357775261731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91877474913124598411167189 2153378318276357775261731)
              ·
                refine ⟨3230067477414536662892597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153378318276357775261731 3230067477414536662892597)
                ·
                  refine ⟨302818826007612812146181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3230067477414536662892597 302818826007612812146181)
                  ·
                    rfl

theorem cell22_2653819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 5].length) (baseStart_2653819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653819 prefixEnd_2653819 := by exact prefixLift 2653819
  have htrace : WordTrace (prefixWord ++ tailWord_2653819) baseStart_2653819 baseEnd_2653819 := by
    simpa [prefixWord, tailWord_2653819, baseEnd_2653819] using wordTrace_append hprefix tailTrace_2653819
  have hstable : (prefixWord ++ tailWord_2653819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653819).length < 2 ^ (prefixWord ++ tailWord_2653819).sum := by decide
  have hdescent : baseEnd_2653819 < baseStart_2653819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653870 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_2653870 : Nat := 118140960795 + 2653870 * 2 ^ 59
def prefixEnd_2653870 : Nat := 4983230072969 + 3 ^ 40 * 2653870 * 2
def baseEnd_2653870 : Nat := 302824645455030434471129

theorem tailTrace_2653870 : CollatzResearch.WordTrace tailWord_2653870 prefixEnd_2653870 302824645455030434471129 := by
  unfold tailWord_2653870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099323861936213719554883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64529727263659806504292709 12099323861936213719554883)
  ·
    refine ⟨18148985792904320579332325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12099323861936213719554883 18148985792904320579332325)
    ·
      refine ⟨3402934836169560108624811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18148985792904320579332325 3402934836169560108624811)
      ·
        refine ⟨5104402254254340162937217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402934836169560108624811 5104402254254340162937217)
        ·
          refine ⟨3828301690690755122202913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104402254254340162937217 3828301690690755122202913)
          ·
            refine ⟨2871226268018066341652185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828301690690755122202913 2871226268018066341652185)
            ·
              refine ⟨2153419701013549756239139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871226268018066341652185 2153419701013549756239139)
              ·
                refine ⟨3230129551520324634358709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153419701013549756239139 3230129551520324634358709)
                ·
                  refine ⟨302824645455030434471129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3230129551520324634358709 302824645455030434471129)
                  ·
                    rfl

theorem cell22_2653870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_2653870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653870 prefixEnd_2653870 := by exact prefixLift 2653870
  have htrace : WordTrace (prefixWord ++ tailWord_2653870) baseStart_2653870 baseEnd_2653870 := by
    simpa [prefixWord, tailWord_2653870, baseEnd_2653870] using wordTrace_append hprefix tailTrace_2653870
  have hstable : (prefixWord ++ tailWord_2653870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653870).length < 2 ^ (prefixWord ++ tailWord_2653870).sum := by decide
  have hdescent : baseEnd_2653870 < baseStart_2653870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2653988 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2653988 : Nat := 118140960795 + 2653988 * 2 ^ 59
def prefixEnd_2653988 : Nat := 4983230072969 + 3 ^ 40 * 2653988 * 2
def baseEnd_2653988 : Nat := 302838110058859442987675

theorem tailTrace_2653988 : CollatzResearch.WordTrace tailWord_2653988 prefixEnd_2653988 302838110058859442987675 := by
  unfold tailWord_2653988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48399447354531107954617309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64532596472708143939489745 48399447354531107954617309)
  ·
    refine ⟨18149792757949165482981491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48399447354531107954617309 18149792757949165482981491)
    ·
      refine ⟨27224689136923748224472237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149792757949165482981491 27224689136923748224472237)
      ·
        refine ⟨10209258426346405584177089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27224689136923748224472237 10209258426346405584177089)
        ·
          refine ⟨7656943819759804188132817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10209258426346405584177089 7656943819759804188132817)
          ·
            refine ⟨5742707864819853141099613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7656943819759804188132817 5742707864819853141099613)
            ·
              refine ⟨2153515449307444927912355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5742707864819853141099613 2153515449307444927912355)
              ·
                refine ⟨3230273173961167391868533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153515449307444927912355 3230273173961167391868533)
                ·
                  refine ⟨302838110058859442987675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3230273173961167391868533 302838110058859442987675)
                  ·
                    rfl

theorem cell22_2653988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2653988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2653988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2653988 prefixEnd_2653988 := by exact prefixLift 2653988
  have htrace : WordTrace (prefixWord ++ tailWord_2653988) baseStart_2653988 baseEnd_2653988 := by
    simpa [prefixWord, tailWord_2653988, baseEnd_2653988] using wordTrace_append hprefix tailTrace_2653988
  have hstable : (prefixWord ++ tailWord_2653988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2653988).length < 2 ^ (prefixWord ++ tailWord_2653988).sum := by decide
  have hdescent : baseEnd_2653988 < baseStart_2653988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2653988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654001 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2654001 : Nat := 118140960795 + 2654001 * 2 ^ 59
def prefixEnd_2654001 : Nat := 4983230072969 + 3 ^ 40 * 2654001 * 2
def baseEnd_2654001 : Nat := 908518780342250628387985

theorem tailTrace_2654001 : CollatzResearch.WordTrace tailWord_2654001 prefixEnd_2654001 908518780342250628387985 := by
  unfold tailWord_2654001
  simp only [CollatzResearch.WordTrace]
  refine ⟨96799368858015119129457857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64532912572010079419638571 96799368858015119129457857)
  ·
    refine ⟨72599526643511339347093393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96799368858015119129457857 72599526643511339347093393)
    ·
      refine ⟨54449644982633504510320045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72599526643511339347093393 54449644982633504510320045)
      ·
        refine ⟨20418616868487564191370017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54449644982633504510320045 20418616868487564191370017)
        ·
          refine ⟨15313962651365673143527513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20418616868487564191370017 15313962651365673143527513)
          ·
            refine ⟨11485471988524254857645635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15313962651365673143527513 11485471988524254857645635)
            ·
              refine ⟨17228207982786382286468453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11485471988524254857645635 17228207982786382286468453)
              ·
                refine ⟨3230288996772446678712835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17228207982786382286468453 3230288996772446678712835)
                ·
                  refine ⟨4845433495158670018069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230288996772446678712835 4845433495158670018069253)
                  ·
                    refine ⟨908518780342250628387985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845433495158670018069253 908518780342250628387985)
                    ·
                      rfl

theorem cell22_2654001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2654001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654001 prefixEnd_2654001 := by exact prefixLift 2654001
  have htrace : WordTrace (prefixWord ++ tailWord_2654001) baseStart_2654001 baseEnd_2654001 := by
    simpa [prefixWord, tailWord_2654001, baseEnd_2654001] using wordTrace_append hprefix tailTrace_2654001
  have hstable : (prefixWord ++ tailWord_2654001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654001).length < 2 ^ (prefixWord ++ tailWord_2654001).sum := by decide
  have hdescent : baseEnd_2654001 < baseStart_2654001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654009 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_2654009 : Nat := 118140960795 + 2654009 * 2 ^ 59
def prefixEnd_2654009 : Nat := 4983230072969 + 3 ^ 40 * 2654009 * 2
def baseEnd_2654009 : Nat := 908521518905741274187961

theorem tailTrace_2654009 : CollatzResearch.WordTrace tailWord_2654009 prefixEnd_2654009 908521518905741274187961 := by
  unfold tailWord_2654009
  simp only [CollatzResearch.WordTrace]
  refine ⟨96799660641986136495749081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64533107094657424330499387 96799660641986136495749081)
  ·
    refine ⟨72599745481489602371811811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96799660641986136495749081 72599745481489602371811811)
    ·
      refine ⟨108899618222234403557717717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72599745481489602371811811 108899618222234403557717717)
      ·
        refine ⟨2552334802083618833384009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108899618222234403557717717 2552334802083618833384009)
        ·
          refine ⟨1914251101562714125038007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2552334802083618833384009 1914251101562714125038007)
          ·
            refine ⟨2871376652344071187557011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914251101562714125038007 2871376652344071187557011)
            ·
              refine ⟨4307064978516106781335517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871376652344071187557011 4307064978516106781335517)
              ·
                refine ⟨1615149366943540043000819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4307064978516106781335517 1615149366943540043000819)
                ·
                  refine ⟨2422724050415310064501229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615149366943540043000819 2422724050415310064501229)
                  ·
                    refine ⟨908521518905741274187961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422724050415310064501229 908521518905741274187961)
                    ·
                      rfl

theorem cell22_2654009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_2654009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654009 prefixEnd_2654009 := by exact prefixLift 2654009
  have htrace : WordTrace (prefixWord ++ tailWord_2654009) baseStart_2654009 baseEnd_2654009 := by
    simpa [prefixWord, tailWord_2654009, baseEnd_2654009] using wordTrace_append hprefix tailTrace_2654009
  have hstable : (prefixWord ++ tailWord_2654009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654009).length < 2 ^ (prefixWord ++ tailWord_2654009).sum := by decide
  have hdescent : baseEnd_2654009 < baseStart_2654009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654048 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_2654048 : Nat := 118140960795 + 2654048 * 2 ^ 59
def prefixEnd_2654048 : Nat := 4983230072969 + 3 ^ 40 * 2654048 * 2
def baseEnd_2654048 : Nat := 908534869402758172462841

theorem tailTrace_2654048 : CollatzResearch.WordTrace tailWord_2654048 prefixEnd_2654048 908534869402758172462841 := by
  unfold tailWord_2654048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48400541544422423078209399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64534055392563230770945865 48400541544422423078209399)
  ·
    refine ⟨72600812316633634617314099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48400541544422423078209399 72600812316633634617314099)
    ·
      refine ⟨108901218474950451925971149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72600812316633634617314099 108901218474950451925971149)
      ·
        refine ⟨40837956928106419472239181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108901218474950451925971149 40837956928106419472239181)
        ·
          refine ⟨15314233848039907302089693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40837956928106419472239181 15314233848039907302089693)
          ·
            refine ⟨5742837693014965238283635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15314233848039907302089693 5742837693014965238283635)
            ·
              refine ⟨8614256539522447857425453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742837693014965238283635 8614256539522447857425453)
              ·
                refine ⟨3230346202320917946534545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8614256539522447857425453 3230346202320917946534545)
                ·
                  refine ⟨2422759651740688459900909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230346202320917946534545 2422759651740688459900909)
                  ·
                    refine ⟨908534869402758172462841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422759651740688459900909 908534869402758172462841)
                    ·
                      rfl

theorem cell22_2654048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_2654048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654048 prefixEnd_2654048 := by exact prefixLift 2654048
  have htrace : WordTrace (prefixWord ++ tailWord_2654048) baseStart_2654048 baseEnd_2654048 := by
    simpa [prefixWord, tailWord_2654048, baseEnd_2654048] using wordTrace_append hprefix tailTrace_2654048
  have hstable : (prefixWord ++ tailWord_2654048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654048).length < 2 ^ (prefixWord ++ tailWord_2654048).sum := by decide
  have hdescent : baseEnd_2654048 < baseStart_2654048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654170 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_2654170 : Nat := 118140960795 + 2654170 * 2 ^ 59
def prefixEnd_2654170 : Nat := 4983230072969 + 3 ^ 40 * 2654170 * 2
def baseEnd_2654170 : Nat := 908576632495990520912467

theorem tailTrace_2654170 : CollatzResearch.WordTrace tailWord_2654170 prefixEnd_2654170 908576632495990520912467 := by
  unfold tailWord_2654170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24201383198600715248089991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64537021862935240661573309 24201383198600715248089991)
  ·
    refine ⟨36302074797901072872134987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24201383198600715248089991 36302074797901072872134987)
    ·
      refine ⟨54453112196851609308202481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36302074797901072872134987 54453112196851609308202481)
      ·
        refine ⟨40839834147638706981151861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54453112196851609308202481 40839834147638706981151861)
        ·
          refine ⟨3828734451341128779482987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40839834147638706981151861 3828734451341128779482987)
          ·
            refine ⟨5743101677011693169224481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828734451341128779482987 5743101677011693169224481)
            ·
              refine ⟨4307326257758769876918361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5743101677011693169224481 4307326257758769876918361)
              ·
                refine ⟨3230494693319077407688771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307326257758769876918361 3230494693319077407688771)
                ·
                  refine ⟨4845742039978616111533157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230494693319077407688771 4845742039978616111533157)
                  ·
                    refine ⟨908576632495990520912467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845742039978616111533157 908576632495990520912467)
                    ·
                      rfl

theorem cell22_2654170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_2654170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654170 prefixEnd_2654170 := by exact prefixLift 2654170
  have htrace : WordTrace (prefixWord ++ tailWord_2654170) baseStart_2654170 baseEnd_2654170 := by
    simpa [prefixWord, tailWord_2654170, baseEnd_2654170] using wordTrace_append hprefix tailTrace_2654170
  have hstable : (prefixWord ++ tailWord_2654170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654170).length < 2 ^ (prefixWord ++ tailWord_2654170).sum := by decide
  have hdescent : baseEnd_2654170 < baseStart_2654170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654221 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2654221 : Nat := 118140960795 + 2654221 * 2 ^ 59
def prefixEnd_2654221 : Nat := 4983230072969 + 3 ^ 40 * 2654221 * 2
def baseEnd_2654221 : Nat := 908594090838243387887311

theorem tailTrace_2654221 : CollatzResearch.WordTrace tailWord_2654221 prefixEnd_2654221 908594090838243387887311 := by
  unfold tailWord_2654221
  simp only [CollatzResearch.WordTrace]
  refine ⟨96807392917218096702466517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64538261944812064468311011 96807392917218096702466517)
  ·
    refine ⟨2268923271497299141464059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 96807392917218096702466517 2268923271497299141464059)
    ·
      refine ⟨3403384907245948712196089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268923271497299141464059 3403384907245948712196089)
      ·
        refine ⟨2552538680434461534147067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403384907245948712196089 2552538680434461534147067)
        ·
          refine ⟨3828808020651692301220601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552538680434461534147067 3828808020651692301220601)
          ·
            refine ⟨2871606015488769225915451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828808020651692301220601 2871606015488769225915451)
            ·
              refine ⟨4307409023233153838873177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871606015488769225915451 4307409023233153838873177)
              ·
                refine ⟨3230556767424865379154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307409023233153838873177 3230556767424865379154883)
                ·
                  refine ⟨4845835151137298068732325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230556767424865379154883 4845835151137298068732325)
                  ·
                    refine ⟨908594090838243387887311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845835151137298068732325 908594090838243387887311)
                    ·
                      rfl

theorem cell22_2654221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2654221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654221 prefixEnd_2654221 := by exact prefixLift 2654221
  have htrace : WordTrace (prefixWord ++ tailWord_2654221) baseStart_2654221 baseEnd_2654221 := by
    simpa [prefixWord, tailWord_2654221, baseEnd_2654221] using wordTrace_append hprefix tailTrace_2654221
  have hstable : (prefixWord ++ tailWord_2654221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654221).length < 2 ^ (prefixWord ++ tailWord_2654221).sum := by decide
  have hdescent : baseEnd_2654221 < baseStart_2654221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654258 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_2654258 : Nat := 118140960795 + 2654258 * 2 ^ 59
def prefixEnd_2654258 : Nat := 4983230072969 + 3 ^ 40 * 2654258 * 2
def baseEnd_2654258 : Nat := 302868918898129208237399

theorem tailTrace_2654258 : CollatzResearch.WordTrace tailWord_2654258 prefixEnd_2654258 302868918898129208237399 := by
  unfold tailWord_2654258
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202185604521013005390857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64539161612056034681042285 24202185604521013005390857)
  ·
    refine ⟨18151639203390759754043143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24202185604521013005390857 18151639203390759754043143)
    ·
      refine ⟨27227458805086139631064715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18151639203390759754043143 27227458805086139631064715)
      ·
        refine ⟨40841188207629209446597073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27227458805086139631064715 40841188207629209446597073)
        ·
          refine ⟨30630891155721907084947805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40841188207629209446597073 30630891155721907084947805)
          ·
            refine ⟨11486584183395715156855427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30630891155721907084947805 11486584183395715156855427)
            ·
              refine ⟨17229876275093572735283141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486584183395715156855427 17229876275093572735283141)
              ·
                refine ⟨3230601801580044887865589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17229876275093572735283141 3230601801580044887865589)
                ·
                  refine ⟨302868918898129208237399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3230601801580044887865589 302868918898129208237399)
                  ·
                    rfl

theorem cell22_2654258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_2654258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654258 prefixEnd_2654258 := by exact prefixLift 2654258
  have htrace : WordTrace (prefixWord ++ tailWord_2654258) baseStart_2654258 baseEnd_2654258 := by
    simpa [prefixWord, tailWord_2654258, baseEnd_2654258] using wordTrace_append hprefix tailTrace_2654258
  have hstable : (prefixWord ++ tailWord_2654258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654258).length < 2 ^ (prefixWord ++ tailWord_2654258).sum := by decide
  have hdescent : baseEnd_2654258 < baseStart_2654258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654273 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2654273 : Nat := 118140960795 + 2654273 * 2 ^ 59
def prefixEnd_2654273 : Nat := 4983230072969 + 3 ^ 40 * 2654273 * 2
def baseEnd_2654273 : Nat := 908611891500932585587151

theorem tailTrace_2654273 : CollatzResearch.WordTrace tailWord_2654273 prefixEnd_2654273 908611891500932585587151 := by
  unfold tailWord_2654273
  simp only [CollatzResearch.WordTrace]
  refine ⟨96809289513029709583359473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64539526342019806388906315 96809289513029709583359473)
  ·
    refine ⟨72606967134772282187519605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96809289513029709583359473 72606967134772282187519605)
    ·
      refine ⟨6806903168884901455079963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72606967134772282187519605 6806903168884901455079963)
      ·
        refine ⟨10210354753327352182619945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806903168884901455079963 10210354753327352182619945)
        ·
          refine ⟨7657766064995514136964959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10210354753327352182619945 7657766064995514136964959)
          ·
            refine ⟨11486649097493271205447439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657766064995514136964959 11486649097493271205447439)
            ·
              refine ⟨17229973646239906808171159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486649097493271205447439 17229973646239906808171159)
              ·
                refine ⟨25844960469359860212256739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17229973646239906808171159 25844960469359860212256739)
                ·
                  refine ⟨38767440704039790318385109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25844960469359860212256739 38767440704039790318385109)
                  ·
                    refine ⟨908611891500932585587151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38767440704039790318385109 908611891500932585587151)
                    ·
                      rfl

theorem cell22_2654273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2654273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654273 prefixEnd_2654273 := by exact prefixLift 2654273
  have htrace : WordTrace (prefixWord ++ tailWord_2654273) baseStart_2654273 baseEnd_2654273 := by
    simpa [prefixWord, tailWord_2654273, baseEnd_2654273] using wordTrace_append hprefix tailTrace_2654273
  have hstable : (prefixWord ++ tailWord_2654273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654273).length < 2 ^ (prefixWord ++ tailWord_2654273).sum := by decide
  have hdescent : baseEnd_2654273 < baseStart_2654273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654320 : List Nat := [2, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_2654320 : Nat := 118140960795 + 2654320 * 2 ^ 59
def prefixEnd_2654320 : Nat := 4983230072969 + 3 ^ 40 * 2654320 * 2
def baseEnd_2654320 : Nat := 302875993520480043220669

theorem tailTrace_2654320 : CollatzResearch.WordTrace tailWord_2654320 prefixEnd_2654320 302875993520480043220669 := by
  unfold tailWord_2654320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405501871929718305160207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64540669162572957740213609 48405501871929718305160207)
  ·
    refine ⟨72608252807894577457740311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48405501871929718305160207 72608252807894577457740311)
    ·
      refine ⟨108912379211841866186610467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72608252807894577457740311 108912379211841866186610467)
      ·
        refine ⟨163368568817762799279915701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108912379211841866186610467 163368568817762799279915701)
        ·
          refine ⟨15315803326665262432492097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163368568817762799279915701 15315803326665262432492097)
          ·
            refine ⟨11486852494998946824369073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15315803326665262432492097 11486852494998946824369073)
            ·
              refine ⟨8615139371249210118276805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11486852494998946824369073 8615139371249210118276805)
              ·
                refine ⟨1615338632109226897176901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8615139371249210118276805 1615338632109226897176901)
                ·
                  refine ⟨302875993520480043220669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615338632109226897176901 302875993520480043220669)
                  ·
                    rfl

theorem cell22_2654320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_2654320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654320 prefixEnd_2654320 := by exact prefixLift 2654320
  have htrace : WordTrace (prefixWord ++ tailWord_2654320) baseStart_2654320 baseEnd_2654320 := by
    simpa [prefixWord, tailWord_2654320, baseEnd_2654320] using wordTrace_append hprefix tailTrace_2654320
  have hstable : (prefixWord ++ tailWord_2654320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654320).length < 2 ^ (prefixWord ++ tailWord_2654320).sum := by decide
  have hdescent : baseEnd_2654320 < baseStart_2654320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654333 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2654333 : Nat := 118140960795 + 2654333 * 2 ^ 59
def prefixEnd_2654333 : Nat := 4983230072969 + 3 ^ 40 * 2654333 * 2
def baseEnd_2654333 : Nat := 908632430727112429086967

theorem tailTrace_2654333 : CollatzResearch.WordTrace tailWord_2654333 prefixEnd_2654333 908632430727112429086967 := by
  unfold tailWord_2654333
  simp only [CollatzResearch.WordTrace]
  refine ⟨96811477892812339830543653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64540985261874893220362435 96811477892812339830543653)
  ·
    refine ⟨18152152104902313718226935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96811477892812339830543653 18152152104902313718226935)
    ·
      refine ⟨27228228157353470577340403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18152152104902313718226935 27228228157353470577340403)
      ·
        refine ⟨40842342236030205866010605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27228228157353470577340403 40842342236030205866010605)
        ·
          refine ⟨15315878338511327199753977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40842342236030205866010605 15315878338511327199753977)
          ·
            refine ⟨11486908753883495399815483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15315878338511327199753977 11486908753883495399815483)
            ·
              refine ⟨17230363130825243099723225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486908753883495399815483 17230363130825243099723225)
              ·
                refine ⟨12922772348118932324792419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17230363130825243099723225 12922772348118932324792419)
                ·
                  refine ⟨19384158522178398487188629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12922772348118932324792419 19384158522178398487188629)
                  ·
                    refine ⟨908632430727112429086967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19384158522178398487188629 908632430727112429086967)
                    ·
                      rfl

theorem cell22_2654333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2654333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654333 prefixEnd_2654333 := by exact prefixLift 2654333
  have htrace : WordTrace (prefixWord ++ tailWord_2654333) baseStart_2654333 baseEnd_2654333 := by
    simpa [prefixWord, tailWord_2654333, baseEnd_2654333] using wordTrace_append hprefix tailTrace_2654333
  have hstable : (prefixWord ++ tailWord_2654333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654333).length < 2 ^ (prefixWord ++ tailWord_2654333).sum := by decide
  have hdescent : baseEnd_2654333 < baseStart_2654333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654408 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2654408 : Nat := 118140960795 + 2654408 * 2 ^ 59
def prefixEnd_2654408 : Nat := 4983230072969 + 3 ^ 40 * 2654408 * 2
def baseEnd_2654408 : Nat := 908658104759837233461737

theorem tailTrace_2654408 : CollatzResearch.WordTrace tailWord_2654408 prefixEnd_2654408 908658104759837233461737 := by
  unfold tailWord_2654408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48407106683770313819761939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64542808911693751759682585 48407106683770313819761939)
  ·
    refine ⟨72610660025655470729642909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48407106683770313819761939 72610660025655470729642909)
    ·
      refine ⟨27228997509620801523616091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72610660025655470729642909 27228997509620801523616091)
      ·
        refine ⟨40843496264431202285424137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27228997509620801523616091 40843496264431202285424137)
        ·
          refine ⟨30632622198323401714068103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40843496264431202285424137 30632622198323401714068103)
          ·
            refine ⟨45948933297485102571102155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30632622198323401714068103 45948933297485102571102155)
            ·
              refine ⟨68923399946227653856653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45948933297485102571102155 68923399946227653856653233)
              ·
                refine ⟨51692549959670740392489925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68923399946227653856653233 51692549959670740392489925)
                ·
                  refine ⟨9692353117438263823591861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51692549959670740392489925 9692353117438263823591861)
                  ·
                    refine ⟨908658104759837233461737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692353117438263823591861 908658104759837233461737)
                    ·
                      rfl

theorem cell22_2654408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2654408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654408 prefixEnd_2654408 := by exact prefixLift 2654408
  have htrace : WordTrace (prefixWord ++ tailWord_2654408) baseStart_2654408 baseEnd_2654408 := by
    simpa [prefixWord, tailWord_2654408, baseEnd_2654408] using wordTrace_append hprefix tailTrace_2654408
  have hstable : (prefixWord ++ tailWord_2654408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654408).length < 2 ^ (prefixWord ++ tailWord_2654408).sum := by decide
  have hdescent : baseEnd_2654408 < baseStart_2654408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654440 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2654440 : Nat := 118140960795 + 2654440 * 2 ^ 59
def prefixEnd_2654440 : Nat := 4983230072969 + 3 ^ 40 * 2654440 * 2
def baseEnd_2654440 : Nat := 908669059013799816661639

theorem tailTrace_2654440 : CollatzResearch.WordTrace tailWord_2654440 prefixEnd_2654440 908669059013799816661639 := by
  unfold tailWord_2654440
  simp only [CollatzResearch.WordTrace]
  refine ⟨48407690251712348552344387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64543587002283131403125849 48407690251712348552344387)
  ·
    refine ⟨72611535377568522828516581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48407690251712348552344387 72611535377568522828516581)
    ·
      refine ⟨13614662883294098030346859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72611535377568522828516581 13614662883294098030346859)
      ·
        refine ⟨20421994324941147045520289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13614662883294098030346859 20421994324941147045520289)
        ·
          refine ⟨15316495743705860284140217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20421994324941147045520289 15316495743705860284140217)
          ·
            refine ⟨11487371807779395213105163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15316495743705860284140217 11487371807779395213105163)
            ·
              refine ⟨17231057711669092819657745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11487371807779395213105163 17231057711669092819657745)
              ·
                refine ⟨12923293283751819614743309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17231057711669092819657745 12923293283751819614743309)
                ·
                  refine ⟨4846234981406932355528741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12923293283751819614743309 4846234981406932355528741)
                  ·
                    refine ⟨908669059013799816661639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4846234981406932355528741 908669059013799816661639)
                    ·
                      rfl

theorem cell22_2654440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2654440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654440 prefixEnd_2654440 := by exact prefixLift 2654440
  have htrace : WordTrace (prefixWord ++ tailWord_2654440) baseStart_2654440 baseEnd_2654440 := by
    simpa [prefixWord, tailWord_2654440, baseEnd_2654440] using wordTrace_append hprefix tailTrace_2654440
  have hstable : (prefixWord ++ tailWord_2654440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654440).length < 2 ^ (prefixWord ++ tailWord_2654440).sum := by decide
  have hdescent : baseEnd_2654440 < baseStart_2654440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654472 : List Nat := [2, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_2654472 : Nat := 118140960795 + 2654472 * 2 ^ 59
def prefixEnd_2654472 : Nat := 4983230072969 + 3 ^ 40 * 2654472 * 2
def baseEnd_2654472 : Nat := 302893337755920799953847

theorem tailTrace_2654472 : CollatzResearch.WordTrace tailWord_2654472 prefixEnd_2654472 302893337755920799953847 := by
  unfold tailWord_2654472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48408273819654383284926835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64544365092872511046569113 48408273819654383284926835)
  ·
    refine ⟨72612410729481574927390253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48408273819654383284926835 72612410729481574927390253)
    ·
      refine ⟨27229654023555590597771345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72612410729481574927390253 27229654023555590597771345)
      ·
        refine ⟨20422240517666692948328509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27229654023555590597771345 20422240517666692948328509)
        ·
          refine ⟨7658340194125009855623191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20422240517666692948328509 7658340194125009855623191)
          ·
            refine ⟨11487510291187514783434787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658340194125009855623191 11487510291187514783434787)
            ·
              refine ⟨17231265436781272175152181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11487510291187514783434787 17231265436781272175152181)
              ·
                refine ⟨1615431134698244266420517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17231265436781272175152181 1615431134698244266420517)
                ·
                  refine ⟨302893337755920799953847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615431134698244266420517 302893337755920799953847)
                  ·
                    rfl

theorem cell22_2654472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_2654472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654472 prefixEnd_2654472 := by exact prefixLift 2654472
  have htrace : WordTrace (prefixWord ++ tailWord_2654472) baseStart_2654472 baseEnd_2654472 := by
    simpa [prefixWord, tailWord_2654472, baseEnd_2654472] using wordTrace_append hprefix tailTrace_2654472
  have hstable : (prefixWord ++ tailWord_2654472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654472).length < 2 ^ (prefixWord ++ tailWord_2654472).sum := by decide
  have hdescent : baseEnd_2654472 < baseStart_2654472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654485 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2654485 : Nat := 118140960795 + 2654485 * 2 ^ 59
def prefixEnd_2654485 : Nat := 4983230072969 + 3 ^ 40 * 2654485 * 2
def baseEnd_2654485 : Nat := 908684463433434699286501

theorem tailTrace_2654485 : CollatzResearch.WordTrace tailWord_2654485 prefixEnd_2654485 908684463433434699286501 := by
  unfold tailWord_2654485
  simp only [CollatzResearch.WordTrace]
  refine ⟨96817021788261669790076909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64544681192174446526717939 96817021788261669790076909)
  ·
    refine ⟨36306383170598126171278841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96817021788261669790076909 36306383170598126171278841)
    ·
      refine ⟨27229787377948594628459131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36306383170598126171278841 27229787377948594628459131)
      ·
        refine ⟨40844681066922891942688697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27229787377948594628459131 40844681066922891942688697)
        ·
          refine ⟨30633510800192168957016523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40844681066922891942688697 30633510800192168957016523)
          ·
            refine ⟨45950266200288253435524785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30633510800192168957016523 45950266200288253435524785)
            ·
              refine ⟨34462699650216190076643589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45950266200288253435524785 34462699650216190076643589)
              ·
                refine ⟨6461756184415535639370673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34462699650216190076643589 6461756184415535639370673)
                ·
                  refine ⟨4846317138311651729528005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461756184415535639370673 4846317138311651729528005)
                  ·
                    refine ⟨908684463433434699286501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4846317138311651729528005 908684463433434699286501)
                    ·
                      rfl

theorem cell22_2654485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2654485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654485 prefixEnd_2654485 := by exact prefixLift 2654485
  have htrace : WordTrace (prefixWord ++ tailWord_2654485) baseStart_2654485 baseEnd_2654485 := by
    simpa [prefixWord, tailWord_2654485, baseEnd_2654485] using wordTrace_append hprefix tailTrace_2654485
  have hstable : (prefixWord ++ tailWord_2654485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654485).length < 2 ^ (prefixWord ++ tailWord_2654485).sum := by decide
  have hdescent : baseEnd_2654485 < baseStart_2654485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654487 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 4, 3]
def baseStart_2654487 : Nat := 118140960795 + 2654487 * 2 ^ 59
def prefixEnd_2654487 : Nat := 4983230072969 + 3 ^ 40 * 2654487 * 2
def baseEnd_2654487 : Nat := 908685148074307360736495

theorem tailTrace_2654487 : CollatzResearch.WordTrace tailWord_2654487 prefixEnd_2654487 908685148074307360736495 := by
  unfold tailWord_2654487
  simp only [CollatzResearch.WordTrace]
  refine ⟨96817094734254424131649715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64544729822836282754433143 96817094734254424131649715)
  ·
    refine ⟨145225642101381636197474573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96817094734254424131649715 145225642101381636197474573)
    ·
      refine ⟨54459615788018113574052965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145225642101381636197474573 54459615788018113574052965)
      ·
        refine ⟨10211177960253396295134931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54459615788018113574052965 10211177960253396295134931)
        ·
          refine ⟨15316766940380094442702397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211177960253396295134931 15316766940380094442702397)
          ·
            refine ⟨5743787602642535416013399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15316766940380094442702397 5743787602642535416013399)
            ·
              refine ⟨8615681403963803124020099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743787602642535416013399 8615681403963803124020099)
              ·
                refine ⟨12923522105945704686030149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615681403963803124020099 12923522105945704686030149)
                ·
                  refine ⟨2423160394864819628630653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12923522105945704686030149 2423160394864819628630653)
                  ·
                    refine ⟨908685148074307360736495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423160394864819628630653 908685148074307360736495)
                    ·
                      rfl

theorem cell22_2654487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_2654487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654487 prefixEnd_2654487 := by exact prefixLift 2654487
  have htrace : WordTrace (prefixWord ++ tailWord_2654487) baseStart_2654487 baseEnd_2654487 := by
    simpa [prefixWord, tailWord_2654487, baseEnd_2654487] using wordTrace_append hprefix tailTrace_2654487
  have hstable : (prefixWord ++ tailWord_2654487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654487).length < 2 ^ (prefixWord ++ tailWord_2654487).sum := by decide
  have hdescent : baseEnd_2654487 < baseStart_2654487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654504 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2654504 : Nat := 118140960795 + 2654504 * 2 ^ 59
def prefixEnd_2654504 : Nat := 4983230072969 + 3 ^ 40 * 2654504 * 2
def baseEnd_2654504 : Nat := 908690967521724983061443

theorem tailTrace_2654504 : CollatzResearch.WordTrace tailWord_2654504 prefixEnd_2654504 908690967521724983061443 := by
  unfold tailWord_2654504
  simp only [CollatzResearch.WordTrace]
  refine ⟨48408857387596418017509283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64545143183461890690012377 48408857387596418017509283)
  ·
    refine ⟨72613286081394627026263925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48408857387596418017509283 72613286081394627026263925)
    ·
      refine ⟨6807495570130746283712243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72613286081394627026263925 6807495570130746283712243)
      ·
        refine ⟨10211243355196119425568365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807495570130746283712243 10211243355196119425568365)
        ·
          refine ⟨3829216258198544784588137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10211243355196119425568365 3829216258198544784588137)
          ·
            refine ⟨2871912193648908588441103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3829216258198544784588137 2871912193648908588441103)
            ·
              refine ⟨4307868290473362882661655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871912193648908588441103 4307868290473362882661655)
              ·
                refine ⟨6461802435710044323992483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307868290473362882661655 6461802435710044323992483)
                ·
                  refine ⟨9692703653565066485988725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461802435710044323992483 9692703653565066485988725)
                  ·
                    refine ⟨908690967521724983061443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692703653565066485988725 908690967521724983061443)
                    ·
                      rfl

theorem cell22_2654504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2654504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654504 prefixEnd_2654504 := by exact prefixLift 2654504
  have htrace : WordTrace (prefixWord ++ tailWord_2654504) baseStart_2654504 baseEnd_2654504 := by
    simpa [prefixWord, tailWord_2654504, baseEnd_2654504] using wordTrace_append hprefix tailTrace_2654504
  have hstable : (prefixWord ++ tailWord_2654504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654504).length < 2 ^ (prefixWord ++ tailWord_2654504).sum := by decide
  have hdescent : baseEnd_2654504 < baseStart_2654504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654545 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 7]
def baseStart_2654545 : Nat := 118140960795 + 2654545 * 2 ^ 59
def prefixEnd_2654545 : Nat := 4983230072969 + 3 ^ 40 * 2654545 * 2
def baseEnd_2654545 : Nat := 302901667553204847595439

theorem tailTrace_2654545 : CollatzResearch.WordTrace tailWord_2654545 prefixEnd_2654545 302901667553204847595439 := by
  unfold tailWord_2654545
  simp only [CollatzResearch.WordTrace]
  refine ⟨96819210168044300037261089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64546140112029533358174059 96819210168044300037261089)
  ·
    refine ⟨72614407626033225027945817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96819210168044300037261089 72614407626033225027945817)
    ·
      refine ⟨54460805719524918770959363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72614407626033225027945817 54460805719524918770959363)
      ·
        refine ⟨81691208579287378156439045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54460805719524918770959363 81691208579287378156439045)
        ·
          refine ⟨15317101608616383404332321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81691208579287378156439045 15317101608616383404332321)
          ·
            refine ⟨11487826206462287553249241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15317101608616383404332321 11487826206462287553249241)
            ·
              refine ⟨8615869654846715664936931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11487826206462287553249241 8615869654846715664936931)
              ·
                refine ⟨12923804482270073497405397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615869654846715664936931 12923804482270073497405397)
                ·
                  refine ⟨302901667553204847595439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12923804482270073497405397 302901667553204847595439)
                  ·
                    rfl

theorem cell22_2654545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_2654545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654545 prefixEnd_2654545 := by exact prefixLift 2654545
  have htrace : WordTrace (prefixWord ++ tailWord_2654545) baseStart_2654545 baseEnd_2654545 := by
    simpa [prefixWord, tailWord_2654545, baseEnd_2654545] using wordTrace_append hprefix tailTrace_2654545
  have hstable : (prefixWord ++ tailWord_2654545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654545).length < 2 ^ (prefixWord ++ tailWord_2654545).sum := by decide
  have hdescent : baseEnd_2654545 < baseStart_2654545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654650 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2654650 : Nat := 118140960795 + 2654650 * 2 ^ 59
def prefixEnd_2654650 : Nat := 4983230072969 + 3 ^ 40 * 2654650 * 2
def baseEnd_2654650 : Nat := 908740946305429268910995

theorem tailTrace_2654650 : CollatzResearch.WordTrace tailWord_2654650 prefixEnd_2654650 908740946305429268910995 := by
  unfold tailWord_2654650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24205759958165975742458351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64548693221775935313222269 24205759958165975742458351)
  ·
    refine ⟨36308639937248963613687527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24205759958165975742458351 36308639937248963613687527)
    ·
      refine ⟨54462959905873445420531291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36308639937248963613687527 54462959905873445420531291)
      ·
        refine ⟨81694439858810168130796937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54462959905873445420531291 81694439858810168130796937)
        ·
          refine ⟨61270829894107626098097703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81694439858810168130796937 61270829894107626098097703)
          ·
            refine ⟨91906244841161439147146555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61270829894107626098097703 91906244841161439147146555)
            ·
              refine ⟨137859367261742158720719833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91906244841161439147146555 137859367261742158720719833)
              ·
                refine ⟨103394525446306619040539875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137859367261742158720719833 103394525446306619040539875)
                ·
                  refine ⟨155091788169459928560809813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103394525446306619040539875 155091788169459928560809813)
                  ·
                    refine ⟨908740946305429268910995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155091788169459928560809813 908740946305429268910995)
                    ·
                      rfl

theorem cell22_2654650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2654650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654650 prefixEnd_2654650 := by exact prefixLift 2654650
  have htrace : WordTrace (prefixWord ++ tailWord_2654650) baseStart_2654650 baseEnd_2654650 := by
    simpa [prefixWord, tailWord_2654650, baseEnd_2654650] using wordTrace_append hprefix tailTrace_2654650
  have hstable : (prefixWord ++ tailWord_2654650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654650).length < 2 ^ (prefixWord ++ tailWord_2654650).sum := by decide
  have hdescent : baseEnd_2654650 < baseStart_2654650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654652 : List Nat := [2, 2, 2, 4, 1, 2, 9]
def baseStart_2654652 : Nat := 118140960795 + 2654652 * 2 ^ 59
def prefixEnd_2654652 : Nat := 4983230072969 + 3 ^ 40 * 2654652 * 2
def baseEnd_2654652 : Nat := 33657097442455627050407

theorem tailTrace_2654652 : CollatzResearch.WordTrace tailWord_2654652 prefixEnd_2654652 33657097442455627050407 := by
  unfold tailWord_2654652
  simp only [CollatzResearch.WordTrace]
  refine ⟨48411556389328328655703105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64548741852437771540937473 48411556389328328655703105)
  ·
    refine ⟨36308667291996246491777329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48411556389328328655703105 36308667291996246491777329)
    ·
      refine ⟨27231500468997184868832997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36308667291996246491777329 27231500468997184868832997)
      ·
        refine ⟨5105906337936972162906187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27231500468997184868832997 5105906337936972162906187)
        ·
          refine ⟨7658859506905458244359281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105906337936972162906187 7658859506905458244359281)
          ·
            refine ⟨5744144630179093683269461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7658859506905458244359281 5744144630179093683269461)
            ·
              refine ⟨33657097442455627050407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5744144630179093683269461 33657097442455627050407)
              ·
                rfl

theorem cell22_2654652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 9].length) (baseStart_2654652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654652 prefixEnd_2654652 := by exact prefixLift 2654652
  have htrace : WordTrace (prefixWord ++ tailWord_2654652) baseStart_2654652 baseEnd_2654652 := by
    simpa [prefixWord, tailWord_2654652, baseEnd_2654652] using wordTrace_append hprefix tailTrace_2654652
  have hstable : (prefixWord ++ tailWord_2654652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654652).length < 2 ^ (prefixWord ++ tailWord_2654652).sum := by decide
  have hdescent : baseEnd_2654652 < baseStart_2654652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654665 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2654665 : Nat := 118140960795 + 2654665 * 2 ^ 59
def prefixEnd_2654665 : Nat := 4983230072969 + 3 ^ 40 * 2654665 * 2
def baseEnd_2654665 : Nat := 908746081111974229785949

theorem tailTrace_2654665 : CollatzResearch.WordTrace tailWord_2654665 prefixEnd_2654665 908746081111974229785949 := by
  unfold tailWord_2654665
  simp only [CollatzResearch.WordTrace]
  refine ⟨96823586927609560531629449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64549057951739707021086299 96823586927609560531629449)
  ·
    refine ⟨72617690195707170398722087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96823586927609560531629449 72617690195707170398722087)
    ·
      refine ⟨108926535293560755598083131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72617690195707170398722087 108926535293560755598083131)
      ·
        refine ⟨163389802940341133397124697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108926535293560755598083131 163389802940341133397124697)
        ·
          refine ⟨122542352205255850047843523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163389802940341133397124697 122542352205255850047843523)
          ·
            refine ⟨183813528307883775071765285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122542352205255850047843523 183813528307883775071765285)
            ·
              refine ⟨34465036557728207825955991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183813528307883775071765285 34465036557728207825955991)
              ·
                refine ⟨51697554836592311738933987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34465036557728207825955991 51697554836592311738933987)
                ·
                  refine ⟨77546332254888467608400981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51697554836592311738933987 77546332254888467608400981)
                  ·
                    refine ⟨908746081111974229785949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77546332254888467608400981 908746081111974229785949)
                    ·
                      rfl

theorem cell22_2654665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2654665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654665 prefixEnd_2654665 := by exact prefixLift 2654665
  have htrace : WordTrace (prefixWord ++ tailWord_2654665) baseStart_2654665 baseEnd_2654665 := by
    simpa [prefixWord, tailWord_2654665, baseEnd_2654665] using wordTrace_append hprefix tailTrace_2654665
  have hstable : (prefixWord ++ tailWord_2654665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654665).length < 2 ^ (prefixWord ++ tailWord_2654665).sum := by decide
  have hdescent : baseEnd_2654665 < baseStart_2654665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654731 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 5]
def baseStart_2654731 : Nat := 118140960795 + 2654731 * 2 ^ 59
def prefixEnd_2654731 : Nat := 4983230072969 + 3 ^ 40 * 2654731 * 2
def baseEnd_2654731 : Nat := 302922891420257352545249

theorem tailTrace_2654731 : CollatzResearch.WordTrace tailWord_2654731 prefixEnd_2654731 302922891420257352545249 := by
  unfold tailWord_2654731
  simp only [CollatzResearch.WordTrace]
  refine ⟨96825994145370453803532047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64550662763580302535688031 96825994145370453803532047)
  ·
    refine ⟨145238991218055680705298071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96825994145370453803532047 145238991218055680705298071)
    ·
      refine ⟨217858486827083521057947107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145238991218055680705298071 217858486827083521057947107)
      ·
        refine ⟨326787730240625281586920661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217858486827083521057947107 326787730240625281586920661)
        ·
          refine ⟨7659087427514655037193453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 326787730240625281586920661 7659087427514655037193453)
          ·
            refine ⟨2872157785317995638947545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7659087427514655037193453 2872157785317995638947545)
            ·
              refine ⟨2154118338988496729210659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872157785317995638947545 2154118338988496729210659)
              ·
                refine ⟨3231177508482745093815989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154118338988496729210659 3231177508482745093815989)
                ·
                  refine ⟨302922891420257352545249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3231177508482745093815989 302922891420257352545249)
                  ·
                    rfl

theorem cell22_2654731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 5].length) (baseStart_2654731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654731 prefixEnd_2654731 := by exact prefixLift 2654731
  have htrace : WordTrace (prefixWord ++ tailWord_2654731) baseStart_2654731 baseEnd_2654731 := by
    simpa [prefixWord, tailWord_2654731, baseEnd_2654731] using wordTrace_append hprefix tailTrace_2654731
  have hstable : (prefixWord ++ tailWord_2654731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654731).length < 2 ^ (prefixWord ++ tailWord_2654731).sum := by decide
  have hdescent : baseEnd_2654731 < baseStart_2654731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654744 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2654744 : Nat := 118140960795 + 2654744 * 2 ^ 59
def prefixEnd_2654744 : Nat := 4983230072969 + 3 ^ 40 * 2654744 * 2
def baseEnd_2654744 : Nat := 908773124426444357060707

theorem tailTrace_2654744 : CollatzResearch.WordTrace tailWord_2654744 prefixEnd_2654744 908773124426444357060707 := by
  unfold tailWord_2654744
  simp only [CollatzResearch.WordTrace]
  refine ⟨48413234147161678511877643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64550978862882238015836857 48413234147161678511877643)
  ·
    refine ⟨72619851220742517767816465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48413234147161678511877643 72619851220742517767816465)
    ·
      refine ⟨54464888415556888325862349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72619851220742517767816465 54464888415556888325862349)
      ·
        refine ⟨20424333155833833122198381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54464888415556888325862349 20424333155833833122198381)
        ·
          refine ⟨7659124933437687420824393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20424333155833833122198381 7659124933437687420824393)
          ·
            refine ⟨5744343700078265565618295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7659124933437687420824393 5744343700078265565618295)
            ·
              refine ⟨8616515550117398348427443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744343700078265565618295 8616515550117398348427443)
              ·
                refine ⟨12924773325176097522641165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8616515550117398348427443 12924773325176097522641165)
                ·
                  refine ⟨4846789996941036570990437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12924773325176097522641165 4846789996941036570990437)
                  ·
                    refine ⟨908773124426444357060707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4846789996941036570990437 908773124426444357060707)
                    ·
                      rfl

theorem cell22_2654744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2654744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654744 prefixEnd_2654744 := by exact prefixLift 2654744
  have htrace : WordTrace (prefixWord ++ tailWord_2654744) baseStart_2654744 baseEnd_2654744 := by
    simpa [prefixWord, tailWord_2654744, baseEnd_2654744] using wordTrace_append hprefix tailTrace_2654744
  have hstable : (prefixWord ++ tailWord_2654744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654744).length < 2 ^ (prefixWord ++ tailWord_2654744).sum := by decide
  have hdescent : baseEnd_2654744 < baseStart_2654744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654757 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2654757 : Nat := 118140960795 + 2654757 * 2 ^ 59
def prefixEnd_2654757 : Nat := 4983230072969 + 3 ^ 40 * 2654757 * 2
def baseEnd_2654757 : Nat := 908777574592116656485667

theorem tailTrace_2654757 : CollatzResearch.WordTrace tailWord_2654757 prefixEnd_2654757 908777574592116656485667 := by
  unfold tailWord_2654757
  simp only [CollatzResearch.WordTrace]
  refine ⟨96826942443276260243978525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64551294962184173495985683 96826942443276260243978525)
  ·
    refine ⟨36310103416228597591491947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96826942443276260243978525 36310103416228597591491947)
    ·
      refine ⟨54465155124342896387237921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36310103416228597591491947 54465155124342896387237921)
      ·
        refine ⟨40848866343257172290428441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54465155124342896387237921 40848866343257172290428441)
        ·
          refine ⟨30636649757442879217821331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40848866343257172290428441 30636649757442879217821331)
          ·
            refine ⟨45954974636164318826731997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30636649757442879217821331 45954974636164318826731997)
            ·
              refine ⟨17233115488561619560024499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45954974636164318826731997 17233115488561619560024499)
              ·
                refine ⟨25849673232842429340036749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17233115488561619560024499 25849673232842429340036749)
                ·
                  refine ⟨9693627462315911002513781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25849673232842429340036749 9693627462315911002513781)
                  ·
                    refine ⟨908777574592116656485667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9693627462315911002513781 908777574592116656485667)
                    ·
                      rfl

theorem cell22_2654757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2654757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654757 prefixEnd_2654757 := by exact prefixLift 2654757
  have htrace : WordTrace (prefixWord ++ tailWord_2654757) baseStart_2654757 baseEnd_2654757 := by
    simpa [prefixWord, tailWord_2654757, baseEnd_2654757] using wordTrace_append hprefix tailTrace_2654757
  have hstable : (prefixWord ++ tailWord_2654757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654757).length < 2 ^ (prefixWord ++ tailWord_2654757).sum := by decide
  have hdescent : baseEnd_2654757 < baseStart_2654757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654765 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2654765 : Nat := 118140960795 + 2654765 * 2 ^ 59
def prefixEnd_2654765 : Nat := 4983230072969 + 3 ^ 40 * 2654765 * 2
def baseEnd_2654765 : Nat := 302926771051869100761881

theorem tailTrace_2654765 : CollatzResearch.WordTrace tailWord_2654765 prefixEnd_2654765 302926771051869100761881 := by
  unfold tailWord_2654765
  simp only [CollatzResearch.WordTrace]
  refine ⟨96827234227247277610269749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64551489484831518406846499 96827234227247277610269749)
  ·
    refine ⟨9077553208804432275962789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96827234227247277610269749 9077553208804432275962789)
    ·
      refine ⟨1702041226650831051743023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9077553208804432275962789 1702041226650831051743023)
      ·
        refine ⟨2553061839976246577614535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702041226650831051743023 2553061839976246577614535)
        ·
          refine ⟨3829592759964369866421803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553061839976246577614535 3829592759964369866421803)
          ·
            refine ⟨5744389139946554799632705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829592759964369866421803 5744389139946554799632705)
            ·
              refine ⟨4308291854959916099724529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744389139946554799632705 4308291854959916099724529)
              ·
                refine ⟨3231218891219937074793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308291854959916099724529 3231218891219937074793397)
                ·
                  refine ⟨302926771051869100761881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3231218891219937074793397 302926771051869100761881)
                  ·
                    rfl

theorem cell22_2654765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2654765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654765 prefixEnd_2654765 := by exact prefixLift 2654765
  have htrace : WordTrace (prefixWord ++ tailWord_2654765) baseStart_2654765 baseEnd_2654765 := by
    simpa [prefixWord, tailWord_2654765, baseEnd_2654765] using wordTrace_append hprefix tailTrace_2654765
  have hstable : (prefixWord ++ tailWord_2654765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654765).length < 2 ^ (prefixWord ++ tailWord_2654765).sum := by decide
  have hdescent : baseEnd_2654765 < baseStart_2654765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654791 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2654791 : Nat := 118140960795 + 2654791 * 2 ^ 59
def prefixEnd_2654791 : Nat := 4983230072969 + 3 ^ 40 * 2654791 * 2
def baseEnd_2654791 : Nat := 908789213486951901135563

theorem tailTrace_2654791 : CollatzResearch.WordTrace tailWord_2654791 prefixEnd_2654791 908789213486951901135563 := by
  unfold tailWord_2654791
  simp only [CollatzResearch.WordTrace]
  refine ⟨96828182525153084050716227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64552121683435389367144151 96828182525153084050716227)
  ·
    refine ⟨145242273787729626076074341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96828182525153084050716227 145242273787729626076074341)
    ·
      refine ⟨27232926335199304889263939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145242273787729626076074341 27232926335199304889263939)
      ·
        refine ⟨40849389502798957333895909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27232926335199304889263939 40849389502798957333895909)
        ·
          refine ⟨7659260531774804500105483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40849389502798957333895909 7659260531774804500105483)
          ·
            refine ⟨11488890797662206750158225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659260531774804500105483 11488890797662206750158225)
            ·
              refine ⟨8616668098246655062618669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11488890797662206750158225 8616668098246655062618669)
              ·
                refine ⟨3231250536842495648482001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8616668098246655062618669 3231250536842495648482001)
                ·
                  refine ⟨2423437902631871736361501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231250536842495648482001 2423437902631871736361501)
                  ·
                    refine ⟨908789213486951901135563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423437902631871736361501 908789213486951901135563)
                    ·
                      rfl

theorem cell22_2654791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2654791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654791 prefixEnd_2654791 := by exact prefixLift 2654791
  have htrace : WordTrace (prefixWord ++ tailWord_2654791) baseStart_2654791 baseEnd_2654791 := by
    simpa [prefixWord, tailWord_2654791, baseEnd_2654791] using wordTrace_append hprefix tailTrace_2654791
  have hstable : (prefixWord ++ tailWord_2654791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654791).length < 2 ^ (prefixWord ++ tailWord_2654791).sum := by decide
  have hdescent : baseEnd_2654791 < baseStart_2654791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654819 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 5, 3]
def baseStart_2654819 : Nat := 118140960795 + 2654819 * 2 ^ 59
def prefixEnd_2654819 : Nat := 4983230072969 + 3 ^ 40 * 2654819 * 2
def baseEnd_2654819 : Nat := 908798798459169161435477

theorem tailTrace_2654819 : CollatzResearch.WordTrace tailWord_2654819 prefixEnd_2654819 908798798459169161435477 := by
  unfold tailWord_2654819
  simp only [CollatzResearch.WordTrace]
  refine ⟨96829203769051644832735511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64552802512701096555157007 96829203769051644832735511)
  ·
    refine ⟨145243805653577467249103267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96829203769051644832735511 145243805653577467249103267)
    ·
      refine ⟨217865708480366200873654901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145243805653577467249103267 217865708480366200873654901)
      ·
        refine ⟨20424910170034331331905147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217865708480366200873654901 20424910170034331331905147)
        ·
          refine ⟨30637365255051496997857721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20424910170034331331905147 30637365255051496997857721)
          ·
            refine ⟨22978023941288622748393291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30637365255051496997857721 22978023941288622748393291)
            ·
              refine ⟨34467035911932934122589937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22978023941288622748393291 34467035911932934122589937)
              ·
                refine ⟨25850276933949700591942453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34467035911932934122589937 25850276933949700591942453)
                ·
                  refine ⟨2423463462557784430494605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25850276933949700591942453 2423463462557784430494605)
                  ·
                    refine ⟨908798798459169161435477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423463462557784430494605 908798798459169161435477)
                    ·
                      rfl

theorem cell22_2654819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].length) (baseStart_2654819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654819 prefixEnd_2654819 := by exact prefixLift 2654819
  have htrace : WordTrace (prefixWord ++ tailWord_2654819) baseStart_2654819 baseEnd_2654819 := by
    simpa [prefixWord, tailWord_2654819, baseEnd_2654819] using wordTrace_append hprefix tailTrace_2654819
  have hstable : (prefixWord ++ tailWord_2654819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654819).length < 2 ^ (prefixWord ++ tailWord_2654819).sum := by decide
  have hdescent : baseEnd_2654819 < baseStart_2654819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654847 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2654847 : Nat := 118140960795 + 2654847 * 2 ^ 59
def prefixEnd_2654847 : Nat := 4983230072969 + 3 ^ 40 * 2654847 * 2
def baseEnd_2654847 : Nat := 908808383431386421735391

theorem tailTrace_2654847 : CollatzResearch.WordTrace tailWord_2654847 prefixEnd_2654847 908808383431386421735391 := by
  unfold tailWord_2654847
  simp only [CollatzResearch.WordTrace]
  refine ⟨96830225012950205614754795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64553483341966803743169863 96830225012950205614754795)
  ·
    refine ⟨145245337519425308422132193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96830225012950205614754795 145245337519425308422132193)
    ·
      refine ⟨108934003139568981316599145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145245337519425308422132193 108934003139568981316599145)
      ·
        refine ⟨81700502354676735987449359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108934003139568981316599145 81700502354676735987449359)
        ·
          refine ⟨122550753532015103981174039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81700502354676735987449359 122550753532015103981174039)
          ·
            refine ⟨183826130298022655971761059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122550753532015103981174039 183826130298022655971761059)
            ·
              refine ⟨275739195447033983957641589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183826130298022655971761059 275739195447033983957641589)
              ·
                refine ⟨25850549573159435996028899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275739195447033983957641589 25850549573159435996028899)
                ·
                  refine ⟨38775824359739153994043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25850549573159435996028899 38775824359739153994043349)
                  ·
                    refine ⟨908808383431386421735391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38775824359739153994043349 908808383431386421735391)
                    ·
                      rfl

theorem cell22_2654847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2654847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654847 prefixEnd_2654847 := by exact prefixLift 2654847
  have htrace : WordTrace (prefixWord ++ tailWord_2654847) baseStart_2654847 baseEnd_2654847 := by
    simpa [prefixWord, tailWord_2654847, baseEnd_2654847] using wordTrace_append hprefix tailTrace_2654847
  have hstable : (prefixWord ++ tailWord_2654847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654847).length < 2 ^ (prefixWord ++ tailWord_2654847).sum := by decide
  have hdescent : baseEnd_2654847 < baseStart_2654847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654887 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2654887 : Nat := 118140960795 + 2654887 * 2 ^ 59
def prefixEnd_2654887 : Nat := 4983230072969 + 3 ^ 40 * 2654887 * 2
def baseEnd_2654887 : Nat := 908822076248839650735269

theorem tailTrace_2654887 : CollatzResearch.WordTrace tailWord_2654887 prefixEnd_2654887 908822076248839650735269 := by
  unfold tailWord_2654887
  simp only [CollatzResearch.WordTrace]
  refine ⟨96831683932805292446210915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64554455955203528297473943 96831683932805292446210915)
  ·
    refine ⟨145247525899207938669316373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96831683932805292446210915 145247525899207938669316373)
    ·
      refine ⟨6808477776525372125124205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145247525899207938669316373 6808477776525372125124205)
      ·
        refine ⟨2553179166197014546921577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6808477776525372125124205 2553179166197014546921577)
        ·
          refine ⟨1914884374647760910191183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553179166197014546921577 1914884374647760910191183)
          ·
            refine ⟨2872326561971641365286775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914884374647760910191183 2872326561971641365286775)
            ·
              refine ⟨4308489842957462047930163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872326561971641365286775 4308489842957462047930163)
              ·
                refine ⟨6462734764436193071895245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308489842957462047930163 6462734764436193071895245)
                ·
                  refine ⟨2423525536663572401960717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6462734764436193071895245 2423525536663572401960717)
                  ·
                    refine ⟨908822076248839650735269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423525536663572401960717 908822076248839650735269)
                    ·
                      rfl

theorem cell22_2654887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2654887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654887 prefixEnd_2654887 := by exact prefixLift 2654887
  have htrace : WordTrace (prefixWord ++ tailWord_2654887) baseStart_2654887 baseEnd_2654887 := by
    simpa [prefixWord, tailWord_2654887, baseEnd_2654887] using wordTrace_append hprefix tailTrace_2654887
  have hstable : (prefixWord ++ tailWord_2654887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654887).length < 2 ^ (prefixWord ++ tailWord_2654887).sum := by decide
  have hdescent : baseEnd_2654887 < baseStart_2654887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654926 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2654926 : Nat := 118140960795 + 2654926 * 2 ^ 59
def prefixEnd_2654926 : Nat := 4983230072969 + 3 ^ 40 * 2654926 * 2
def baseEnd_2654926 : Nat := 908835426745856549010149

theorem tailTrace_2654926 : CollatzResearch.WordTrace tailWord_2654926 prefixEnd_2654926 908835426745856549010149 := by
  unfold tailWord_2654926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104138297458000263360079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64555404253109334737920421 12104138297458000263360079)
  ·
    refine ⟨18156207446187000395040119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12104138297458000263360079 18156207446187000395040119)
    ·
      refine ⟨27234311169280500592560179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18156207446187000395040119 27234311169280500592560179)
      ·
        refine ⟨40851466753920750888840269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27234311169280500592560179 40851466753920750888840269)
        ·
          refine ⟨15319300032720281583315101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40851466753920750888840269 15319300032720281583315101)
          ·
            refine ⟨5744737512270105593743163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15319300032720281583315101 5744737512270105593743163)
            ·
              refine ⟨8617106268405158390614745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744737512270105593743163 8617106268405158390614745)
              ·
                refine ⟨6462829701303868792961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8617106268405158390614745 6462829701303868792961059)
                ·
                  refine ⟨9694244551955803189441589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462829701303868792961059 9694244551955803189441589)
                  ·
                    refine ⟨908835426745856549010149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9694244551955803189441589 908835426745856549010149)
                    ·
                      rfl

theorem cell22_2654926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2654926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654926 prefixEnd_2654926 := by exact prefixLift 2654926
  have htrace : WordTrace (prefixWord ++ tailWord_2654926) baseStart_2654926 baseEnd_2654926 := by
    simpa [prefixWord, tailWord_2654926, baseEnd_2654926] using wordTrace_append hprefix tailTrace_2654926
  have hstable : (prefixWord ++ tailWord_2654926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654926).length < 2 ^ (prefixWord ++ tailWord_2654926).sum := by decide
  have hdescent : baseEnd_2654926 < baseStart_2654926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654930 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2654930 : Nat := 118140960795 + 2654930 * 2 ^ 59
def prefixEnd_2654930 : Nat := 4983230072969 + 3 ^ 40 * 2654930 * 2
def baseEnd_2654930 : Nat := 908836796027601871910137

theorem tailTrace_2654930 : CollatzResearch.WordTrace tailWord_2654930 prefixEnd_2654930 908836796027601871910137 := by
  unfold tailWord_2654930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208313067912377697506561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64555501514433007193350829 24208313067912377697506561)
  ·
    refine ⟨18156234800934283273129921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24208313067912377697506561 18156234800934283273129921)
    ·
      refine ⟨13617176100700712454847441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18156234800934283273129921 13617176100700712454847441)
      ·
        refine ⟨10212882075525534341135581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13617176100700712454847441 10212882075525534341135581)
        ·
          refine ⟨3829830778322075377925843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10212882075525534341135581 3829830778322075377925843)
          ·
            refine ⟨5744746167483113066888765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829830778322075377925843 5744746167483113066888765)
            ·
              refine ⟨2154279812806167400083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5744746167483113066888765 2154279812806167400083287)
              ·
                refine ⟨3231419719209251100124931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154279812806167400083287 3231419719209251100124931)
                ·
                  refine ⟨4847129578813876650187397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231419719209251100124931 4847129578813876650187397)
                  ·
                    refine ⟨908836796027601871910137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847129578813876650187397 908836796027601871910137)
                    ·
                      rfl

theorem cell22_2654930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2654930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654930 prefixEnd_2654930 := by exact prefixLift 2654930
  have htrace : WordTrace (prefixWord ++ tailWord_2654930) baseStart_2654930 baseEnd_2654930 := by
    simpa [prefixWord, tailWord_2654930, baseEnd_2654930] using wordTrace_append hprefix tailTrace_2654930
  have hstable : (prefixWord ++ tailWord_2654930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654930).length < 2 ^ (prefixWord ++ tailWord_2654930).sum := by decide
  have hdescent : baseEnd_2654930 < baseStart_2654930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654943 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 2, 3]
def baseStart_2654943 : Nat := 118140960795 + 2654943 * 2 ^ 59
def prefixEnd_2654943 : Nat := 4983230072969 + 3 ^ 40 * 2654943 * 2
def baseEnd_2654943 : Nat := 908841246193274171335097

theorem tailTrace_2654943 : CollatzResearch.WordTrace tailWord_2654943 prefixEnd_2654943 908841246193274171335097 := by
  unfold tailWord_2654943
  simp only [CollatzResearch.WordTrace]
  refine ⟨96833726420602414010249483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64555817613734942673499655 96833726420602414010249483)
  ·
    refine ⟨145250589630903621015374225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96833726420602414010249483 145250589630903621015374225)
    ·
      refine ⟨108937942223177715761530669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145250589630903621015374225 108937942223177715761530669)
      ·
        refine ⟨40851728333691643410574001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108937942223177715761530669 40851728333691643410574001)
        ·
          refine ⟨30638796250268732557930501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40851728333691643410574001 30638796250268732557930501)
          ·
            refine ⟨5744774296925387354611969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30638796250268732557930501 5744774296925387354611969)
            ·
              refine ⟨4308580722694040515958977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744774296925387354611969 4308580722694040515958977)
              ·
                refine ⟨3231435542020530386969233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308580722694040515958977 3231435542020530386969233)
                ·
                  refine ⟨2423576656515397790226925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231435542020530386969233 2423576656515397790226925)
                  ·
                    refine ⟨908841246193274171335097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423576656515397790226925 908841246193274171335097)
                    ·
                      rfl

theorem cell22_2654943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_2654943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654943 prefixEnd_2654943 := by exact prefixLift 2654943
  have htrace : WordTrace (prefixWord ++ tailWord_2654943) baseStart_2654943 baseEnd_2654943 := by
    simpa [prefixWord, tailWord_2654943, baseEnd_2654943] using wordTrace_append hprefix tailTrace_2654943
  have hstable : (prefixWord ++ tailWord_2654943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654943).length < 2 ^ (prefixWord ++ tailWord_2654943).sum := by decide
  have hdescent : baseEnd_2654943 < baseStart_2654943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654945 : List Nat := [1, 2, 3, 1, 4, 3, 2, 2, 4]
def baseStart_2654945 : Nat := 118140960795 + 2654945 * 2 ^ 59
def prefixEnd_2654945 : Nat := 4983230072969 + 3 ^ 40 * 2654945 * 2
def baseEnd_2654945 : Nat := 302947310278048944261697

theorem tailTrace_2654945 : CollatzResearch.WordTrace tailWord_2654945 prefixEnd_2654945 302947310278048944261697 := by
  unfold tailWord_2654945
  simp only [CollatzResearch.WordTrace]
  refine ⟨96833799366595168351822289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64555866244396778901214859 96833799366595168351822289)
  ·
    refine ⟨72625349524946376263866717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96833799366595168351822289 72625349524946376263866717)
    ·
      refine ⟨27234506071854891098950019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72625349524946376263866717 27234506071854891098950019)
      ·
        refine ⟨40851759107782336648425029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27234506071854891098950019 40851759107782336648425029)
        ·
          refine ⟨7659704832709188121579693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40851759107782336648425029 7659704832709188121579693)
          ·
            refine ⟨2872389312265945545592385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7659704832709188121579693 2872389312265945545592385)
            ·
              refine ⟨2154291984199459159194289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872389312265945545592385 2154291984199459159194289)
              ·
                refine ⟨1615718988149594369395717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154291984199459159194289 1615718988149594369395717)
                ·
                  refine ⟨302947310278048944261697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615718988149594369395717 302947310278048944261697)
                  ·
                    rfl

theorem cell22_2654945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_2654945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654945 prefixEnd_2654945 := by exact prefixLift 2654945
  have htrace : WordTrace (prefixWord ++ tailWord_2654945) baseStart_2654945 baseEnd_2654945 := by
    simpa [prefixWord, tailWord_2654945, baseEnd_2654945] using wordTrace_append hprefix tailTrace_2654945
  have hstable : (prefixWord ++ tailWord_2654945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654945).length < 2 ^ (prefixWord ++ tailWord_2654945).sum := by decide
  have hdescent : baseEnd_2654945 < baseStart_2654945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654954 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2654954 : Nat := 118140960795 + 2654954 * 2 ^ 59
def prefixEnd_2654954 : Nat := 4983230072969 + 3 ^ 40 * 2654954 * 2
def baseEnd_2654954 : Nat := 908845011718073809310063

theorem tailTrace_2654954 : CollatzResearch.WordTrace tailWord_2654954 prefixEnd_2654954 908845011718073809310063 := by
  unfold tailWord_2654954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208531905890640722224979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64556085082375041925933277 24208531905890640722224979)
  ·
    refine ⟨36312797858835961083337469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24208531905890640722224979 36312797858835961083337469)
    ·
      refine ⟨13617299197063485406251551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36312797858835961083337469 13617299197063485406251551)
      ·
        refine ⟨20425948795595228109377327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13617299197063485406251551 20425948795595228109377327)
        ·
          refine ⟨30638923193392842164065991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20425948795595228109377327 30638923193392842164065991)
          ·
            refine ⟨45958384790089263246098987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30638923193392842164065991 45958384790089263246098987)
            ·
              refine ⟨68937577185133894869148481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45958384790089263246098987 68937577185133894869148481)
              ·
                refine ⟨51703182888850421151861361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68937577185133894869148481 51703182888850421151861361)
                ·
                  refine ⟨38777387166637815863896021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51703182888850421151861361 38777387166637815863896021)
                  ·
                    refine ⟨908845011718073809310063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38777387166637815863896021 908845011718073809310063)
                    ·
                      rfl

theorem cell22_2654954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2654954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654954 prefixEnd_2654954 := by exact prefixLift 2654954
  have htrace : WordTrace (prefixWord ++ tailWord_2654954) baseStart_2654954 baseEnd_2654954 := by
    simpa [prefixWord, tailWord_2654954, baseEnd_2654954] using wordTrace_append hprefix tailTrace_2654954
  have hstable : (prefixWord ++ tailWord_2654954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654954).length < 2 ^ (prefixWord ++ tailWord_2654954).sum := by decide
  have hdescent : baseEnd_2654954 < baseStart_2654954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2654994 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_2654994 : Nat := 118140960795 + 2654994 * 2 ^ 59
def prefixEnd_2654994 : Nat := 4983230072969 + 3 ^ 40 * 2654994 * 2
def baseEnd_2654994 : Nat := 908858704535527038309941

theorem tailTrace_2654994 : CollatzResearch.WordTrace tailWord_2654994 prefixEnd_2654994 908858704535527038309941 := by
  unfold tailWord_2654994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208896635854412430089009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64557057695611766480237357 24208896635854412430089009)
  ·
    refine ⟨18156672476890809322566757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24208896635854412430089009 18156672476890809322566757)
    ·
      refine ⟨3404376089417026747981267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18156672476890809322566757 3404376089417026747981267)
      ·
        refine ⟨5106564134125540121971901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404376089417026747981267 5106564134125540121971901)
        ·
          refine ⟨1914961550297077545739463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5106564134125540121971901 1914961550297077545739463)
          ·
            refine ⟨2872442325445616318609195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914961550297077545739463 2872442325445616318609195)
            ·
              refine ⟨4308663488168424477913793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872442325445616318609195 4308663488168424477913793)
              ·
                refine ⟨3231497616126318358435345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308663488168424477913793 3231497616126318358435345)
                ·
                  refine ⟨2423623212094738768826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231497616126318358435345 2423623212094738768826509)
                  ·
                    refine ⟨908858704535527038309941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423623212094738768826509 908858704535527038309941)
                    ·
                      rfl

theorem cell22_2654994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_2654994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2654994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2654994 prefixEnd_2654994 := by exact prefixLift 2654994
  have htrace : WordTrace (prefixWord ++ tailWord_2654994) baseStart_2654994 baseEnd_2654994 := by
    simpa [prefixWord, tailWord_2654994, baseEnd_2654994] using wordTrace_append hprefix tailTrace_2654994
  have hstable : (prefixWord ++ tailWord_2654994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2654994).length < 2 ^ (prefixWord ++ tailWord_2654994).sum := by decide
  have hdescent : baseEnd_2654994 < baseStart_2654994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2654994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655016 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2655016 : Nat := 118140960795 + 2655016 * 2 ^ 59
def prefixEnd_2655016 : Nat := 4983230072969 + 3 ^ 40 * 2655016 * 2
def baseEnd_2655016 : Nat := 908866235585126314259873

theorem tailTrace_2655016 : CollatzResearch.WordTrace tailWord_2655016 prefixEnd_2655016 908866235585126314259873 := by
  unfold tailWord_2655016
  simp only [CollatzResearch.WordTrace]
  refine ⟨48418194474668973738828451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64557592632891964985104601 48418194474668973738828451)
  ·
    refine ⟨72627291712003460608242677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48418194474668973738828451 72627291712003460608242677)
    ·
      refine ⟨6808808598000324432022751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72627291712003460608242677 6808808598000324432022751)
      ·
        refine ⟨10213212897000486648034127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6808808598000324432022751 10213212897000486648034127)
        ·
          refine ⟨15319819345500729972051191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213212897000486648034127 15319819345500729972051191)
          ·
            refine ⟨22979729018251094958076787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15319819345500729972051191 22979729018251094958076787)
            ·
              refine ⟨34469593527376642437115181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22979729018251094958076787 34469593527376642437115181)
              ·
                refine ⟨12926097572766240913918193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34469593527376642437115181 12926097572766240913918193)
                ·
                  refine ⟨9694573179574680685438645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12926097572766240913918193 9694573179574680685438645)
                  ·
                    refine ⟨908866235585126314259873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9694573179574680685438645 908866235585126314259873)
                    ·
                      rfl

theorem cell22_2655016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2655016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655016 prefixEnd_2655016 := by exact prefixLift 2655016
  have htrace : WordTrace (prefixWord ++ tailWord_2655016) baseStart_2655016 baseEnd_2655016 := by
    simpa [prefixWord, tailWord_2655016, baseEnd_2655016] using wordTrace_append hprefix tailTrace_2655016
  have hstable : (prefixWord ++ tailWord_2655016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655016).length < 2 ^ (prefixWord ++ tailWord_2655016).sum := by decide
  have hdescent : baseEnd_2655016 < baseStart_2655016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655063 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 6]
def baseStart_2655063 : Nat := 118140960795 + 2655063 * 2 ^ 59
def prefixEnd_2655063 : Nat := 4983230072969 + 3 ^ 40 * 2655063 * 2
def baseEnd_2655063 : Nat := 302960774881877952778243

theorem tailTrace_2655063 : CollatzResearch.WordTrace tailWord_2655063 prefixEnd_2655063 302960774881877952778243 := by
  unfold tailWord_2655063
  simp only [CollatzResearch.WordTrace]
  refine ⟨96838103180167674504617843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64558735453445116336411895 96838103180167674504617843)
  ·
    refine ⟨145257154770251511756926765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96838103180167674504617843 145257154770251511756926765)
    ·
      refine ⟨54471433038844316908847537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145257154770251511756926765 54471433038844316908847537)
      ·
        refine ⟨40853574779133237681635653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54471433038844316908847537 40853574779133237681635653)
        ·
          refine ⟨7660045271087482065306685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40853574779133237681635653 7660045271087482065306685)
          ·
            refine ⟨2872516976657805774490007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7660045271087482065306685 2872516976657805774490007)
            ·
              refine ⟨4308775464986708661735011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872516976657805774490007 4308775464986708661735011)
              ·
                refine ⟨6463163197480062992602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308775464986708661735011 6463163197480062992602517)
                ·
                  refine ⟨302960774881877952778243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6463163197480062992602517 302960774881877952778243)
                  ·
                    rfl

theorem cell22_2655063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].length) (baseStart_2655063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655063 prefixEnd_2655063 := by exact prefixLift 2655063
  have htrace : WordTrace (prefixWord ++ tailWord_2655063) baseStart_2655063 baseEnd_2655063 := by
    simpa [prefixWord, tailWord_2655063, baseEnd_2655063] using wordTrace_append hprefix tailTrace_2655063
  have hstable : (prefixWord ++ tailWord_2655063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655063).length < 2 ^ (prefixWord ++ tailWord_2655063).sum := by decide
  have hdescent : baseEnd_2655063 < baseStart_2655063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655093 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2655093 : Nat := 118140960795 + 2655093 * 2 ^ 59
def prefixEnd_2655093 : Nat := 4983230072969 + 3 ^ 40 * 2655093 * 2
def baseEnd_2655093 : Nat := 908892594258723780084637

theorem tailTrace_2655093 : CollatzResearch.WordTrace tailWord_2655093 prefixEnd_2655093 908892594258723780084637 := by
  unfold tailWord_2655093
  simp only [CollatzResearch.WordTrace]
  refine ⟨96839197370058989628209933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64559464913372659752139955 96839197370058989628209933)
  ·
    refine ⟨36314699013772121110578725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96839197370058989628209933 36314699013772121110578725)
    ·
      refine ⟨6809006065082272708233511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36314699013772121110578725 6809006065082272708233511)
      ·
        refine ⟨10213509097623409062350267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809006065082272708233511 10213509097623409062350267)
        ·
          refine ⟨15320263646435113593525401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213509097623409062350267 15320263646435113593525401)
          ·
            refine ⟨11490197734826335195144051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15320263646435113593525401 11490197734826335195144051)
            ·
              refine ⟨17235296602239502792716077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490197734826335195144051 17235296602239502792716077)
              ·
                refine ⟨6463236225839813547268529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17235296602239502792716077 6463236225839813547268529)
                ·
                  refine ⟨4847427169379860160451397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6463236225839813547268529 4847427169379860160451397)
                  ·
                    refine ⟨908892594258723780084637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847427169379860160451397 908892594258723780084637)
                    ·
                      rfl

theorem cell22_2655093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2655093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655093 prefixEnd_2655093 := by exact prefixLift 2655093
  have htrace : WordTrace (prefixWord ++ tailWord_2655093) baseStart_2655093 baseEnd_2655093 := by
    simpa [prefixWord, tailWord_2655093, baseEnd_2655093] using wordTrace_append hprefix tailTrace_2655093
  have hstable : (prefixWord ++ tailWord_2655093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655093).length < 2 ^ (prefixWord ++ tailWord_2655093).sum := by decide
  have hdescent : baseEnd_2655093 < baseStart_2655093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655157 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2655157 : Nat := 118140960795 + 2655157 * 2 ^ 59
def prefixEnd_2655157 : Nat := 4983230072969 + 3 ^ 40 * 2655157 * 2
def baseEnd_2655157 : Nat := 908914502766648946484441

theorem tailTrace_2655157 : CollatzResearch.WordTrace tailWord_2655157 prefixEnd_2655157 908914502766648946484441 := by
  unfold tailWord_2655157
  simp only [CollatzResearch.WordTrace]
  refine ⟨96841531641827128558539725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64561021094551419039026483 96841531641827128558539725)
  ·
    refine ⟨36315574365685173209452397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96841531641827128558539725 36315574365685173209452397)
    ·
      refine ⟨13618340387131939953544649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36315574365685173209452397 13618340387131939953544649)
      ·
        refine ⟨10213755290348954965158487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13618340387131939953544649 10213755290348954965158487)
        ·
          refine ⟨15320632935523432447737731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213755290348954965158487 15320632935523432447737731)
          ·
            refine ⟨22980949403285148671606597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15320632935523432447737731 22980949403285148671606597)
            ·
              refine ⟨4308928013115965375926237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22980949403285148671606597 4308928013115965375926237)
              ·
                refine ⟨1615848004918487015972339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4308928013115965375926237 1615848004918487015972339)
                ·
                  refine ⟨2423772007377730523958509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615848004918487015972339 2423772007377730523958509)
                  ·
                    refine ⟨908914502766648946484441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423772007377730523958509 908914502766648946484441)
                    ·
                      rfl

theorem cell22_2655157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2655157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655157 prefixEnd_2655157 := by exact prefixLift 2655157
  have htrace : WordTrace (prefixWord ++ tailWord_2655157) baseStart_2655157 baseEnd_2655157 := by
    simpa [prefixWord, tailWord_2655157, baseEnd_2655157] using wordTrace_append hprefix tailTrace_2655157
  have hstable : (prefixWord ++ tailWord_2655157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655157).length < 2 ^ (prefixWord ++ tailWord_2655157).sum := by decide
  have hdescent : baseEnd_2655157 < baseStart_2655157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655215 : List Nat := [1, 1, 2, 1, 4, 3, 3, 3, 4]
def baseStart_2655215 : Nat := 118140960795 + 2655215 * 2 ^ 59
def prefixEnd_2655215 : Nat := 4983230072969 + 3 ^ 40 * 2655215 * 2
def baseEnd_2655215 : Nat := 302978119117318709511421

theorem tailTrace_2655215 : CollatzResearch.WordTrace tailWord_2655215 prefixEnd_2655215 302978119117318709511421 := by
  unfold tailWord_2655215
  simp only [CollatzResearch.WordTrace]
  refine ⟨96843647075617004464151099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64562431383744669642767399 96843647075617004464151099)
  ·
    refine ⟨145265470613425506696226649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96843647075617004464151099 145265470613425506696226649)
    ·
      refine ⟨108949102960069130022169987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145265470613425506696226649 108949102960069130022169987)
      ·
        refine ⟨163423654440103695033254981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108949102960069130022169987 163423654440103695033254981)
        ·
          refine ⟨30641935207519442818735309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163423654440103695033254981 30641935207519442818735309)
          ·
            refine ⟨11490725702819791057025741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30641935207519442818735309 11490725702819791057025741)
            ·
              refine ⟨4309022138557421646384653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11490725702819791057025741 4309022138557421646384653)
              ·
                refine ⟨1615883301959033117394245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4309022138557421646384653 1615883301959033117394245)
                ·
                  refine ⟨302978119117318709511421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615883301959033117394245 302978119117318709511421)
                  ·
                    rfl

theorem cell22_2655215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 4].length) (baseStart_2655215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655215 prefixEnd_2655215 := by exact prefixLift 2655215
  have htrace : WordTrace (prefixWord ++ tailWord_2655215) baseStart_2655215 baseEnd_2655215 := by
    simpa [prefixWord, tailWord_2655215, baseEnd_2655215] using wordTrace_append hprefix tailTrace_2655215
  have hstable : (prefixWord ++ tailWord_2655215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655215).length < 2 ^ (prefixWord ++ tailWord_2655215).sum := by decide
  have hdescent : baseEnd_2655215 < baseStart_2655215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655228 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2655228 : Nat := 118140960795 + 2655228 * 2 ^ 59
def prefixEnd_2655228 : Nat := 4983230072969 + 3 ^ 40 * 2655228 * 2
def baseEnd_2655228 : Nat := 908938807517628427959223

theorem tailTrace_2655228 : CollatzResearch.WordTrace tailWord_2655228 prefixEnd_2655228 908938807517628427959223 := by
  unfold tailWord_2655228
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422060612284953842187169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64562747483046605122916225 48422060612284953842187169)
  ·
    refine ⟨36316545459213715381640377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48422060612284953842187169 36316545459213715381640377)
    ·
      refine ⟨27237409094410286536230283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36316545459213715381640377 27237409094410286536230283)
      ·
        refine ⟨40856113641615429804345425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27237409094410286536230283 40856113641615429804345425)
        ·
          refine ⟨30642085231211572353259069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40856113641615429804345425 30642085231211572353259069)
          ·
            refine ⟨11490781961704339632472151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30642085231211572353259069 11490781961704339632472151)
            ·
              refine ⟨17236172942556509448708227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490781961704339632472151 17236172942556509448708227)
              ·
                refine ⟨25854259413834764173062341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17236172942556509448708227 25854259413834764173062341)
                ·
                  refine ⟨4847673640094018282449189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25854259413834764173062341 4847673640094018282449189)
                  ·
                    refine ⟨908938807517628427959223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847673640094018282449189 908938807517628427959223)
                    ·
                      rfl

theorem cell22_2655228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2655228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655228 prefixEnd_2655228 := by exact prefixLift 2655228
  have htrace : WordTrace (prefixWord ++ tailWord_2655228) baseStart_2655228 baseEnd_2655228 := by
    simpa [prefixWord, tailWord_2655228, baseEnd_2655228] using wordTrace_append hprefix tailTrace_2655228
  have hstable : (prefixWord ++ tailWord_2655228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655228).length < 2 ^ (prefixWord ++ tailWord_2655228).sum := by decide
  have hdescent : baseEnd_2655228 < baseStart_2655228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655243 : List Nat := [1, 1, 1, 1, 6, 3, 2, 7]
def baseStart_2655243 : Nat := 118140960795 + 2655243 * 2 ^ 59
def prefixEnd_2655243 : Nat := 4983230072969 + 3 ^ 40 * 2655243 * 2
def baseEnd_2655243 : Nat := 100993771369352598759353

theorem tailTrace_2655243 : CollatzResearch.WordTrace tailWord_2655243 prefixEnd_2655243 100993771369352598759353 := by
  unfold tailWord_2655243
  simp only [CollatzResearch.WordTrace]
  refine ⟨96844668319515565246170383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64563112213010376830780255 96844668319515565246170383)
  ·
    refine ⟨145267002479273347869255575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96844668319515565246170383 145267002479273347869255575)
    ·
      refine ⟨217900503718910021803883363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145267002479273347869255575 217900503718910021803883363)
      ·
        refine ⟨326850755578365032705825045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217900503718910021803883363 326850755578365032705825045)
        ·
          refine ⟨15321129167735860908085549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326850755578365032705825045 15321129167735860908085549)
          ·
            refine ⟨5745423437900947840532081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15321129167735860908085549 5745423437900947840532081)
            ·
              refine ⟨4309067578425710880399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745423437900947840532081 4309067578425710880399061)
              ·
                refine ⟨100993771369352598759353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4309067578425710880399061 100993771369352598759353)
                ·
                  rfl

theorem cell22_2655243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 7].length) (baseStart_2655243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655243 prefixEnd_2655243 := by exact prefixLift 2655243
  have htrace : WordTrace (prefixWord ++ tailWord_2655243) baseStart_2655243 baseEnd_2655243 := by
    simpa [prefixWord, tailWord_2655243, baseEnd_2655243] using wordTrace_append hprefix tailTrace_2655243
  have hstable : (prefixWord ++ tailWord_2655243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655243).length < 2 ^ (prefixWord ++ tailWord_2655243).sum := by decide
  have hdescent : baseEnd_2655243 < baseStart_2655243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655303 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2655303 : Nat := 118140960795 + 2655303 * 2 ^ 59
def prefixEnd_2655303 : Nat := 4983230072969 + 3 ^ 40 * 2655303 * 2
def baseEnd_2655303 : Nat := 908964481550353232333993

theorem tailTrace_2655303 : CollatzResearch.WordTrace tailWord_2655303 prefixEnd_2655303 908964481550353232333993 := by
  unfold tailWord_2655303
  simp only [CollatzResearch.WordTrace]
  refine ⟨96846856699298195493354563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64564571132865463662236375 96846856699298195493354563)
  ·
    refine ⟨145270285048947293240031845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96846856699298195493354563 145270285048947293240031845)
    ·
      refine ⟨27238178446677617482505971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145270285048947293240031845 27238178446677617482505971)
      ·
        refine ⟨40857267670016426223758957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27238178446677617482505971 40857267670016426223758957)
        ·
          refine ⟨15321475376256159833909609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40857267670016426223758957 15321475376256159833909609)
          ·
            refine ⟨11491106532192119875432207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15321475376256159833909609 11491106532192119875432207)
            ·
              refine ⟨17236659798288179813148311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491106532192119875432207 17236659798288179813148311)
              ·
                refine ⟨25854989697432269719722467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17236659798288179813148311 25854989697432269719722467)
                ·
                  refine ⟨38782484546148404579583701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25854989697432269719722467 38782484546148404579583701)
                  ·
                    refine ⟨908964481550353232333993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38782484546148404579583701 908964481550353232333993)
                    ·
                      rfl

theorem cell22_2655303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2655303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655303 prefixEnd_2655303 := by exact prefixLift 2655303
  have htrace : WordTrace (prefixWord ++ tailWord_2655303) baseStart_2655303 baseEnd_2655303 := by
    simpa [prefixWord, tailWord_2655303, baseEnd_2655303] using wordTrace_append hprefix tailTrace_2655303
  have hstable : (prefixWord ++ tailWord_2655303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655303).length < 2 ^ (prefixWord ++ tailWord_2655303).sum := by decide
  have hdescent : baseEnd_2655303 < baseStart_2655303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655333 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 8]
def baseStart_2655333 : Nat := 118140960795 + 2655333 * 2 ^ 59
def prefixEnd_2655333 : Nat := 4983230072969 + 3 ^ 40 * 2655333 * 2
def baseEnd_2655333 : Nat := 302991583721147718027967

theorem tailTrace_2655333 : CollatzResearch.WordTrace tailWord_2655333 prefixEnd_2655333 302991583721147718027967 := by
  unfold tailWord_2655333
  simp only [CollatzResearch.WordTrace]
  refine ⟨96847950889189510616946653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64565300592793007077964435 96847950889189510616946653)
  ·
    refine ⟨36317981583446066481354995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96847950889189510616946653 36317981583446066481354995)
    ·
      refine ⟨54476972375169099722032493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36317981583446066481354995 54476972375169099722032493)
      ·
        refine ⟨20428864640688412395762185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54476972375169099722032493 20428864640688412395762185)
        ·
          refine ⟨15321648480516309296821639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20428864640688412395762185 15321648480516309296821639)
          ·
            refine ⟨22982472720774463945232459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15321648480516309296821639 22982472720774463945232459)
            ·
              refine ⟨34473709081161695917848689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22982472720774463945232459 34473709081161695917848689)
              ·
                refine ⟨25855281810871271938386517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34473709081161695917848689 25855281810871271938386517)
                ·
                  refine ⟨302991583721147718027967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25855281810871271938386517 302991583721147718027967)
                  ·
                    rfl

theorem cell22_2655333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_2655333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655333 prefixEnd_2655333 := by exact prefixLift 2655333
  have htrace : WordTrace (prefixWord ++ tailWord_2655333) baseStart_2655333 baseEnd_2655333 := by
    simpa [prefixWord, tailWord_2655333, baseEnd_2655333] using wordTrace_append hprefix tailTrace_2655333
  have hstable : (prefixWord ++ tailWord_2655333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655333).length < 2 ^ (prefixWord ++ tailWord_2655333).sum := by decide
  have hdescent : baseEnd_2655333 < baseStart_2655333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655363 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_2655363 : Nat := 118140960795 + 2655363 * 2 ^ 59
def prefixEnd_2655363 : Nat := 4983230072969 + 3 ^ 40 * 2655363 * 2
def baseEnd_2655363 : Nat := 908985020776533075833809

theorem tailTrace_2655363 : CollatzResearch.WordTrace tailWord_2655363 prefixEnd_2655363 908985020776533075833809 := by
  unfold tailWord_2655363
  simp only [CollatzResearch.WordTrace]
  refine ⟨96849045079080825740538743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64566030052720550493692495 96849045079080825740538743)
  ·
    refine ⟨145273567618621238610808115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96849045079080825740538743 145273567618621238610808115)
    ·
      refine ⟨217910351427931857916212173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145273567618621238610808115 217910351427931857916212173)
      ·
        refine ⟨81716381785474446718579565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217910351427931857916212173 81716381785474446718579565)
        ·
          refine ⟨30643643169552917519467337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81716381785474446718579565 30643643169552917519467337)
          ·
            refine ⟨22982732377164688139600503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30643643169552917519467337 22982732377164688139600503)
            ·
              refine ⟨34474098565747032209400755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22982732377164688139600503 34474098565747032209400755)
              ·
                refine ⟨51711147848620548314101133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34474098565747032209400755 51711147848620548314101133)
                ·
                  refine ⟨19391680443232705617787925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51711147848620548314101133 19391680443232705617787925)
                  ·
                    refine ⟨908985020776533075833809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19391680443232705617787925 908985020776533075833809)
                    ·
                      rfl

theorem cell22_2655363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_2655363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655363 prefixEnd_2655363 := by exact prefixLift 2655363
  have htrace : WordTrace (prefixWord ++ tailWord_2655363) baseStart_2655363 baseEnd_2655363 := by
    simpa [prefixWord, tailWord_2655363, baseEnd_2655363] using wordTrace_append hprefix tailTrace_2655363
  have hstable : (prefixWord ++ tailWord_2655363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655363).length < 2 ^ (prefixWord ++ tailWord_2655363).sum := by decide
  have hdescent : baseEnd_2655363 < baseStart_2655363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655384 : List Nat := [2, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_2655384 : Nat := 118140960795 + 2655384 * 2 ^ 59
def prefixEnd_2655384 : Nat := 4983230072969 + 3 ^ 40 * 2655384 * 2
def baseEnd_2655384 : Nat := 302997403168565340352915

theorem tailTrace_2655384 : CollatzResearch.WordTrace tailWord_2655384 prefixEnd_2655384 302997403168565340352915 := by
  unfold tailWord_2655384
  simp only [CollatzResearch.WordTrace]
  refine ⟨48424905506002373163526603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64566540674669830884702137 48424905506002373163526603)
  ·
    refine ⟨72637358259003559745289905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48424905506002373163526603 72637358259003559745289905)
    ·
      refine ⟨54478018694252669808967429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72637358259003559745289905 54478018694252669808967429)
      ·
        refine ⟨10214628505172375589181393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54478018694252669808967429 10214628505172375589181393)
        ·
          refine ⟨7660971378879281691886045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10214628505172375589181393 7660971378879281691886045)
          ·
            refine ⟨2872864267079730634457267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7660971378879281691886045 2872864267079730634457267)
            ·
              refine ⟨4309296400619595951685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872864267079730634457267 4309296400619595951685901)
              ·
                refine ⟨1615986150232348481882213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4309296400619595951685901 1615986150232348481882213)
                ·
                  refine ⟨302997403168565340352915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615986150232348481882213 302997403168565340352915)
                  ·
                    rfl

theorem cell22_2655384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_2655384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655384 prefixEnd_2655384 := by exact prefixLift 2655384
  have htrace : WordTrace (prefixWord ++ tailWord_2655384) baseStart_2655384 baseEnd_2655384 := by
    simpa [prefixWord, tailWord_2655384, baseEnd_2655384] using wordTrace_append hprefix tailTrace_2655384
  have hstable : (prefixWord ++ tailWord_2655384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655384).length < 2 ^ (prefixWord ++ tailWord_2655384).sum := by decide
  have hdescent : baseEnd_2655384 < baseStart_2655384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655408 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_2655408 : Nat := 118140960795 + 2655408 * 2 ^ 59
def prefixEnd_2655408 : Nat := 4983230072969 + 3 ^ 40 * 2655408 * 2
def baseEnd_2655408 : Nat := 909000425196167958458671

theorem tailTrace_2655408 : CollatzResearch.WordTrace tailWord_2655408 prefixEnd_2655408 909000425196167958458671 := by
  unfold tailWord_2655408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48425343181958899212963439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64567124242611865617284585 48425343181958899212963439)
  ·
    refine ⟨72638014772938348819445159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48425343181958899212963439 72638014772938348819445159)
    ·
      refine ⟨108957022159407523229167739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72638014772938348819445159 108957022159407523229167739)
      ·
        refine ⟨163435533239111284843751609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108957022159407523229167739 163435533239111284843751609)
        ·
          refine ⟨122576649929333463632813707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163435533239111284843751609 122576649929333463632813707)
          ·
            refine ⟨183864974894000195449220561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122576649929333463632813707 183864974894000195449220561)
            ·
              refine ⟨137898731170500146586915421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183864974894000195449220561 137898731170500146586915421)
              ·
                refine ⟨51712024188937554970093283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137898731170500146586915421 51712024188937554970093283)
                ·
                  refine ⟨77568036283406332455139925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51712024188937554970093283 77568036283406332455139925)
                  ·
                    refine ⟨909000425196167958458671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77568036283406332455139925 909000425196167958458671)
                    ·
                      rfl

theorem cell22_2655408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_2655408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655408 prefixEnd_2655408 := by exact prefixLift 2655408
  have htrace : WordTrace (prefixWord ++ tailWord_2655408) baseStart_2655408 baseEnd_2655408 := by
    simpa [prefixWord, tailWord_2655408, baseEnd_2655408] using wordTrace_append hprefix tailTrace_2655408
  have hstable : (prefixWord ++ tailWord_2655408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655408).length < 2 ^ (prefixWord ++ tailWord_2655408).sum := by decide
  have hdescent : baseEnd_2655408 < baseStart_2655408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655457 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 5]
def baseStart_2655457 : Nat := 118140960795 + 2655457 * 2 ^ 59
def prefixEnd_2655457 : Nat := 4983230072969 + 3 ^ 40 * 2655457 * 2
def baseEnd_2655457 : Nat := 303005732965849387994507

theorem tailTrace_2655457 : CollatzResearch.WordTrace tailWord_2655457 prefixEnd_2655457 303005732965849387994507 := by
  unfold tailWord_2655457
  simp only [CollatzResearch.WordTrace]
  refine ⟨96852473540740279794460625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64568315693826853196307083 96852473540740279794460625)
  ·
    refine ⟨72639355155555209845845469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96852473540740279794460625 72639355155555209845845469)
    ·
      refine ⟨27239758183333203692192051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72639355155555209845845469 27239758183333203692192051)
      ·
        refine ⟨40859637274999805538288077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27239758183333203692192051 40859637274999805538288077)
        ·
          refine ⟨15322363978124927076858029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40859637274999805538288077 15322363978124927076858029)
          ·
            refine ⟨5745886491796847653821761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15322363978124927076858029 5745886491796847653821761)
            ·
              refine ⟨4309414868847635740366321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745886491796847653821761 4309414868847635740366321)
              ·
                refine ⟨3232061151635726805274741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309414868847635740366321 3232061151635726805274741)
                ·
                  refine ⟨303005732965849387994507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232061151635726805274741 303005732965849387994507)
                  ·
                    rfl

theorem cell22_2655457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_2655457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655457 prefixEnd_2655457 := by exact prefixLift 2655457
  have htrace : WordTrace (prefixWord ++ tailWord_2655457) baseStart_2655457 baseEnd_2655457 := by
    simpa [prefixWord, tailWord_2655457, baseEnd_2655457] using wordTrace_append hprefix tailTrace_2655457
  have hstable : (prefixWord ++ tailWord_2655457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655457).length < 2 ^ (prefixWord ++ tailWord_2655457).sum := by decide
  have hdescent : baseEnd_2655457 < baseStart_2655457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655461 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_2655461 : Nat := 118140960795 + 2655461 * 2 ^ 59
def prefixEnd_2655461 : Nat := 4983230072969 + 3 ^ 40 * 2655461 * 2
def baseEnd_2655461 : Nat := 909018568179293486883509

theorem tailTrace_2655461 : CollatzResearch.WordTrace tailWord_2655461 prefixEnd_2655461 909018568179293486883509 := by
  unfold tailWord_2655461
  simp only [CollatzResearch.WordTrace]
  refine ⟨96852619432725788477606237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64568412955150525651737491 96852619432725788477606237)
  ·
    refine ⟨36319732287272170679102339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96852619432725788477606237 36319732287272170679102339)
    ·
      refine ⟨54479598430908256018653509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36319732287272170679102339 54479598430908256018653509)
      ·
        refine ⟨10214924705795298003497533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54479598430908256018653509 10214924705795298003497533)
        ·
          refine ⟨3830596764673236751311575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10214924705795298003497533 3830596764673236751311575)
          ·
            refine ⟨5745895147009855126967363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830596764673236751311575 5745895147009855126967363)
            ·
              refine ⟨8618842720514782690451045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745895147009855126967363 8618842720514782690451045)
              ·
                refine ⟨1616033010096521754459571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8618842720514782690451045 1616033010096521754459571)
                ·
                  refine ⟨2424049515144782631689357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616033010096521754459571 2424049515144782631689357)
                  ·
                    refine ⟨909018568179293486883509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424049515144782631689357 909018568179293486883509)
                    ·
                      rfl

theorem cell22_2655461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_2655461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655461 prefixEnd_2655461 := by exact prefixLift 2655461
  have htrace : WordTrace (prefixWord ++ tailWord_2655461) baseStart_2655461 baseEnd_2655461 := by
    simpa [prefixWord, tailWord_2655461, baseEnd_2655461] using wordTrace_append hprefix tailTrace_2655461
  have hstable : (prefixWord ++ tailWord_2655461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655461).length < 2 ^ (prefixWord ++ tailWord_2655461).sum := by decide
  have hdescent : baseEnd_2655461 < baseStart_2655461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655515 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_2655515 : Nat := 118140960795 + 2655515 * 2 ^ 59
def prefixEnd_2655515 : Nat := 4983230072969 + 3 ^ 40 * 2655515 * 2
def baseEnd_2655515 : Nat := 909037053482855346033343

theorem tailTrace_2655515 : CollatzResearch.WordTrace tailWord_2655515 prefixEnd_2655515 909037053482855346033343 := by
  unfold tailWord_2655515
  simp only [CollatzResearch.WordTrace]
  refine ⟨96854588974530155700071999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64569725983020103800047999 96854588974530155700071999)
  ·
    refine ⟨145281883461795233550107999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96854588974530155700071999 145281883461795233550107999)
    ·
      refine ⟨217922825192692850325161999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145281883461795233550107999 217922825192692850325161999)
      ·
        refine ⟨326884237789039275487742999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217922825192692850325161999 326884237789039275487742999)
        ·
          refine ⟨490326356683558913231614499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326884237789039275487742999 490326356683558913231614499)
          ·
            refine ⟨735489535025338369847421749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490326356683558913231614499 735489535025338369847421749)
            ·
              refine ⟨68952143908625472173195789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 735489535025338369847421749 68952143908625472173195789)
              ·
                refine ⟨25857053965734552064948421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68952143908625472173195789 25857053965734552064948421)
                ·
                  refine ⟨4848197618575228512177829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25857053965734552064948421 4848197618575228512177829)
                  ·
                    refine ⟨909037053482855346033343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848197618575228512177829 909037053482855346033343)
                    ·
                      rfl

theorem cell22_2655515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_2655515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655515 prefixEnd_2655515 := by exact prefixLift 2655515
  have htrace : WordTrace (prefixWord ++ tailWord_2655515) baseStart_2655515 baseEnd_2655515 := by
    simpa [prefixWord, tailWord_2655515, baseEnd_2655515] using wordTrace_append hprefix tailTrace_2655515
  have hstable : (prefixWord ++ tailWord_2655515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655515).length < 2 ^ (prefixWord ++ tailWord_2655515).sum := by decide
  have hdescent : baseEnd_2655515 < baseStart_2655515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655560 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2655560 : Nat := 118140960795 + 2655560 * 2 ^ 59
def prefixEnd_2655560 : Nat := 4983230072969 + 3 ^ 40 * 2655560 * 2
def baseEnd_2655560 : Nat := 909052457902490228658205

theorem tailTrace_2655560 : CollatzResearch.WordTrace tailWord_2655560 prefixEnd_2655560 909052457902490228658205 := by
  unfold tailWord_2655560
  simp only [CollatzResearch.WordTrace]
  refine ⟨48428115129683564192730067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64570820172911418923640089 48428115129683564192730067)
  ·
    refine ⟨72642172694525346289095101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48428115129683564192730067 72642172694525346289095101)
    ·
      refine ⟨27240814760447004858410663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72642172694525346289095101 27240814760447004858410663)
      ·
        refine ⟨40861222140670507287615995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27240814760447004858410663 40861222140670507287615995)
        ·
          refine ⟨61291833211005760931423993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861222140670507287615995 61291833211005760931423993)
          ·
            refine ⟨45968874908254320698567995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61291833211005760931423993 45968874908254320698567995)
            ·
              refine ⟨68953312362381481047851993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45968874908254320698567995 68953312362381481047851993)
              ·
                refine ⟨51714984271786110785888995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68953312362381481047851993 51714984271786110785888995)
                ·
                  refine ⟨77572476407679166178833493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51714984271786110785888995 77572476407679166178833493)
                  ·
                    refine ⟨909052457902490228658205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77572476407679166178833493 909052457902490228658205)
                    ·
                      rfl

theorem cell22_2655560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2655560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655560 prefixEnd_2655560 := by exact prefixLift 2655560
  have htrace : WordTrace (prefixWord ++ tailWord_2655560) baseStart_2655560 baseEnd_2655560 := by
    simpa [prefixWord, tailWord_2655560, baseEnd_2655560] using wordTrace_append hprefix tailTrace_2655560
  have hstable : (prefixWord ++ tailWord_2655560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655560).length < 2 ^ (prefixWord ++ tailWord_2655560).sum := by decide
  have hdescent : baseEnd_2655560 < baseStart_2655560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655562 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2655562 : Nat := 118140960795 + 2655562 * 2 ^ 59
def prefixEnd_2655562 : Nat := 4983230072969 + 3 ^ 40 * 2655562 * 2
def baseEnd_2655562 : Nat := 909053142543362890108199

theorem tailTrace_2655562 : CollatzResearch.WordTrace tailWord_2655562 prefixEnd_2655562 909053142543362890108199 := by
  unfold tailWord_2655562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214075801339970681758235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64570868803573255151355293 24214075801339970681758235)
  ·
    refine ⟨36321113702009956022637353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24214075801339970681758235 36321113702009956022637353)
    ·
      refine ⟨27240835276507467016978015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36321113702009956022637353 27240835276507467016978015)
      ·
        refine ⟨40861252914761200525467023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27240835276507467016978015 40861252914761200525467023)
        ·
          refine ⟨61291879372141800788200535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861252914761200525467023 61291879372141800788200535)
          ·
            refine ⟨91937819058212701182300803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61291879372141800788200535 91937819058212701182300803)
            ·
              refine ⟨137906728587319051773451205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91937819058212701182300803 137906728587319051773451205)
              ·
                refine ⟨25857511610122322207522101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137906728587319051773451205 25857511610122322207522101)
                ·
                  refine ⟨2424141713448967706955197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25857511610122322207522101 2424141713448967706955197)
                  ·
                    refine ⟨909053142543362890108199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424141713448967706955197 909053142543362890108199)
                    ·
                      rfl

theorem cell22_2655562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2655562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655562 prefixEnd_2655562 := by exact prefixLift 2655562
  have htrace : WordTrace (prefixWord ++ tailWord_2655562) baseStart_2655562 baseEnd_2655562 := by
    simpa [prefixWord, tailWord_2655562, baseEnd_2655562] using wordTrace_append hprefix tailTrace_2655562
  have hstable : (prefixWord ++ tailWord_2655562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655562).length < 2 ^ (prefixWord ++ tailWord_2655562).sum := by decide
  have hdescent : baseEnd_2655562 < baseStart_2655562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655669 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2655669 : Nat := 118140960795 + 2655669 * 2 ^ 59
def prefixEnd_2655669 : Nat := 4983230072969 + 3 ^ 40 * 2655669 * 2
def baseEnd_2655669 : Nat := 909089770830050277682871

theorem tailTrace_2655669 : CollatzResearch.WordTrace tailWord_2655669 prefixEnd_2655669 909089770830050277682871 := by
  unfold tailWord_2655669
  simp only [CollatzResearch.WordTrace]
  refine ⟨96860205815972240001178061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64573470543981493334118707 96860205815972240001178061)
  ·
    refine ⟨36322577180989590000441773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96860205815972240001178061 36322577180989590000441773)
    ·
      refine ⟨13620966442871096250165665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36322577180989590000441773 13620966442871096250165665)
      ·
        refine ⟨10215724832153322187624249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13620966442871096250165665 10215724832153322187624249)
        ·
          refine ⟨7661793624114991640718187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10215724832153322187624249 7661793624114991640718187)
          ·
            refine ⟨11492690436172487461077281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661793624114991640718187 11492690436172487461077281)
            ·
              refine ⟨8619517827129365595807961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11492690436172487461077281 8619517827129365595807961)
              ·
                refine ⟨6464638370347024196855971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8619517827129365595807961 6464638370347024196855971)
                ·
                  refine ⟨9696957555520536295283957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6464638370347024196855971 9696957555520536295283957)
                  ·
                    refine ⟨909089770830050277682871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9696957555520536295283957 909089770830050277682871)
                    ·
                      rfl

theorem cell22_2655669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2655669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655669 prefixEnd_2655669 := by exact prefixLift 2655669
  have htrace : WordTrace (prefixWord ++ tailWord_2655669) baseStart_2655669 baseEnd_2655669 := by
    simpa [prefixWord, tailWord_2655669, baseEnd_2655669] using wordTrace_append hprefix tailTrace_2655669
  have hstable : (prefixWord ++ tailWord_2655669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655669).length < 2 ^ (prefixWord ++ tailWord_2655669).sum := by decide
  have hdescent : baseEnd_2655669 < baseStart_2655669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655673 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_2655673 : Nat := 118140960795 + 2655673 * 2 ^ 59
def prefixEnd_2655673 : Nat := 4983230072969 + 3 ^ 40 * 2655673 * 2
def baseEnd_2655673 : Nat := 909091140111795600582859

theorem tailTrace_2655673 : CollatzResearch.WordTrace tailWord_2655673 prefixEnd_2655673 909091140111795600582859 := by
  unfold tailWord_2655673
  simp only [CollatzResearch.WordTrace]
  refine ⟨96860351707957748684323673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64573567805305165789549115 96860351707957748684323673)
  ·
    refine ⟨72645263780968311513242755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96860351707957748684323673 72645263780968311513242755)
    ·
      refine ⟨108967895671452467269864133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72645263780968311513242755 108967895671452467269864133)
      ·
        refine ⟨20431480438397337613099525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108967895671452467269864133 20431480438397337613099525)
        ·
          refine ⟨3830902582199500802456161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20431480438397337613099525 3830902582199500802456161)
          ·
            refine ⟨2873176936649625601842121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3830902582199500802456161 2873176936649625601842121)
            ·
              refine ⟨2154882702487219201381591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873176936649625601842121 2154882702487219201381591)
              ·
                refine ⟨3232324053730828802072387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154882702487219201381591 3232324053730828802072387)
                ·
                  refine ⟨4848486080596243203108581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232324053730828802072387 4848486080596243203108581)
                  ·
                    refine ⟨909091140111795600582859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848486080596243203108581 909091140111795600582859)
                    ·
                      rfl

theorem cell22_2655673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_2655673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655673 prefixEnd_2655673 := by exact prefixLift 2655673
  have htrace : WordTrace (prefixWord ++ tailWord_2655673) baseStart_2655673 baseEnd_2655673 := by
    simpa [prefixWord, tailWord_2655673, baseEnd_2655673] using wordTrace_append hprefix tailTrace_2655673
  have hstable : (prefixWord ++ tailWord_2655673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655673).length < 2 ^ (prefixWord ++ tailWord_2655673).sum := by decide
  have hdescent : baseEnd_2655673 < baseStart_2655673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655727 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 7]
def baseStart_2655727 : Nat := 118140960795 + 2655727 * 2 ^ 59
def prefixEnd_2655727 : Nat := 4983230072969 + 3 ^ 40 * 2655727 * 2
def baseEnd_2655727 : Nat := 303036541805119153244231

theorem tailTrace_2655727 : CollatzResearch.WordTrace tailWord_2655727 prefixEnd_2655727 303036541805119153244231 := by
  unfold tailWord_2655727
  simp only [CollatzResearch.WordTrace]
  refine ⟨96862321249762115906789435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574880833174743937859623 96862321249762115906789435)
  ·
    refine ⟨145293481874643173860184153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96862321249762115906789435 145293481874643173860184153)
    ·
      refine ⟨108970111405982380395138115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145293481874643173860184153 108970111405982380395138115)
      ·
        refine ⟨163455167108973570592707173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108970111405982380395138115 163455167108973570592707173)
        ·
          refine ⟨30647843832932544486132595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163455167108973570592707173 30647843832932544486132595)
          ·
            refine ⟨45971765749398816729198893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30647843832932544486132595 45971765749398816729198893)
            ·
              refine ⟨17239412156024556273449585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45971765749398816729198893 17239412156024556273449585)
              ·
                refine ⟨12929559117018417205087189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17239412156024556273449585 12929559117018417205087189)
                ·
                  refine ⟨303036541805119153244231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12929559117018417205087189 303036541805119153244231)
                  ·
                    rfl

theorem cell22_2655727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_2655727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655727 prefixEnd_2655727 := by exact prefixLift 2655727
  have htrace : WordTrace (prefixWord ++ tailWord_2655727) baseStart_2655727 baseEnd_2655727 := by
    simpa [prefixWord, tailWord_2655727, baseEnd_2655727] using wordTrace_append hprefix tailTrace_2655727
  have hstable : (prefixWord ++ tailWord_2655727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655727).length < 2 ^ (prefixWord ++ tailWord_2655727).sum := by decide
  have hdescent : baseEnd_2655727 < baseStart_2655727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655731 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 1, 3]
def baseStart_2655731 : Nat := 118140960795 + 2655731 * 2 ^ 59
def prefixEnd_2655731 : Nat := 4983230072969 + 3 ^ 40 * 2655731 * 2
def baseEnd_2655731 : Nat := 909110994697102782632681

theorem tailTrace_2655731 : CollatzResearch.WordTrace tailWord_2655731 prefixEnd_2655731 909110994697102782632681 := by
  unfold tailWord_2655731
  simp only [CollatzResearch.WordTrace]
  refine ⟨96862467141747624589935047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64574978094498416393290031 96862467141747624589935047)
  ·
    refine ⟨145293700712621436884902571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96862467141747624589935047 145293700712621436884902571)
    ·
      refine ⟨217940551068932155327353857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145293700712621436884902571 217940551068932155327353857)
      ·
        refine ⟨163455413301699116495515393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217940551068932155327353857 163455413301699116495515393)
        ·
          refine ⟨122591559976274337371636545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163455413301699116495515393 122591559976274337371636545)
          ·
            refine ⟨91943669982205753028727409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122591559976274337371636545 91943669982205753028727409)
            ·
              refine ⟨68957752486654314771545557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91943669982205753028727409 68957752486654314771545557)
              ·
                refine ⟨1616197323905960502458099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68957752486654314771545557 1616197323905960502458099)
                ·
                  refine ⟨2424295985858940753687149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616197323905960502458099 2424295985858940753687149)
                  ·
                    refine ⟨909110994697102782632681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424295985858940753687149 909110994697102782632681)
                    ·
                      rfl

theorem cell22_2655731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 3].length) (baseStart_2655731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655731 prefixEnd_2655731 := by exact prefixLift 2655731
  have htrace : WordTrace (prefixWord ++ tailWord_2655731) baseStart_2655731 baseEnd_2655731 := by
    simpa [prefixWord, tailWord_2655731, baseEnd_2655731] using wordTrace_append hprefix tailTrace_2655731
  have hstable : (prefixWord ++ tailWord_2655731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655731).length < 2 ^ (prefixWord ++ tailWord_2655731).sum := by decide
  have hdescent : baseEnd_2655731 < baseStart_2655731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655750 : List Nat := [6, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2655750 : Nat := 118140960795 + 2655750 * 2 ^ 59
def prefixEnd_2655750 : Nat := 4983230072969 + 3 ^ 40 * 2655750 * 2
def baseEnd_2655750 : Nat := 101013055420599229600847

theorem tailTrace_2655750 : CollatzResearch.WordTrace tailWord_2655750 prefixEnd_2655750 101013055420599229600847 := by
  unfold tailWord_2655750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026973754021212213589897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64575440085785860556584469 3026973754021212213589897)
  ·
    refine ⟨2270230315515909160192423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3026973754021212213589897 2270230315515909160192423)
    ·
      refine ⟨3405345473273863740288635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270230315515909160192423 3405345473273863740288635)
      ·
        refine ⟨5108018209910795610432953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405345473273863740288635 5108018209910795610432953)
        ·
          refine ⟨3831013657433096707824715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5108018209910795610432953 3831013657433096707824715)
          ·
            refine ⟨5746520486149645061737073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831013657433096707824715 5746520486149645061737073)
            ·
              refine ⟨4309890364612233796302805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5746520486149645061737073 4309890364612233796302805)
              ·
                refine ⟨101013055420599229600847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4309890364612233796302805 101013055420599229600847)
                ·
                  rfl

theorem cell22_2655750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2655750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655750 prefixEnd_2655750 := by exact prefixLift 2655750
  have htrace : WordTrace (prefixWord ++ tailWord_2655750) baseStart_2655750 baseEnd_2655750 := by
    simpa [prefixWord, tailWord_2655750, baseEnd_2655750] using wordTrace_append hprefix tailTrace_2655750
  have hstable : (prefixWord ++ tailWord_2655750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655750).length < 2 ^ (prefixWord ++ tailWord_2655750).sum := by decide
  have hdescent : baseEnd_2655750 < baseStart_2655750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655836 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2655836 : Nat := 118140960795 + 2655836 * 2 ^ 59
def prefixEnd_2655836 : Nat := 4983230072969 + 3 ^ 40 * 2655836 * 2
def baseEnd_2655836 : Nat := 909146938342917508757359

theorem tailTrace_2655836 : CollatzResearch.WordTrace tailWord_2655836 prefixEnd_2655836 909146938342917508757359 := by
  unfold tailWord_2655836
  simp only [CollatzResearch.WordTrace]
  refine ⟨48433148403183613761253681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64577531204244818348338241 48433148403183613761253681)
  ·
    refine ⟨36324861302387710320940261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48433148403183613761253681 36324861302387710320940261)
    ·
      refine ⟨6810911494197695685176299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36324861302387710320940261 6810911494197695685176299)
      ·
        refine ⟨10216367241296543527764449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6810911494197695685176299 10216367241296543527764449)
        ·
          refine ⟨7662275430972407645823337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10216367241296543527764449 7662275430972407645823337)
          ·
            refine ⟨5746706573229305734367503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7662275430972407645823337 5746706573229305734367503)
            ·
              refine ⟨8620059859843958601551255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746706573229305734367503 8620059859843958601551255)
              ·
                refine ⟨12930089789765937902326883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8620059859843958601551255 12930089789765937902326883)
                ·
                  refine ⟨19395134684648906853490325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12930089789765937902326883 19395134684648906853490325)
                  ·
                    refine ⟨909146938342917508757359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19395134684648906853490325 909146938342917508757359)
                    ·
                      rfl

theorem cell22_2655836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2655836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655836 prefixEnd_2655836 := by exact prefixLift 2655836
  have htrace : WordTrace (prefixWord ++ tailWord_2655836) baseStart_2655836 baseEnd_2655836 := by
    simpa [prefixWord, tailWord_2655836, baseEnd_2655836] using wordTrace_append hprefix tailTrace_2655836
  have hstable : (prefixWord ++ tailWord_2655836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655836).length < 2 ^ (prefixWord ++ tailWord_2655836).sum := by decide
  have hdescent : baseEnd_2655836 < baseStart_2655836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655917 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_2655917 : Nat := 118140960795 + 2655917 * 2 ^ 59
def prefixEnd_2655917 : Nat := 4983230072969 + 3 ^ 40 * 2655917 * 2
def baseEnd_2655917 : Nat := 909174666298260297482111

theorem tailTrace_2655917 : CollatzResearch.WordTrace tailWord_2655917 prefixEnd_2655917 909174666298260297482111 := by
  unfold tailWord_2655917
  simp only [CollatzResearch.WordTrace]
  refine ⟨96869251119073778356206005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64579500746049185570804003 96869251119073778356206005)
  ·
    refine ⟨9081492292413166720894313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96869251119073778356206005 9081492292413166720894313)
    ·
      refine ⟨6811119219309875040670735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9081492292413166720894313 6811119219309875040670735)
      ·
        refine ⟨10216678828964812561006103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811119219309875040670735 10216678828964812561006103)
        ·
          refine ⟨15325018243447218841509155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216678828964812561006103 15325018243447218841509155)
          ·
            refine ⟨22987527365170828262263733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15325018243447218841509155 22987527365170828262263733)
            ·
              refine ⟨2155080690484765149587225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22987527365170828262263733 2155080690484765149587225)
              ·
                refine ⟨1616310517863573862190419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155080690484765149587225 1616310517863573862190419)
                ·
                  refine ⟨2424465776795360793285629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616310517863573862190419 2424465776795360793285629)
                  ·
                    refine ⟨909174666298260297482111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424465776795360793285629 909174666298260297482111)
                    ·
                      rfl

theorem cell22_2655917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_2655917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655917 prefixEnd_2655917 := by exact prefixLift 2655917
  have htrace : WordTrace (prefixWord ++ tailWord_2655917) baseStart_2655917 baseEnd_2655917 := by
    simpa [prefixWord, tailWord_2655917, baseEnd_2655917] using wordTrace_append hprefix tailTrace_2655917
  have hstable : (prefixWord ++ tailWord_2655917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655917).length < 2 ^ (prefixWord ++ tailWord_2655917).sum := by decide
  have hdescent : baseEnd_2655917 < baseStart_2655917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655939 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_2655939 : Nat := 118140960795 + 2655939 * 2 ^ 59
def prefixEnd_2655939 : Nat := 4983230072969 + 3 ^ 40 * 2655939 * 2
def baseEnd_2655939 : Nat := 909182197347859573432043

theorem tailTrace_2655939 : CollatzResearch.WordTrace tailWord_2655939 prefixEnd_2655939 909182197347859573432043 := by
  unfold tailWord_2655939
  simp only [CollatzResearch.WordTrace]
  refine ⟨96870053524994076113506871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64580035683329384075671247 96870053524994076113506871)
  ·
    refine ⟨145305080287491114170260307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96870053524994076113506871 145305080287491114170260307)
    ·
      refine ⟨217957620431236671255390461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145305080287491114170260307 217957620431236671255390461)
      ·
        refine ⟨81734107661713751720771423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217957620431236671255390461 81734107661713751720771423)
        ·
          refine ⟨122601161492570627581157135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81734107661713751720771423 122601161492570627581157135)
          ·
            refine ⟨183901742238855941371735703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122601161492570627581157135 183901742238855941371735703)
            ·
              refine ⟨275852613358283912057603555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183901742238855941371735703 275852613358283912057603555)
              ·
                refine ⟨413778920037425868086405333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275852613358283912057603555 413778920037425868086405333)
                ·
                  refine ⟨9697943438377168783275125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 413778920037425868086405333 9697943438377168783275125)
                  ·
                    refine ⟨909182197347859573432043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9697943438377168783275125 909182197347859573432043)
                    ·
                      rfl

theorem cell22_2655939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_2655939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655939 prefixEnd_2655939 := by exact prefixLift 2655939
  have htrace : WordTrace (prefixWord ++ tailWord_2655939) baseStart_2655939 baseEnd_2655939 := by
    simpa [prefixWord, tailWord_2655939, baseEnd_2655939] using wordTrace_append hprefix tailTrace_2655939
  have hstable : (prefixWord ++ tailWord_2655939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655939).length < 2 ^ (prefixWord ++ tailWord_2655939).sum := by decide
  have hdescent : baseEnd_2655939 < baseStart_2655939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655969 : List Nat := [1, 2, 3, 1, 15]
def baseStart_2655969 : Nat := 118140960795 + 2655969 * 2 ^ 59
def prefixEnd_2655969 : Nat := 4983230072969 + 3 ^ 40 * 2655969 * 2
def baseEnd_2655969 : Nat := 3741532785847528786757

theorem tailTrace_2655969 : CollatzResearch.WordTrace tailWord_2655969 prefixEnd_2655969 3741532785847528786757 := by
  unfold tailWord_2655969
  simp only [CollatzResearch.WordTrace]
  refine ⟨96871147714885391237098961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64580765143256927491399307 96871147714885391237098961)
  ·
    refine ⟨72653360786164043427824221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96871147714885391237098961 72653360786164043427824221)
    ·
      refine ⟨27245010294811516285434083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72653360786164043427824221 27245010294811516285434083)
      ·
        refine ⟨40867515442217274428151125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27245010294811516285434083 40867515442217274428151125)
        ·
          refine ⟨3741532785847528786757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 40867515442217274428151125 3741532785847528786757)
          ·
            rfl

theorem cell22_2655969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 15].length) (baseStart_2655969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655969 prefixEnd_2655969 := by exact prefixLift 2655969
  have htrace : WordTrace (prefixWord ++ tailWord_2655969) baseStart_2655969 baseEnd_2655969 := by
    simpa [prefixWord, tailWord_2655969, baseEnd_2655969] using wordTrace_append hprefix tailTrace_2655969
  have hstable : (prefixWord ++ tailWord_2655969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655969).length < 2 ^ (prefixWord ++ tailWord_2655969).sum := by decide
  have hdescent : baseEnd_2655969 < baseStart_2655969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2655990 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_2655990 : Nat := 118140960795 + 2655990 * 2 ^ 59
def prefixEnd_2655990 : Nat := 4983230072969 + 3 ^ 40 * 2655990 * 2
def baseEnd_2655990 : Nat := 909199655690112440406887

theorem tailTrace_2655990 : CollatzResearch.WordTrace tailWord_2655990 prefixEnd_2655990 909199655690112440406887 := by
  unfold tailWord_2655990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054494602988081988975839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64581275765206207882408949 6054494602988081988975839)
  ·
    refine ⟨9081741904482122983463759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054494602988081988975839 9081741904482122983463759)
    ·
      refine ⟨13622612856723184475195639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9081741904482122983463759 13622612856723184475195639)
      ·
        refine ⟨20433919285084776712793459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13622612856723184475195639 20433919285084776712793459)
        ·
          refine ⟨30650878927627165069190189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20433919285084776712793459 30650878927627165069190189)
          ·
            refine ⟨11494079597860186900946321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30650878927627165069190189 11494079597860186900946321)
            ·
              refine ⟨8620559698395140175709741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11494079597860186900946321 8620559698395140175709741)
              ·
                refine ⟨3232709886898177565891153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8620559698395140175709741 3232709886898177565891153)
                ·
                  refine ⟨2424532415173633174418365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232709886898177565891153 2424532415173633174418365)
                  ·
                    refine ⟨909199655690112440406887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424532415173633174418365 909199655690112440406887)
                    ·
                      rfl

theorem cell22_2655990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_2655990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2655990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2655990 prefixEnd_2655990 := by exact prefixLift 2655990
  have htrace : WordTrace (prefixWord ++ tailWord_2655990) baseStart_2655990 baseEnd_2655990 := by
    simpa [prefixWord, tailWord_2655990, baseEnd_2655990] using wordTrace_append hprefix tailTrace_2655990
  have hstable : (prefixWord ++ tailWord_2655990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2655990).length < 2 ^ (prefixWord ++ tailWord_2655990).sum := by decide
  have hdescent : baseEnd_2655990 < baseStart_2655990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2655990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656031 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 7]
def baseStart_2656031 : Nat := 118140960795 + 2656031 * 2 ^ 59
def prefixEnd_2656031 : Nat := 4983230072969 + 3 ^ 40 * 2656031 * 2
def baseEnd_2656031 : Nat := 303071230276000666710587

theorem tailTrace_2656031 : CollatzResearch.WordTrace tailWord_2656031 prefixEnd_2656031 303071230276000666710587 := by
  unfold tailWord_2656031
  simp only [CollatzResearch.WordTrace]
  refine ⟨96873409040660775825855947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64582272693773850550570631 96873409040660775825855947)
  ·
    refine ⟨145310113560991163738783921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96873409040660775825855947 145310113560991163738783921)
    ·
      refine ⟨108982585170743372804087941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145310113560991163738783921 108982585170743372804087941)
      ·
        refine ⟨20434234719514382400766489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108982585170743372804087941 20434234719514382400766489)
        ·
          refine ⟨15325676039635786800574867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20434234719514382400766489 15325676039635786800574867)
          ·
            refine ⟨22988514059453680200862301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15325676039635786800574867 22988514059453680200862301)
            ·
              refine ⟨8620692772295130075323363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22988514059453680200862301 8620692772295130075323363)
              ·
                refine ⟨12931039158442695112985045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8620692772295130075323363 12931039158442695112985045)
                ·
                  refine ⟨303071230276000666710587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12931039158442695112985045 303071230276000666710587)
                  ·
                    rfl

theorem cell22_2656031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_2656031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656031 prefixEnd_2656031 := by exact prefixLift 2656031
  have htrace : WordTrace (prefixWord ++ tailWord_2656031) baseStart_2656031 baseEnd_2656031 := by
    simpa [prefixWord, tailWord_2656031, baseEnd_2656031] using wordTrace_append hprefix tailTrace_2656031
  have hstable : (prefixWord ++ tailWord_2656031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656031).length < 2 ^ (prefixWord ++ tailWord_2656031).sum := by decide
  have hdescent : baseEnd_2656031 < baseStart_2656031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656035 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 1, 3]
def baseStart_2656035 : Nat := 118140960795 + 2656035 * 2 ^ 59
def prefixEnd_2656035 : Nat := 4983230072969 + 3 ^ 40 * 2656035 * 2
def baseEnd_2656035 : Nat := 909215060109747323031749

theorem tailTrace_2656035 : CollatzResearch.WordTrace tailWord_2656035 prefixEnd_2656035 909215060109747323031749 := by
  unfold tailWord_2656035
  simp only [CollatzResearch.WordTrace]
  refine ⟨96873554932646284509001559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64582369955097523006001039 96873554932646284509001559)
  ·
    refine ⟨145310332398969426763502339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96873554932646284509001559 145310332398969426763502339)
    ·
      refine ⟨217965498598454140145253509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145310332398969426763502339 217965498598454140145253509)
      ·
        refine ⟨40868530987210151277235033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217965498598454140145253509 40868530987210151277235033)
        ·
          refine ⟨30651398240407613457926275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40868530987210151277235033 30651398240407613457926275)
          ·
            refine ⟨45977097360611420186889413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30651398240407613457926275 45977097360611420186889413)
            ·
              refine ⟨8620705755114641285041765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45977097360611420186889413 8620705755114641285041765)
              ·
                refine ⟨1616382329083995240945331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8620705755114641285041765 1616382329083995240945331)
                ·
                  refine ⟨2424573493625992861417997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616382329083995240945331 2424573493625992861417997)
                  ·
                    refine ⟨909215060109747323031749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424573493625992861417997 909215060109747323031749)
                    ·
                      rfl

theorem cell22_2656035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 3].length) (baseStart_2656035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656035 prefixEnd_2656035 := by exact prefixLift 2656035
  have htrace : WordTrace (prefixWord ++ tailWord_2656035) baseStart_2656035 baseEnd_2656035 := by
    simpa [prefixWord, tailWord_2656035, baseEnd_2656035] using wordTrace_append hprefix tailTrace_2656035
  have hstable : (prefixWord ++ tailWord_2656035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656035).length < 2 ^ (prefixWord ++ tailWord_2656035).sum := by decide
  have hdescent : baseEnd_2656035 < baseStart_2656035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656121 : List Nat := [1, 2, 1, 3, 2, 2, 1, 10]
def baseStart_2656121 : Nat := 118140960795 + 2656121 * 2 ^ 59
def prefixEnd_2656121 : Nat := 4983230072969 + 3 ^ 40 * 2656121 * 2
def baseEnd_2656121 : Nat := 101027166629696862820165

theorem tailTrace_2656121 : CollatzResearch.WordTrace tailWord_2656121 prefixEnd_2656121 101027166629696862820165 := by
  unfold tailWord_2656121
  simp only [CollatzResearch.WordTrace]
  refine ⟨96876691610334721196632217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64584461073556480797754811 96876691610334721196632217)
  ·
    refine ⟨72657518707751040897474163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96876691610334721196632217 72657518707751040897474163)
    ·
      refine ⟨108986278061626561346211245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72657518707751040897474163 108986278061626561346211245)
      ·
        refine ⟨40869854273109960504829217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108986278061626561346211245 40869854273109960504829217)
        ·
          refine ⟨30652390704832470378621913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40869854273109960504829217 30652390704832470378621913)
          ·
            refine ⟨22989293028624352783966435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30652390704832470378621913 22989293028624352783966435)
            ·
              refine ⟨34483939542936529175949653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22989293028624352783966435 34483939542936529175949653)
              ·
                refine ⟨101027166629696862820165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34483939542936529175949653 101027166629696862820165)
                ·
                  rfl

theorem cell22_2656121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 10].length) (baseStart_2656121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656121 prefixEnd_2656121 := by exact prefixLift 2656121
  have htrace : WordTrace (prefixWord ++ tailWord_2656121) baseStart_2656121 baseEnd_2656121 := by
    simpa [prefixWord, tailWord_2656121, baseEnd_2656121] using wordTrace_append hprefix tailTrace_2656121
  have hstable : (prefixWord ++ tailWord_2656121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656121).length < 2 ^ (prefixWord ++ tailWord_2656121).sum := by decide
  have hdescent : baseEnd_2656121 < baseStart_2656121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656129 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2656129 : Nat := 118140960795 + 2656129 * 2 ^ 59
def prefixEnd_2656129 : Nat := 4983230072969 + 3 ^ 40 * 2656129 * 2
def baseEnd_2656129 : Nat := 909247238230762411181461

theorem tailTrace_2656129 : CollatzResearch.WordTrace tailWord_2656129 prefixEnd_2656129 909247238230762411181461 := by
  unfold tailWord_2656129
  simp only [CollatzResearch.WordTrace]
  refine ⟨96876983394305738562923441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64584655596203825708615627 96876983394305738562923441)
  ·
    refine ⟨72657737545729303922192581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96876983394305738562923441 72657737545729303922192581)
    ·
      refine ⟨13623325789824244485411109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72657737545729303922192581 13623325789824244485411109)
      ·
        refine ⟨2554373585592045841014583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13623325789824244485411109 2554373585592045841014583)
        ·
          refine ⟨3831560378388068761521875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554373585592045841014583 3831560378388068761521875)
          ·
            refine ⟨5747340567582103142282813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831560378388068761521875 5747340567582103142282813)
            ·
              refine ⟨2155252712843288678356055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747340567582103142282813 2155252712843288678356055)
              ·
                refine ⟨3232879069264933017534083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155252712843288678356055 3232879069264933017534083)
                ·
                  refine ⟨4849318603897399526301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232879069264933017534083 4849318603897399526301125)
                  ·
                    refine ⟨909247238230762411181461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849318603897399526301125 909247238230762411181461)
                    ·
                      rfl

theorem cell22_2656129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2656129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656129 prefixEnd_2656129 := by exact prefixLift 2656129
  have htrace : WordTrace (prefixWord ++ tailWord_2656129) baseStart_2656129 baseEnd_2656129 := by
    simpa [prefixWord, tailWord_2656129, baseEnd_2656129] using wordTrace_append hprefix tailTrace_2656129
  have hstable : (prefixWord ++ tailWord_2656129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656129).length < 2 ^ (prefixWord ++ tailWord_2656129).sum := by decide
  have hdescent : baseEnd_2656129 < baseStart_2656129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656138 : List Nat := [3, 1, 2, 4, 2, 10]
def baseStart_2656138 : Nat := 118140960795 + 2656138 * 2 ^ 59
def prefixEnd_2656138 : Nat := 4983230072969 + 3 ^ 40 * 2656138 * 2
def baseEnd_2656138 : Nat := 11225312581662831946993

theorem tailTrace_2656138 : CollatzResearch.WordTrace tailWord_2656138 prefixEnd_2656138 11225312581662831946993 := by
  unfold tailWord_2656138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219327912818283275000267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64584874434182088733334045 24219327912818283275000267)
  ·
    refine ⟨36328991869227424912500401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24219327912818283275000267 36328991869227424912500401)
    ·
      refine ⟨27246743901920568684375301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36328991869227424912500401 27246743901920568684375301)
      ·
        refine ⟨5108764481610106628320369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27246743901920568684375301 5108764481610106628320369)
        ·
          refine ⟨3831573361207579971240277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5108764481610106628320369 3831573361207579971240277)
          ·
            refine ⟨11225312581662831946993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3831573361207579971240277 11225312581662831946993)
            ·
              rfl

theorem cell22_2656138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 10].length) (baseStart_2656138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656138 prefixEnd_2656138 := by exact prefixLift 2656138
  have htrace : WordTrace (prefixWord ++ tailWord_2656138) baseStart_2656138 baseEnd_2656138 := by
    simpa [prefixWord, tailWord_2656138, baseEnd_2656138] using wordTrace_append hprefix tailTrace_2656138
  have hstable : (prefixWord ++ tailWord_2656138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656138).length < 2 ^ (prefixWord ++ tailWord_2656138).sum := by decide
  have hdescent : baseEnd_2656138 < baseStart_2656138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656174 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2656174 : Nat := 118140960795 + 2656174 * 2 ^ 59
def prefixEnd_2656174 : Nat := 4983230072969 + 3 ^ 40 * 2656174 * 2
def baseEnd_2656174 : Nat := 909262642650397293806323

theorem tailTrace_2656174 : CollatzResearch.WordTrace tailWord_2656174 prefixEnd_2656174 909262642650397293806323 := by
  unfold tailWord_2656174
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109828084892838906038947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64585749786095140832207717 12109828084892838906038947)
  ·
    refine ⟨18164742127339258359058421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109828084892838906038947 18164742127339258359058421)
    ·
      refine ⟨1702944574438055471161727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18164742127339258359058421 1702944574438055471161727)
      ·
        refine ⟨2554416861657083206742591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702944574438055471161727 2554416861657083206742591)
        ·
          refine ⟨3831625292485624810113887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554416861657083206742591 3831625292485624810113887)
          ·
            refine ⟨5747437938728437215170831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831625292485624810113887 5747437938728437215170831)
            ·
              refine ⟨8621156908092655822756247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747437938728437215170831 8621156908092655822756247)
              ·
                refine ⟨12931735362138983734134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8621156908092655822756247 12931735362138983734134371)
                ·
                  refine ⟨19397603043208475601201557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12931735362138983734134371 19397603043208475601201557)
                  ·
                    refine ⟨909262642650397293806323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19397603043208475601201557 909262642650397293806323)
                    ·
                      rfl

theorem cell22_2656174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2656174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656174 prefixEnd_2656174 := by exact prefixLift 2656174
  have htrace : WordTrace (prefixWord ++ tailWord_2656174) baseStart_2656174 baseEnd_2656174 := by
    simpa [prefixWord, tailWord_2656174, baseEnd_2656174] using wordTrace_append hprefix tailTrace_2656174
  have hstable : (prefixWord ++ tailWord_2656174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656174).length < 2 ^ (prefixWord ++ tailWord_2656174).sum := by decide
  have hdescent : baseEnd_2656174 < baseStart_2656174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656200 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_2656200 : Nat := 118140960795 + 2656200 * 2 ^ 59
def prefixEnd_2656200 : Nat := 4983230072969 + 3 ^ 40 * 2656200 * 2
def baseEnd_2656200 : Nat := 303090514327247297552081

theorem tailTrace_2656200 : CollatzResearch.WordTrace tailWord_2656200 prefixEnd_2656200 303090514327247297552081 := by
  unfold tailWord_2656200
  simp only [CollatzResearch.WordTrace]
  refine ⟨48439786488524258844379027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64586381984699011792505369 48439786488524258844379027)
  ·
    refine ⟨72659679732786388266568541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48439786488524258844379027 72659679732786388266568541)
    ·
      refine ⟨27247379899794895599963203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72659679732786388266568541 27247379899794895599963203)
      ·
        refine ⟨40871069849692343399944805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27247379899794895599963203 40871069849692343399944805)
        ·
          refine ⟨7663325596817314387489651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40871069849692343399944805 7663325596817314387489651)
          ·
            refine ⟨11494988395225971581234477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663325596817314387489651 11494988395225971581234477)
            ·
              refine ⟨4310620648209739342962929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11494988395225971581234477 4310620648209739342962929)
              ·
                refine ⟨3232965486157304507222197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310620648209739342962929 3232965486157304507222197)
                ·
                  refine ⟨303090514327247297552081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232965486157304507222197 303090514327247297552081)
                  ·
                    rfl

theorem cell22_2656200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_2656200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656200 prefixEnd_2656200 := by exact prefixLift 2656200
  have htrace : WordTrace (prefixWord ++ tailWord_2656200) baseStart_2656200 baseEnd_2656200 := by
    simpa [prefixWord, tailWord_2656200, baseEnd_2656200] using wordTrace_append hprefix tailTrace_2656200
  have hstable : (prefixWord ++ tailWord_2656200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656200).length < 2 ^ (prefixWord ++ tailWord_2656200).sum := by decide
  have hdescent : baseEnd_2656200 < baseStart_2656200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656217 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 5]
def baseStart_2656217 : Nat := 118140960795 + 2656217 * 2 ^ 59
def prefixEnd_2656217 : Nat := 4983230072969 + 3 ^ 40 * 2656217 * 2
def baseEnd_2656217 : Nat := 303092454143053171660397

theorem tailTrace_2656217 : CollatzResearch.WordTrace tailWord_2656217 prefixEnd_2656217 303092454143053171660397 := by
  unfold tailWord_2656217
  simp only [CollatzResearch.WordTrace]
  refine ⟨96880193017986929592126905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64586795345324619728084603 96880193017986929592126905)
  ·
    refine ⟨72660144763490197194095179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96880193017986929592126905 72660144763490197194095179)
    ·
      refine ⟨108990217145235295791142769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72660144763490197194095179 108990217145235295791142769)
      ·
        refine ⟨81742662858926471843357077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108990217145235295791142769 81742662858926471843357077)
        ·
          refine ⟨3831687321512178367657363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81742662858926471843357077 3831687321512178367657363)
          ·
            refine ⟨5747530982268267551486045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831687321512178367657363 5747530982268267551486045)
            ·
              refine ⟨2155324118350600331807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747530982268267551486045 2155324118350600331807267)
              ·
                refine ⟨3232986177525900497710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155324118350600331807267 3232986177525900497710901)
                ·
                  refine ⟨303092454143053171660397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232986177525900497710901 303092454143053171660397)
                  ·
                    rfl

theorem cell22_2656217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_2656217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656217 prefixEnd_2656217 := by exact prefixLift 2656217
  have htrace : WordTrace (prefixWord ++ tailWord_2656217) baseStart_2656217 baseEnd_2656217 := by
    simpa [prefixWord, tailWord_2656217, baseEnd_2656217] using wordTrace_append hprefix tailTrace_2656217
  have hstable : (prefixWord ++ tailWord_2656217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656217).length < 2 ^ (prefixWord ++ tailWord_2656217).sum := by decide
  have hdescent : baseEnd_2656217 < baseStart_2656217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656228 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_2656228 : Nat := 118140960795 + 2656228 * 2 ^ 59
def prefixEnd_2656228 : Nat := 4983230072969 + 3 ^ 40 * 2656228 * 2
def baseEnd_2656228 : Nat := 303093709317986384318719

theorem tailTrace_2656228 : CollatzResearch.WordTrace tailWord_2656228 prefixEnd_2656228 303093709317986384318719 := by
  unfold tailWord_2656228
  simp only [CollatzResearch.WordTrace]
  refine ⟨48440297110473539235388669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64587062813964718980518225 48440297110473539235388669)
  ·
    refine ⟨18165111416427577213270751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48440297110473539235388669 18165111416427577213270751)
    ·
      refine ⟨27247667124641365819906127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18165111416427577213270751 27247667124641365819906127)
      ·
        refine ⟨40871500686962048729859191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27247667124641365819906127 40871500686962048729859191)
        ·
          refine ⟨61307251030443073094788787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40871500686962048729859191 61307251030443073094788787)
          ·
            refine ⟨91960876545664609642183181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61307251030443073094788787 91960876545664609642183181)
            ·
              refine ⟨34485328704624228615818693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91960876545664609642183181 34485328704624228615818693)
              ·
                refine ⟨6465999132117042865466005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34485328704624228615818693 6465999132117042865466005)
                ·
                  refine ⟨303093709317986384318719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6465999132117042865466005 303093709317986384318719)
                  ·
                    rfl

theorem cell22_2656228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_2656228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656228 prefixEnd_2656228 := by exact prefixLift 2656228
  have htrace : WordTrace (prefixWord ++ tailWord_2656228) baseStart_2656228 baseEnd_2656228 := by
    simpa [prefixWord, tailWord_2656228, baseEnd_2656228] using wordTrace_append hprefix tailTrace_2656228
  have hstable : (prefixWord ++ tailWord_2656228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656228).length < 2 ^ (prefixWord ++ tailWord_2656228).sum := by decide
  have hdescent : baseEnd_2656228 < baseStart_2656228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656243 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_2656243 : Nat := 118140960795 + 2656243 * 2 ^ 59
def prefixEnd_2656243 : Nat := 4983230072969 + 3 ^ 40 * 2656243 * 2
def baseEnd_2656243 : Nat := 909286262760504113831111

theorem tailTrace_2656243 : CollatzResearch.WordTrace tailWord_2656243 prefixEnd_2656243 909286262760504113831111 := by
  unfold tailWord_2656243
  simp only [CollatzResearch.WordTrace]
  refine ⟨96881141315892736032573383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64587427543928490688382255 96881141315892736032573383)
  ·
    refine ⟨145321711973839104048860075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96881141315892736032573383 145321711973839104048860075)
    ·
      refine ⟨217982567960758656073290113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145321711973839104048860075 217982567960758656073290113)
      ·
        refine ⟨163486925970568992054967585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217982567960758656073290113 163486925970568992054967585)
        ·
          refine ⟨122615194477926744041225689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163486925970568992054967585 122615194477926744041225689)
          ·
            refine ⟨91961395858445058030919267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122615194477926744041225689 91961395858445058030919267)
            ·
              refine ⟨137942093787667587046378901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91961395858445058030919267 137942093787667587046378901)
              ·
                refine ⟨6466035646296918142799011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137942093787667587046378901 6466035646296918142799011)
                ·
                  refine ⟨9699053469445377214198517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466035646296918142799011 9699053469445377214198517)
                  ·
                    refine ⟨909286262760504113831111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9699053469445377214198517 909286262760504113831111)
                    ·
                      rfl

theorem cell22_2656243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_2656243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656243 prefixEnd_2656243 := by exact prefixLift 2656243
  have htrace : WordTrace (prefixWord ++ tailWord_2656243) baseStart_2656243 baseEnd_2656243 := by
    simpa [prefixWord, tailWord_2656243, baseEnd_2656243] using wordTrace_append hprefix tailTrace_2656243
  have hstable : (prefixWord ++ tailWord_2656243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656243).length < 2 ^ (prefixWord ++ tailWord_2656243).sum := by decide
  have hdescent : baseEnd_2656243 < baseStart_2656243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656380 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_2656380 : Nat := 118140960795 + 2656380 * 2 ^ 59
def prefixEnd_2656380 : Nat := 4983230072969 + 3 ^ 40 * 2656380 * 2
def baseEnd_2656380 : Nat := 303111053553427141051897

theorem tailTrace_2656380 : CollatzResearch.WordTrace tailWord_2656380 prefixEnd_2656380 303111053553427141051897 := by
  unfold tailWord_2656380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48443069058198204215155297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64590758744264272286873729 48443069058198204215155297)
  ·
    refine ⟨36332301793648653161366473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48443069058198204215155297 36332301793648653161366473)
    ·
      refine ⟨27249226345236489871024855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36332301793648653161366473 27249226345236489871024855)
      ·
        refine ⟨40873839517854734806537283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27249226345236489871024855 40873839517854734806537283)
        ·
          refine ⟨61310759276782102209805925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40873839517854734806537283 61310759276782102209805925)
          ·
            refine ⟨11495767364396644164338611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61310759276782102209805925 11495767364396644164338611)
            ·
              refine ⟨17243651046594966246507917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495767364396644164338611 17243651046594966246507917)
              ·
                refine ⟨6466369142473112342440469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17243651046594966246507917 6466369142473112342440469)
                ·
                  refine ⟨303111053553427141051897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6466369142473112342440469 303111053553427141051897)
                  ·
                    rfl

theorem cell22_2656380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_2656380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656380 prefixEnd_2656380 := by exact prefixLift 2656380
  have htrace : WordTrace (prefixWord ++ tailWord_2656380) baseStart_2656380 baseEnd_2656380 := by
    simpa [prefixWord, tailWord_2656380, baseEnd_2656380] using wordTrace_append hprefix tailTrace_2656380
  have hstable : (prefixWord ++ tailWord_2656380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656380).length < 2 ^ (prefixWord ++ tailWord_2656380).sum := by decide
  have hdescent : baseEnd_2656380 < baseStart_2656380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656412 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2656412 : Nat := 118140960795 + 2656412 * 2 ^ 59
def prefixEnd_2656412 : Nat := 4983230072969 + 3 ^ 40 * 2656412 * 2
def baseEnd_2656412 : Nat := 909344114914244006355593

theorem tailTrace_2656412 : CollatzResearch.WordTrace tailWord_2656412 prefixEnd_2656412 909344114914244006355593 := by
  unfold tailWord_2656412
  simp only [CollatzResearch.WordTrace]
  refine ⟨48443652626140238947737745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64591536834853651930316993 48443652626140238947737745)
  ·
    refine ⟨36332739469605179210803309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48443652626140238947737745 36332739469605179210803309)
    ·
      refine ⟨13624777301101942204051241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36332739469605179210803309 13624777301101942204051241)
      ·
        refine ⟨10218582975826456653038431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13624777301101942204051241 10218582975826456653038431)
        ·
          refine ⟨15327874463739684979557647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218582975826456653038431 15327874463739684979557647)
          ·
            refine ⟨22991811695609527469336471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15327874463739684979557647 22991811695609527469336471)
            ·
              refine ⟨34487717543414291204004707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22991811695609527469336471 34487717543414291204004707)
              ·
                refine ⟨51731576315121436806007061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34487717543414291204004707 51731576315121436806007061)
                ·
                  refine ⟨2424917639771317350281581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51731576315121436806007061 2424917639771317350281581)
                  ·
                    refine ⟨909344114914244006355593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424917639771317350281581 909344114914244006355593)
                    ·
                      rfl

theorem cell22_2656412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2656412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656412 prefixEnd_2656412 := by exact prefixLift 2656412
  have htrace : WordTrace (prefixWord ++ tailWord_2656412) baseStart_2656412 baseEnd_2656412 := by
    simpa [prefixWord, tailWord_2656412, baseEnd_2656412] using wordTrace_append hprefix tailTrace_2656412
  have hstable : (prefixWord ++ tailWord_2656412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656412).length < 2 ^ (prefixWord ++ tailWord_2656412).sum := by decide
  have hdescent : baseEnd_2656412 < baseStart_2656412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656429 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2656429 : Nat := 118140960795 + 2656429 * 2 ^ 59
def prefixEnd_2656429 : Nat := 4983230072969 + 3 ^ 40 * 2656429 * 2
def baseEnd_2656429 : Nat := 909349934361661628680541

theorem tailTrace_2656429 : CollatzResearch.WordTrace tailWord_2656429 prefixEnd_2656429 909349934361661628680541 := by
  unfold tailWord_2656429
  simp only [CollatzResearch.WordTrace]
  refine ⟨96887925293218889798844341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64591950195479259865896227 96887925293218889798844341)
  ·
    refine ⟨9083242996239270918641657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96887925293218889798844341 9083242996239270918641657)
    ·
      refine ⟨6812432247179453188981243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9083242996239270918641657 6812432247179453188981243)
      ·
        refine ⟨10218648370769179783471865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6812432247179453188981243 10218648370769179783471865)
        ·
          refine ⟨7663986278076884837603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10218648370769179783471865 7663986278076884837603899)
          ·
            refine ⟨11495979417115327256405849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663986278076884837603899 11495979417115327256405849)
            ·
              refine ⟨8621984562836495442304387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11495979417115327256405849 8621984562836495442304387)
              ·
                refine ⟨12932976844254743163456581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8621984562836495442304387 12932976844254743163456581)
                ·
                  refine ⟨2424933158297764343148109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12932976844254743163456581 2424933158297764343148109)
                  ·
                    refine ⟨909349934361661628680541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424933158297764343148109 909349934361661628680541)
                    ·
                      rfl

theorem cell22_2656429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2656429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656429 prefixEnd_2656429 := by exact prefixLift 2656429
  have htrace : WordTrace (prefixWord ++ tailWord_2656429) baseStart_2656429 baseEnd_2656429 := by
    simpa [prefixWord, tailWord_2656429, baseEnd_2656429] using wordTrace_append hprefix tailTrace_2656429
  have hstable : (prefixWord ++ tailWord_2656429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656429).length < 2 ^ (prefixWord ++ tailWord_2656429).sum := by decide
  have hdescent : baseEnd_2656429 < baseStart_2656429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656446 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_2656446 : Nat := 118140960795 + 2656446 * 2 ^ 59
def prefixEnd_2656446 : Nat := 4983230072969 + 3 ^ 40 * 2656446 * 2
def baseEnd_2656446 : Nat := 909355753809079251005489

theorem tailTrace_2656446 : CollatzResearch.WordTrace tailWord_2656446 prefixEnd_2656446 909355753809079251005489 := by
  unfold tailWord_2656446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111068166769662712776649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64592363556104867801475461 12111068166769662712776649)
  ·
    refine ⟨9083301125077247034582487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12111068166769662712776649 9083301125077247034582487)
    ·
      refine ⟨13624951687615870551873731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083301125077247034582487 13624951687615870551873731)
      ·
        refine ⟨20437427531423805827810597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13624951687615870551873731 20437427531423805827810597)
        ·
          refine ⟨3832017662141963592714487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20437427531423805827810597 3832017662141963592714487)
          ·
            refine ⟨5748026493212945389071731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832017662141963592714487 5748026493212945389071731)
            ·
              refine ⟨8622039739819418083607597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748026493212945389071731 8622039739819418083607597)
              ·
                refine ⟨3233264902432281781352849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8622039739819418083607597 3233264902432281781352849)
                ·
                  refine ⟨2424948676824211336014637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3233264902432281781352849 2424948676824211336014637)
                  ·
                    refine ⟨909355753809079251005489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424948676824211336014637 909355753809079251005489)
                    ·
                      rfl

theorem cell22_2656446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_2656446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656446 prefixEnd_2656446 := by exact prefixLift 2656446
  have htrace : WordTrace (prefixWord ++ tailWord_2656446) baseStart_2656446 baseEnd_2656446 := by
    simpa [prefixWord, tailWord_2656446, baseEnd_2656446] using wordTrace_append hprefix tailTrace_2656446
  have hstable : (prefixWord ++ tailWord_2656446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656446).length < 2 ^ (prefixWord ++ tailWord_2656446).sum := by decide
  have hdescent : baseEnd_2656446 < baseStart_2656446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656482 : List Nat := [3, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2656482 : Nat := 118140960795 + 2656482 * 2 ^ 59
def prefixEnd_2656482 : Nat := 4983230072969 + 3 ^ 40 * 2656482 * 2
def baseEnd_2656482 : Nat := 303122692448262385701793

theorem tailTrace_2656482 : CollatzResearch.WordTrace tailWord_2656482 prefixEnd_2656482 303122692448262385701793 := by
  unfold tailWord_2656482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222464590506719962630925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64593238908017919900349133 24222464590506719962630925)
  ·
    refine ⟨9083424221440019985986597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24222464590506719962630925 9083424221440019985986597)
    ·
      refine ⟨1703142041520003747372487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9083424221440019985986597 1703142041520003747372487)
      ·
        refine ⟨2554713062280005621058731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703142041520003747372487 2554713062280005621058731)
        ·
          refine ⟨3832069593420008431588097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554713062280005621058731 3832069593420008431588097)
          ·
            refine ⟨2874052195065006323691073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832069593420008431588097 2874052195065006323691073)
            ·
              refine ⟨2155539146298754742768305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874052195065006323691073 2155539146298754742768305)
              ·
                refine ⟨1616654359724066057076229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155539146298754742768305 1616654359724066057076229)
                ·
                  refine ⟨303122692448262385701793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616654359724066057076229 303122692448262385701793)
                  ·
                    rfl

theorem cell22_2656482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2656482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656482 prefixEnd_2656482 := by exact prefixLift 2656482
  have htrace : WordTrace (prefixWord ++ tailWord_2656482) baseStart_2656482 baseEnd_2656482 := by
    simpa [prefixWord, tailWord_2656482, baseEnd_2656482] using wordTrace_append hprefix tailTrace_2656482
  have hstable : (prefixWord ++ tailWord_2656482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656482).length < 2 ^ (prefixWord ++ tailWord_2656482).sum := by decide
  have hdescent : baseEnd_2656482 < baseStart_2656482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656502 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2656502 : Nat := 118140960795 + 2656502 * 2 ^ 59
def prefixEnd_2656502 : Nat := 4983230072969 + 3 ^ 40 * 2656502 * 2
def baseEnd_2656502 : Nat := 909374923753513771605317

theorem tailTrace_2656502 : CollatzResearch.WordTrace tailWord_2656502 prefixEnd_2656502 909374923753513771605317 := by
  unfold tailWord_2656502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055661738872151454140735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64593725214636282177501173 6055661738872151454140735)
  ·
    refine ⟨9083492608308227181211103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055661738872151454140735 9083492608308227181211103)
    ·
      refine ⟨13625238912462340771816655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083492608308227181211103 13625238912462340771816655)
      ·
        refine ⟨20437858368693511157724983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13625238912462340771816655 20437858368693511157724983)
        ·
          refine ⟨30656787553040266736587475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437858368693511157724983 30656787553040266736587475)
          ·
            refine ⟨45985181329560400104881213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30656787553040266736587475 45985181329560400104881213)
            ·
              refine ⟨17244442998585150039330455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45985181329560400104881213 17244442998585150039330455)
              ·
                refine ⟨25866664497877725058995683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17244442998585150039330455 25866664497877725058995683)
                ·
                  refine ⟨38799996746816587588493525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25866664497877725058995683 38799996746816587588493525)
                  ·
                    refine ⟨909374923753513771605317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38799996746816587588493525 909374923753513771605317)
                    ·
                      rfl

theorem cell22_2656502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2656502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656502 prefixEnd_2656502 := by exact prefixLift 2656502
  have htrace : WordTrace (prefixWord ++ tailWord_2656502) baseStart_2656502 baseEnd_2656502 := by
    simpa [prefixWord, tailWord_2656502, baseEnd_2656502] using wordTrace_append hprefix tailTrace_2656502
  have hstable : (prefixWord ++ tailWord_2656502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656502).length < 2 ^ (prefixWord ++ tailWord_2656502).sum := by decide
  have hdescent : baseEnd_2656502 < baseStart_2656502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656549 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 6]
def baseStart_2656549 : Nat := 118140960795 + 2656549 * 2 ^ 59
def prefixEnd_2656549 : Nat := 4983230072969 + 3 ^ 40 * 2656549 * 2
def baseEnd_2656549 : Nat := 303130337604673771893391

theorem tailTrace_2656549 : CollatzResearch.WordTrace tailWord_2656549 prefixEnd_2656549 303130337604673771893391 := by
  unfold tailWord_2656549
  simp only [CollatzResearch.WordTrace]
  refine ⟨96892302052784150293212701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64594868035189433528808467 96892302052784150293212701)
  ·
    refine ⟨36334613269794056359954763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96892302052784150293212701 36334613269794056359954763)
    ·
      refine ⟨54501919904691084539932145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36334613269794056359954763 54501919904691084539932145)
      ·
        refine ⟨40876439928518313404949109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54501919904691084539932145 40876439928518313404949109)
        ·
          refine ⟨3832166243298591881713979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40876439928518313404949109 3832166243298591881713979)
          ·
            refine ⟨5748249364947887822570969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832166243298591881713979 5748249364947887822570969)
            ·
              refine ⟨4311187023710915866928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748249364947887822570969 4311187023710915866928227)
              ·
                refine ⟨6466780535566373800392341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4311187023710915866928227 6466780535566373800392341)
                ·
                  refine ⟨303130337604673771893391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6466780535566373800392341 303130337604673771893391)
                  ·
                    rfl

theorem cell22_2656549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_2656549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656549 prefixEnd_2656549 := by exact prefixLift 2656549
  have htrace : WordTrace (prefixWord ++ tailWord_2656549) baseStart_2656549 baseEnd_2656549 := by
    simpa [prefixWord, tailWord_2656549, baseEnd_2656549] using wordTrace_append hprefix tailTrace_2656549
  have hstable : (prefixWord ++ tailWord_2656549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656549).length < 2 ^ (prefixWord ++ tailWord_2656549).sum := by decide
  have hdescent : baseEnd_2656549 < baseStart_2656549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656660 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2656660 : Nat := 118140960795 + 2656660 * 2 ^ 59
def prefixEnd_2656660 : Nat := 4983230072969 + 3 ^ 40 * 2656660 * 2
def baseEnd_2656660 : Nat := 909429010382454026154833

theorem tailTrace_2656660 : CollatzResearch.WordTrace tailWord_2656660 prefixEnd_2656660 909429010382454026154833 := by
  unfold tailWord_2656660
  simp only [CollatzResearch.WordTrace]
  refine ⟨48448175277691008125251717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64597567036921344167002289 48448175277691008125251717)
  ·
    refine ⟨9084032864567064023484697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48448175277691008125251717 9084032864567064023484697)
    ·
      refine ⟨6813024648425298017613523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9084032864567064023484697 6813024648425298017613523)
      ·
        refine ⟨10219536972637947026420285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813024648425298017613523 10219536972637947026420285)
        ·
          refine ⟨3832326364739230134907607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10219536972637947026420285 3832326364739230134907607)
          ·
            refine ⟨5748489547108845202361411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832326364739230134907607 5748489547108845202361411)
            ·
              refine ⟨8622734320663267803542117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748489547108845202361411 8622734320663267803542117)
              ·
                refine ⟨1616762685124362713164147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8622734320663267803542117 1616762685124362713164147)
                ·
                  refine ⟨2425144027686544069746221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616762685124362713164147 2425144027686544069746221)
                  ·
                    refine ⟨909429010382454026154833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425144027686544069746221 909429010382454026154833)
                    ·
                      rfl

theorem cell22_2656660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2656660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656660 prefixEnd_2656660 := by exact prefixLift 2656660
  have htrace : WordTrace (prefixWord ++ tailWord_2656660) baseStart_2656660 baseEnd_2656660 := by
    simpa [prefixWord, tailWord_2656660, baseEnd_2656660] using wordTrace_append hprefix tailTrace_2656660
  have hstable : (prefixWord ++ tailWord_2656660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656660).length < 2 ^ (prefixWord ++ tailWord_2656660).sum := by decide
  have hdescent : baseEnd_2656660 < baseStart_2656660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656662 : List Nat := [5, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2656662 : Nat := 118140960795 + 2656662 * 2 ^ 59
def prefixEnd_2656662 : Nat := 4983230072969 + 3 ^ 40 * 2656662 * 2
def baseEnd_2656662 : Nat := 101047743891480743067203

theorem tailTrace_2656662 : CollatzResearch.WordTrace tailWord_2656662 prefixEnd_2656662 101047743891480743067203 := by
  unfold tailWord_2656662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056026468835923162004765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64597615667583180394717493 6056026468835923162004765)
  ·
    refine ⟨2271009925813471185751787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6056026468835923162004765 2271009925813471185751787)
    ·
      refine ⟨3406514888720206778627681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2271009925813471185751787 3406514888720206778627681)
      ·
        refine ⟨2554886166540155083970761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3406514888720206778627681 2554886166540155083970761)
        ·
          refine ⟨1916164624905116312978071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2554886166540155083970761 1916164624905116312978071)
          ·
            refine ⟨2874246937357674469467107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916164624905116312978071 2874246937357674469467107)
            ·
              refine ⟨4311370406036511704200661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874246937357674469467107 4311370406036511704200661)
              ·
                refine ⟨101047743891480743067203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4311370406036511704200661 101047743891480743067203)
                ·
                  rfl

theorem cell22_2656662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2656662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656662 prefixEnd_2656662 := by exact prefixLift 2656662
  have htrace : WordTrace (prefixWord ++ tailWord_2656662) baseStart_2656662 baseEnd_2656662 := by
    simpa [prefixWord, tailWord_2656662, baseEnd_2656662] using wordTrace_append hprefix tailTrace_2656662
  have hstable : (prefixWord ++ tailWord_2656662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656662).length < 2 ^ (prefixWord ++ tailWord_2656662).sum := by decide
  have hdescent : baseEnd_2656662 < baseStart_2656662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656701 : List Nat := [1, 4, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2656701 : Nat := 118140960795 + 2656701 * 2 ^ 59
def prefixEnd_2656701 : Nat := 4983230072969 + 3 ^ 40 * 2656701 * 2
def baseEnd_2656701 : Nat := 303147681840114528626569

theorem tailTrace_2656701 : CollatzResearch.WordTrace tailWord_2656701 prefixEnd_2656701 303147681840114528626569 := by
  unfold tailWord_2656701
  simp only [CollatzResearch.WordTrace]
  refine ⟨96897845948233480252745957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64598563965488986835163971 96897845948233480252745957)
  ·
    refine ⟨18168346115293777547389867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96897845948233480252745957 18168346115293777547389867)
    ·
      refine ⟨27252519172940666321084801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18168346115293777547389867 27252519172940666321084801)
      ·
        refine ⟨20439389379705499740813601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27252519172940666321084801 20439389379705499740813601)
        ·
          refine ⟨15329542034779124805610201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20439389379705499740813601 15329542034779124805610201)
          ·
            refine ⟨11497156526084343604207651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329542034779124805610201 11497156526084343604207651)
            ·
              refine ⟨17245734789126515406311477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11497156526084343604207651 17245734789126515406311477)
              ·
                refine ⟨1616787636480610819341701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17245734789126515406311477 1616787636480610819341701)
                ·
                  refine ⟨303147681840114528626569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616787636480610819341701 303147681840114528626569)
                  ·
                    rfl

theorem cell22_2656701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2656701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656701 prefixEnd_2656701 := by exact prefixLift 2656701
  have htrace : WordTrace (prefixWord ++ tailWord_2656701) baseStart_2656701 baseEnd_2656701 := by
    simpa [prefixWord, tailWord_2656701, baseEnd_2656701] using wordTrace_append hprefix tailTrace_2656701
  have hstable : (prefixWord ++ tailWord_2656701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656701).length < 2 ^ (prefixWord ++ tailWord_2656701).sum := by decide
  have hdescent : baseEnd_2656701 < baseStart_2656701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656714 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2656714 : Nat := 118140960795 + 2656714 * 2 ^ 59
def prefixEnd_2656714 : Nat := 4983230072969 + 3 ^ 40 * 2656714 * 2
def baseEnd_2656714 : Nat := 909447495686015885304667

theorem tailTrace_2656714 : CollatzResearch.WordTrace tailWord_2656714 prefixEnd_2656714 909447495686015885304667 := by
  unfold tailWord_2656714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24224580024296595868242299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64598880064790922315312797 24224580024296595868242299)
  ·
    refine ⟨36336870036444893802363449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24224580024296595868242299 36336870036444893802363449)
    ·
      refine ⟨27252652527333670351772587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36336870036444893802363449 27252652527333670351772587)
      ·
        refine ⟨40878978791000505527658881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27252652527333670351772587 40878978791000505527658881)
        ·
          refine ⟨30659234093250379145744161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40878978791000505527658881 30659234093250379145744161)
          ·
            refine ⟨22994425569937784359308121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30659234093250379145744161 22994425569937784359308121)
            ·
              refine ⟨17245819177453338269481091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22994425569937784359308121 17245819177453338269481091)
              ·
                refine ⟨25868728766180007404221637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17245819177453338269481091 25868728766180007404221637)
                ·
                  refine ⟨4850386643658751388291557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25868728766180007404221637 4850386643658751388291557)
                  ·
                    refine ⟨909447495686015885304667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850386643658751388291557 909447495686015885304667)
                    ·
                      rfl

theorem cell22_2656714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2656714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656714 prefixEnd_2656714 := by exact prefixLift 2656714
  have htrace : WordTrace (prefixWord ++ tailWord_2656714) baseStart_2656714 baseEnd_2656714 := by
    simpa [prefixWord, tailWord_2656714, baseEnd_2656714] using wordTrace_append hprefix tailTrace_2656714
  have hstable : (prefixWord ++ tailWord_2656714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656714).length < 2 ^ (prefixWord ++ tailWord_2656714).sum := by decide
  have hdescent : baseEnd_2656714 < baseStart_2656714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656746 : List Nat := [3, 1, 3, 1, 3, 1, 4, 6]
def baseStart_2656746 : Nat := 118140960795 + 2656746 * 2 ^ 59
def prefixEnd_2656746 : Nat := 4983230072969 + 3 ^ 40 * 2656746 * 2
def baseEnd_2656746 : Nat := 101050938882219829833841

theorem tailTrace_2656746 : CollatzResearch.WordTrace tailWord_2656746 prefixEnd_2656746 101050938882219829833841 := by
  unfold tailWord_2656746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24224871808267613234533523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64599658155380301958756061 24224871808267613234533523)
  ·
    refine ⟨36337307712401419851800285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24224871808267613234533523 36337307712401419851800285)
    ·
      refine ⟨13626490392150532444425107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36337307712401419851800285 13626490392150532444425107)
      ·
        refine ⟨20439735588225798666637661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13626490392150532444425107 20439735588225798666637661)
        ·
          refine ⟨7664900845584674499989123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20439735588225798666637661 7664900845584674499989123)
          ·
            refine ⟨11497351268377011749983685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7664900845584674499989123 11497351268377011749983685)
            ·
              refine ⟨2155753362820689703121941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11497351268377011749983685 2155753362820689703121941)
              ·
                refine ⟨101050938882219829833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2155753362820689703121941 101050938882219829833841)
                ·
                  rfl

theorem cell22_2656746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_2656746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656746 prefixEnd_2656746 := by exact prefixLift 2656746
  have htrace : WordTrace (prefixWord ++ tailWord_2656746) baseStart_2656746 baseEnd_2656746 := by
    simpa [prefixWord, tailWord_2656746, baseEnd_2656746] using wordTrace_append hprefix tailTrace_2656746
  have hstable : (prefixWord ++ tailWord_2656746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656746).length < 2 ^ (prefixWord ++ tailWord_2656746).sum := by decide
  have hdescent : baseEnd_2656746 < baseStart_2656746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656789 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2656789 : Nat := 118140960795 + 2656789 * 2 ^ 59
def prefixEnd_2656789 : Nat := 4983230072969 + 3 ^ 40 * 2656789 * 2
def baseEnd_2656789 : Nat := 909473169718740689679437

theorem tailTrace_2656789 : CollatzResearch.WordTrace tailWord_2656789 prefixEnd_2656789 909473169718740689679437 := by
  unfold tailWord_2656789
  simp only [CollatzResearch.WordTrace]
  refine ⟨96901055571914671281949421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64600703714609780854632947 96901055571914671281949421)
  ·
    refine ⟨36337895839468001730731033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96901055571914671281949421 36337895839468001730731033)
    ·
      refine ⟨27253421879601001298048275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36337895839468001730731033 27253421879601001298048275)
      ·
        refine ⟨40880132819401501947072413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27253421879601001298048275 40880132819401501947072413)
        ·
          refine ⟨15330049807275563230152155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40880132819401501947072413 15330049807275563230152155)
          ·
            refine ⟨22995074710913344845228233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15330049807275563230152155 22995074710913344845228233)
            ·
              refine ⟨17246306033185008633921175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22995074710913344845228233 17246306033185008633921175)
              ·
                refine ⟨25869459049777512950881763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17246306033185008633921175 25869459049777512950881763)
                ·
                  refine ⟨38804188574666269426322645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25869459049777512950881763 38804188574666269426322645)
                  ·
                    refine ⟨909473169718740689679437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38804188574666269426322645 909473169718740689679437)
                    ·
                      rfl

theorem cell22_2656789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2656789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656789 prefixEnd_2656789 := by exact prefixLift 2656789
  have htrace : WordTrace (prefixWord ++ tailWord_2656789) baseStart_2656789 baseEnd_2656789 := by
    simpa [prefixWord, tailWord_2656789, baseEnd_2656789] using wordTrace_append hprefix tailTrace_2656789
  have hstable : (prefixWord ++ tailWord_2656789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656789).length < 2 ^ (prefixWord ++ tailWord_2656789).sum := by decide
  have hdescent : baseEnd_2656789 < baseStart_2656789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656864 : List Nat := [2, 1, 1, 3, 2, 1, 2, 10]
def baseStart_2656864 : Nat := 118140960795 + 2656864 * 2 ^ 59
def prefixEnd_2656864 : Nat := 4983230072969 + 3 ^ 40 * 2656864 * 2
def baseEnd_2656864 : Nat := 101055427083496166006023

theorem tailTrace_2656864 : CollatzResearch.WordTrace tailWord_2656864 prefixEnd_2656864 101055427083496166006023 := by
  unfold tailWord_2656864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48451895523321479545464823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64602527364428639393953097 48451895523321479545464823)
  ·
    refine ⟨72677843284982219318197235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48451895523321479545464823 72677843284982219318197235)
    ·
      refine ⟨109016764927473328977295853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72677843284982219318197235 109016764927473328977295853)
      ·
        refine ⟨40881286847802498366485945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109016764927473328977295853 40881286847802498366485945)
        ·
          refine ⟨30660965135851873774864459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40881286847802498366485945 30660965135851873774864459)
          ·
            refine ⟨45991447703777810662296689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30660965135851873774864459 45991447703777810662296689)
            ·
              refine ⟨34493585777833357996722517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45991447703777810662296689 34493585777833357996722517)
              ·
                refine ⟨101055427083496166006023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34493585777833357996722517 101055427083496166006023)
                ·
                  rfl

theorem cell22_2656864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_2656864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656864 prefixEnd_2656864 := by exact prefixLift 2656864
  have htrace : WordTrace (prefixWord ++ tailWord_2656864) baseStart_2656864 baseEnd_2656864 := by
    simpa [prefixWord, tailWord_2656864, baseEnd_2656864] using wordTrace_append hprefix tailTrace_2656864
  have hstable : (prefixWord ++ tailWord_2656864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656864).length < 2 ^ (prefixWord ++ tailWord_2656864).sum := by decide
  have hdescent : baseEnd_2656864 < baseStart_2656864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656872 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_2656872 : Nat := 118140960795 + 2656872 * 2 ^ 59
def prefixEnd_2656872 : Nat := 4983230072969 + 3 ^ 40 * 2656872 * 2
def baseEnd_2656872 : Nat := 909501582314956139854183

theorem tailTrace_2656872 : CollatzResearch.WordTrace tailWord_2656872 prefixEnd_2656872 909501582314956139854183 := by
  unfold tailWord_2656872
  simp only [CollatzResearch.WordTrace]
  refine ⟨48452041415306988228610435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64602721887075984304813913 48452041415306988228610435)
  ·
    refine ⟨72678062122960482342915653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48452041415306988228610435 72678062122960482342915653)
    ·
      refine ⟨13627136648055090439296685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72678062122960482342915653 13627136648055090439296685)
      ·
        refine ⟨5110176243020658914736257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13627136648055090439296685 5110176243020658914736257)
        ·
          refine ⟨3832632182265494186052193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110176243020658914736257 3832632182265494186052193)
          ·
            refine ⟨2874474136699120639539145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832632182265494186052193 2874474136699120639539145)
            ·
              refine ⟨2155855602524340479654359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874474136699120639539145 2155855602524340479654359)
              ·
                refine ⟨3233783403786510719481539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155855602524340479654359 3233783403786510719481539)
                ·
                  refine ⟨4850675105679766079222309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233783403786510719481539 4850675105679766079222309)
                  ·
                    refine ⟨909501582314956139854183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850675105679766079222309 909501582314956139854183)
                    ·
                      rfl

theorem cell22_2656872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_2656872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656872 prefixEnd_2656872 := by exact prefixLift 2656872
  have htrace : WordTrace (prefixWord ++ tailWord_2656872) baseStart_2656872 baseEnd_2656872 := by
    simpa [prefixWord, tailWord_2656872, baseEnd_2656872] using wordTrace_append hprefix tailTrace_2656872
  have hstable : (prefixWord ++ tailWord_2656872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656872).length < 2 ^ (prefixWord ++ tailWord_2656872).sum := by decide
  have hdescent : baseEnd_2656872 < baseStart_2656872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656885 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2656885 : Nat := 118140960795 + 2656885 * 2 ^ 59
def prefixEnd_2656885 : Nat := 4983230072969 + 3 ^ 40 * 2656885 * 2
def baseEnd_2656885 : Nat := 909506032480628439279143

theorem tailTrace_2656885 : CollatzResearch.WordTrace tailWord_2656885 prefixEnd_2656885 909506032480628439279143 := by
  unfold tailWord_2656885
  simp only [CollatzResearch.WordTrace]
  refine ⟨96904556979566879677444109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64603037986377919784962739 96904556979566879677444109)
  ·
    refine ⟨36339208867337579879041541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96904556979566879677444109 36339208867337579879041541)
    ·
      refine ⟨6813601662625796227320289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36339208867337579879041541 6813601662625796227320289)
      ·
        refine ⟨5110201246969347170490217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6813601662625796227320289 5110201246969347170490217)
        ·
          refine ⟨3832650935227010377867663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110201246969347170490217 3832650935227010377867663)
          ·
            refine ⟨5748976402840515566801495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832650935227010377867663 5748976402840515566801495)
            ·
              refine ⟨8623464604260773350202243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748976402840515566801495 8623464604260773350202243)
              ·
                refine ⟨12935196906391160025303365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623464604260773350202243 12935196906391160025303365)
                ·
                  refine ⟨2425349419948342504744381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12935196906391160025303365 2425349419948342504744381)
                  ·
                    refine ⟨909506032480628439279143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425349419948342504744381 909506032480628439279143)
                    ·
                      rfl

theorem cell22_2656885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2656885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656885 prefixEnd_2656885 := by exact prefixLift 2656885
  have htrace : WordTrace (prefixWord ++ tailWord_2656885) baseStart_2656885 baseEnd_2656885 := by
    simpa [prefixWord, tailWord_2656885, baseEnd_2656885] using wordTrace_append hprefix tailTrace_2656885
  have hstable : (prefixWord ++ tailWord_2656885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656885).length < 2 ^ (prefixWord ++ tailWord_2656885).sum := by decide
  have hdescent : baseEnd_2656885 < baseStart_2656885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656947 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 1, 3]
def baseStart_2656947 : Nat := 118140960795 + 2656947 * 2 ^ 59
def prefixEnd_2656947 : Nat := 4983230072969 + 3 ^ 40 * 2656947 * 2
def baseEnd_2656947 : Nat := 909527256347680944228953

theorem tailTrace_2656947 : CollatzResearch.WordTrace tailWord_2656947 prefixEnd_2656947 909527256347680944228953 := by
  unfold tailWord_2656947
  simp only [CollatzResearch.WordTrace]
  refine ⟨96906818305342264266201095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64604545536894842844134063 96906818305342264266201095)
  ·
    refine ⟨145360227458013396399301643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96906818305342264266201095 145360227458013396399301643)
    ·
      refine ⟨218040341187020094598952465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145360227458013396399301643 218040341187020094598952465)
      ·
        refine ⟨163530255890265070949214349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218040341187020094598952465 163530255890265070949214349)
        ·
          refine ⟨61323845958849401605955381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163530255890265070949214349 61323845958849401605955381)
          ·
            refine ⟨5749110558642131400558317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61323845958849401605955381 5749110558642131400558317)
            ·
              refine ⟨2155916459490799275209369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5749110558642131400558317 2155916459490799275209369)
              ·
                refine ⟨1616937344618099456407027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155916459490799275209369 1616937344618099456407027)
                ·
                  refine ⟨2425406016927149184610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616937344618099456407027 2425406016927149184610541)
                  ·
                    refine ⟨909527256347680944228953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425406016927149184610541 909527256347680944228953)
                    ·
                      rfl

theorem cell22_2656947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 3].length) (baseStart_2656947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656947 prefixEnd_2656947 := by exact prefixLift 2656947
  have htrace : WordTrace (prefixWord ++ tailWord_2656947) baseStart_2656947 baseEnd_2656947 := by
    simpa [prefixWord, tailWord_2656947, baseEnd_2656947] using wordTrace_append hprefix tailTrace_2656947
  have hstable : (prefixWord ++ tailWord_2656947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656947).length < 2 ^ (prefixWord ++ tailWord_2656947).sum := by decide
  have hdescent : baseEnd_2656947 < baseStart_2656947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2656960 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_2656960 : Nat := 118140960795 + 2656960 * 2 ^ 59
def prefixEnd_2656960 : Nat := 4983230072969 + 3 ^ 40 * 2656960 * 2
def baseEnd_2656960 : Nat := 303177235504451081217971

theorem tailTrace_2656960 : CollatzResearch.WordTrace tailWord_2656960 prefixEnd_2656960 303177235504451081217971 := by
  unfold tailWord_2656960
  simp only [CollatzResearch.WordTrace]
  refine ⟨48453646227147583743212167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64604861636196778324282889 48453646227147583743212167)
  ·
    refine ⟨72680469340721375614818251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48453646227147583743212167 72680469340721375614818251)
    ·
      refine ⟨109020704011082063422227377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72680469340721375614818251 109020704011082063422227377)
      ·
        refine ⟨81765528008311547566670533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109020704011082063422227377 81765528008311547566670533)
        ·
          refine ⟨15331036501558415168750725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81765528008311547566670533 15331036501558415168750725)
          ·
            refine ⟨2874569344042202844140761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15331036501558415168750725 2874569344042202844140761)
            ·
              refine ⟨2155927008031652133105571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874569344042202844140761 2155927008031652133105571)
              ·
                refine ⟨3233890512047478199658357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155927008031652133105571 3233890512047478199658357)
                ·
                  refine ⟨303177235504451081217971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3233890512047478199658357 303177235504451081217971)
                  ·
                    rfl

theorem cell22_2656960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_2656960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2656960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2656960 prefixEnd_2656960 := by exact prefixLift 2656960
  have htrace : WordTrace (prefixWord ++ tailWord_2656960) baseStart_2656960 baseEnd_2656960 := by
    simpa [prefixWord, tailWord_2656960, baseEnd_2656960] using wordTrace_append hprefix tailTrace_2656960
  have hstable : (prefixWord ++ tailWord_2656960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2656960).length < 2 ^ (prefixWord ++ tailWord_2656960).sum := by decide
  have hdescent : baseEnd_2656960 < baseStart_2656960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2656960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657005 : List Nat := [1, 5, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2657005 : Nat := 118140960795 + 2657005 * 2 ^ 59
def prefixEnd_2657005 : Nat := 4983230072969 + 3 ^ 40 * 2657005 * 2
def baseEnd_2657005 : Nat := 303182370310996042092925

theorem tailTrace_2657005 : CollatzResearch.WordTrace tailWord_2657005 prefixEnd_2657005 303182370310996042092925 := by
  unfold tailWord_2657005
  simp only [CollatzResearch.WordTrace]
  refine ⟨96908933739132140171812469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64605955826088093447874979 96908933739132140171812469)
  ·
    refine ⟨9085212538043638141107419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96908933739132140171812469 9085212538043638141107419)
    ·
      refine ⟨13627818807065457211661129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085212538043638141107419 13627818807065457211661129)
      ·
        refine ⟨10220864105299092908745847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13627818807065457211661129 10220864105299092908745847)
        ·
          refine ⟨15331296157948639363118771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220864105299092908745847 15331296157948639363118771)
          ·
            refine ⟨22996944236922959044678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15331296157948639363118771 22996944236922959044678157)
            ·
              refine ⟨8623854088846109641754309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22996944236922959044678157 8623854088846109641754309)
              ·
                refine ⟨1616972641658645557828933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8623854088846109641754309 1616972641658645557828933)
                ·
                  refine ⟨303182370310996042092925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616972641658645557828933 303182370310996042092925)
                  ·
                    rfl

theorem cell22_2657005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2657005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657005 prefixEnd_2657005 := by exact prefixLift 2657005
  have htrace : WordTrace (prefixWord ++ tailWord_2657005) baseStart_2657005 baseEnd_2657005 := by
    simpa [prefixWord, tailWord_2657005, baseEnd_2657005] using wordTrace_append hprefix tailTrace_2657005
  have hstable : (prefixWord ++ tailWord_2657005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657005).length < 2 ^ (prefixWord ++ tailWord_2657005).sum := by decide
  have hdescent : baseEnd_2657005 < baseStart_2657005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657020 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2657020 : Nat := 118140960795 + 2657020 * 2 ^ 59
def prefixEnd_2657020 : Nat := 4983230072969 + 3 ^ 40 * 2657020 * 2
def baseEnd_2657020 : Nat := 909552245739533087153729

theorem tailTrace_2657020 : CollatzResearch.WordTrace tailWord_2657020 prefixEnd_2657020 909552245739533087153729 := by
  unfold tailWord_2657020
  simp only [CollatzResearch.WordTrace]
  refine ⟨48454740417038898866804257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64606320556051865155739009 48454740417038898866804257)
  ·
    refine ⟨36341055312779174150103193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48454740417038898866804257 36341055312779174150103193)
    ·
      refine ⟨27255791484584380612577395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36341055312779174150103193 27255791484584380612577395)
      ·
        refine ⟨40883687226876570918866093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27255791484584380612577395 40883687226876570918866093)
        ·
          refine ⟨15331382710078714094574785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40883687226876570918866093 15331382710078714094574785)
          ·
            refine ⟨11498537032559035570931089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15331382710078714094574785 11498537032559035570931089)
            ·
              refine ⟨8623902774419276678198317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11498537032559035570931089 8623902774419276678198317)
              ·
                refine ⟨3233963540407228754324369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8623902774419276678198317 3233963540407228754324369)
                ·
                  refine ⟨2425472655305421565743277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3233963540407228754324369 2425472655305421565743277)
                  ·
                    refine ⟨909552245739533087153729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425472655305421565743277 909552245739533087153729)
                    ·
                      rfl

theorem cell22_2657020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2657020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657020 prefixEnd_2657020 := by exact prefixLift 2657020
  have htrace : WordTrace (prefixWord ++ tailWord_2657020) baseStart_2657020 baseEnd_2657020 := by
    simpa [prefixWord, tailWord_2657020, baseEnd_2657020] using wordTrace_append hprefix tailTrace_2657020
  have hstable : (prefixWord ++ tailWord_2657020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657020).length < 2 ^ (prefixWord ++ tailWord_2657020).sum := by decide
  have hdescent : baseEnd_2657020 < baseStart_2657020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657048 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_2657048 : Nat := 118140960795 + 2657048 * 2 ^ 59
def prefixEnd_2657048 : Nat := 4983230072969 + 3 ^ 40 * 2657048 * 2
def baseEnd_2657048 : Nat := 909561830711750347453643

theorem tailTrace_2657048 : CollatzResearch.WordTrace tailWord_2657048 prefixEnd_2657048 909561830711750347453643 := by
  unfold tailWord_2657048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48455251038988179257813899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64607001385317572343751865 48455251038988179257813899)
  ·
    refine ⟨72682876558482268886720849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48455251038988179257813899 72682876558482268886720849)
    ·
      refine ⟨54512157418861701665040637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72682876558482268886720849 54512157418861701665040637)
      ·
        refine ⟨20442059032073138124390239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54512157418861701665040637 20442059032073138124390239)
        ·
          refine ⟨30663088548109707186585359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20442059032073138124390239 30663088548109707186585359)
          ·
            refine ⟨45994632822164560779878039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30663088548109707186585359 45994632822164560779878039)
            ·
              refine ⟨68991949233246841169817059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45994632822164560779878039 68991949233246841169817059)
              ·
                refine ⟨103487923849870261754725589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68991949233246841169817059 103487923849870261754725589)
                ·
                  refine ⟨2425498215231334259876381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 103487923849870261754725589 2425498215231334259876381)
                  ·
                    refine ⟨909561830711750347453643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425498215231334259876381 909561830711750347453643)
                    ·
                      rfl

theorem cell22_2657048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_2657048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657048 prefixEnd_2657048 := by exact prefixLift 2657048
  have htrace : WordTrace (prefixWord ++ tailWord_2657048) baseStart_2657048 baseEnd_2657048 := by
    simpa [prefixWord, tailWord_2657048, baseEnd_2657048] using wordTrace_append hprefix tailTrace_2657048
  have hstable : (prefixWord ++ tailWord_2657048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657048).length < 2 ^ (prefixWord ++ tailWord_2657048).sum := by decide
  have hdescent : baseEnd_2657048 < baseStart_2657048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657116 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2657116 : Nat := 118140960795 + 2657116 * 2 ^ 59
def prefixEnd_2657116 : Nat := 4983230072969 + 3 ^ 40 * 2657116 * 2
def baseEnd_2657116 : Nat := 909585108501420836753435

theorem tailTrace_2657116 : CollatzResearch.WordTrace tailWord_2657116 prefixEnd_2657116 909585108501420836753435 := by
  unfold tailWord_2657116
  simp only [CollatzResearch.WordTrace]
  refine ⟨48456491120865003064551601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64608654827820004086068801 48456491120865003064551601)
  ·
    refine ⟨36342368340648752298413701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48456491120865003064551601 36342368340648752298413701)
    ·
      refine ⟨6814194063871641055952569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36342368340648752298413701 6814194063871641055952569)
      ·
        refine ⟨5110645547903730791964427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6814194063871641055952569 5110645547903730791964427)
        ·
          refine ⟨7665968321855596187946641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110645547903730791964427 7665968321855596187946641)
          ·
            refine ⟨5749476241391697140959981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7665968321855596187946641 5749476241391697140959981)
            ·
              refine ⟨2156053590521886427859993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5749476241391697140959981 2156053590521886427859993)
              ·
                refine ⟨1617040192891414820894995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156053590521886427859993 1617040192891414820894995)
                ·
                  refine ⟨2425560289337122231342493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617040192891414820894995 2425560289337122231342493)
                  ·
                    refine ⟨909585108501420836753435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425560289337122231342493 909585108501420836753435)
                    ·
                      rfl

theorem cell22_2657116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2657116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657116 prefixEnd_2657116 := by exact prefixLift 2657116
  have htrace : WordTrace (prefixWord ++ tailWord_2657116) baseStart_2657116 baseEnd_2657116 := by
    simpa [prefixWord, tailWord_2657116, baseEnd_2657116] using wordTrace_append hprefix tailTrace_2657116
  have hstable : (prefixWord ++ tailWord_2657116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657116).length < 2 ^ (prefixWord ++ tailWord_2657116).sum := by decide
  have hdescent : baseEnd_2657116 < baseStart_2657116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657142 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2657142 : Nat := 118140960795 + 2657142 * 2 ^ 59
def prefixEnd_2657142 : Nat := 4983230072969 + 3 ^ 40 * 2657142 * 2
def baseEnd_2657142 : Nat := 909594008832765435603355

theorem tailTrace_2657142 : CollatzResearch.WordTrace tailWord_2657142 prefixEnd_2657142 909594008832765435603355 := by
  unfold tailWord_2657142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057120658727238285596855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64609287026423875046366453 6057120658727238285596855)
  ·
    refine ⟨9085680988090857428395283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6057120658727238285596855 9085680988090857428395283)
    ·
      refine ⟨13628521482136286142592925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085680988090857428395283 13628521482136286142592925)
      ·
        refine ⟨5110695555801107303472347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13628521482136286142592925 5110695555801107303472347)
        ·
          refine ⟨7666043333701660955208521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110695555801107303472347 7666043333701660955208521)
          ·
            refine ⟨5749532500276245716406391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666043333701660955208521 5749532500276245716406391)
            ·
              refine ⟨8624298750414368574609587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749532500276245716406391 8624298750414368574609587)
              ·
                refine ⟨12936448125621552861914381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624298750414368574609587 12936448125621552861914381)
                ·
                  refine ⟨4851168047108082323217893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12936448125621552861914381 4851168047108082323217893)
                  ·
                    refine ⟨909594008832765435603355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851168047108082323217893 909594008832765435603355)
                    ·
                      rfl

theorem cell22_2657142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2657142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657142 prefixEnd_2657142 := by exact prefixLift 2657142
  have htrace : WordTrace (prefixWord ++ tailWord_2657142) baseStart_2657142 baseEnd_2657142 := by
    simpa [prefixWord, tailWord_2657142, baseEnd_2657142] using wordTrace_append hprefix tailTrace_2657142
  have hstable : (prefixWord ++ tailWord_2657142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657142).length < 2 ^ (prefixWord ++ tailWord_2657142).sum := by decide
  have hdescent : baseEnd_2657142 < baseStart_2657142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657185 : List Nat := [1, 2, 3, 4, 1, 1, 3, 7]
def baseStart_2657185 : Nat := 118140960795 + 2657185 * 2 ^ 59
def prefixEnd_2657185 : Nat := 4983230072969 + 3 ^ 40 * 2657185 * 2
def baseEnd_2657185 : Nat := 101067636512391961864247

theorem tailTrace_2657185 : CollatzResearch.WordTrace tailWord_2657185 prefixEnd_2657185 101067636512391961864247 := by
  unfold tailWord_2657185
  simp only [CollatzResearch.WordTrace]
  refine ⟨96915498878480030913365009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64610332585653353942243339 96915498878480030913365009)
  ·
    refine ⟨72686624158860023185023757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96915498878480030913365009 72686624158860023185023757)
    ·
      refine ⟨27257484059572508694383909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72686624158860023185023757 27257484059572508694383909)
      ·
        refine ⟨5110778261169845380196983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27257484059572508694383909 5110778261169845380196983)
        ·
          refine ⟨7666167391754768070295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110778261169845380196983 7666167391754768070295475)
          ·
            refine ⟨11499251087632152105443213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666167391754768070295475 11499251087632152105443213)
            ·
              refine ⟨4312219157862057039541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499251087632152105443213 4312219157862057039541205)
              ·
                refine ⟨101067636512391961864247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4312219157862057039541205 101067636512391961864247)
                ·
                  rfl

theorem cell22_2657185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 7].length) (baseStart_2657185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657185 prefixEnd_2657185 := by exact prefixLift 2657185
  have htrace : WordTrace (prefixWord ++ tailWord_2657185) baseStart_2657185 baseEnd_2657185 := by
    simpa [prefixWord, tailWord_2657185, baseEnd_2657185] using wordTrace_append hprefix tailTrace_2657185
  have hstable : (prefixWord ++ tailWord_2657185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657185).length < 2 ^ (prefixWord ++ tailWord_2657185).sum := by decide
  have hdescent : baseEnd_2657185 < baseStart_2657185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657204 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2657204 : Nat := 118140960795 + 2657204 * 2 ^ 59
def prefixEnd_2657204 : Nat := 4983230072969 + 3 ^ 40 * 2657204 * 2
def baseEnd_2657204 : Nat := 909615232699817940553165

theorem tailTrace_2657204 : CollatzResearch.WordTrace tailWord_2657204 prefixEnd_2657204 909615232699817940553165 := by
  unfold tailWord_2657204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48458095932705598579153333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64610794576940798105537777 48458095932705598579153333)
  ·
    refine ⟨4542946493691149866795625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48458095932705598579153333 4542946493691149866795625)
    ·
      refine ⟨3407209870268362400096719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542946493691149866795625 3407209870268362400096719)
      ·
        refine ⟨5110814805402543600145079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407209870268362400096719 5110814805402543600145079)
        ·
          refine ⟨7666222208103815400217619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110814805402543600145079 7666222208103815400217619)
          ·
            refine ⟨11499333312155723100326429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666222208103815400217619 11499333312155723100326429)
            ·
              refine ⟨4312249992058396162622411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499333312155723100326429 4312249992058396162622411)
              ·
                refine ⟨6468374988087594243933617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312249992058396162622411 6468374988087594243933617)
                ·
                  refine ⟨4851281241065695682950213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468374988087594243933617 4851281241065695682950213)
                  ·
                    refine ⟨909615232699817940553165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851281241065695682950213 909615232699817940553165)
                    ·
                      rfl

theorem cell22_2657204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2657204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657204 prefixEnd_2657204 := by exact prefixLift 2657204
  have htrace : WordTrace (prefixWord ++ tailWord_2657204) baseStart_2657204 baseEnd_2657204 := by
    simpa [prefixWord, tailWord_2657204, baseEnd_2657204] using wordTrace_append hprefix tailTrace_2657204
  have hstable : (prefixWord ++ tailWord_2657204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657204).length < 2 ^ (prefixWord ++ tailWord_2657204).sum := by decide
  have hdescent : baseEnd_2657204 < baseStart_2657204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657230 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2657230 : Nat := 118140960795 + 2657230 * 2 ^ 59
def prefixEnd_2657230 : Nat := 4983230072969 + 3 ^ 40 * 2657230 * 2
def baseEnd_2657230 : Nat := 303208044343720846467695

theorem tailTrace_2657230 : CollatzResearch.WordTrace tailWord_2657230 prefixEnd_2657230 303208044343720846467695 := by
  unfold tailWord_2657230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114642520414625449844143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64611426775544669065835429 12114642520414625449844143)
  ·
    refine ⟨18171963780621938174766215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12114642520414625449844143 18171963780621938174766215)
    ·
      refine ⟨27257945670932907262149323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18171963780621938174766215 27257945670932907262149323)
      ·
        refine ⟨40886918506399360893223985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27257945670932907262149323 40886918506399360893223985)
        ·
          refine ⟨30665188879799520669917989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40886918506399360893223985 30665188879799520669917989)
          ·
            refine ⟨5749722914962410125609623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30665188879799520669917989 5749722914962410125609623)
            ·
              refine ⟨8624584372443615188414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749722914962410125609623 8624584372443615188414435)
              ·
                refine ⟨12936876558665422782621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624584372443615188414435 12936876558665422782621653)
                ·
                  refine ⟨303208044343720846467695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12936876558665422782621653 303208044343720846467695)
                  ·
                    rfl

theorem cell22_2657230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2657230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657230 prefixEnd_2657230 := by exact prefixLift 2657230
  have htrace : WordTrace (prefixWord ++ tailWord_2657230) baseStart_2657230 baseEnd_2657230 := by
    simpa [prefixWord, tailWord_2657230, baseEnd_2657230] using wordTrace_append hprefix tailTrace_2657230
  have hstable : (prefixWord ++ tailWord_2657230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657230).length < 2 ^ (prefixWord ++ tailWord_2657230).sum := by decide
  have hdescent : baseEnd_2657230 < baseStart_2657230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657234 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2657234 : Nat := 118140960795 + 2657234 * 2 ^ 59
def prefixEnd_2657234 : Nat := 4983230072969 + 3 ^ 40 * 2657234 * 2
def baseEnd_2657234 : Nat := 909625502312907862303073

theorem tailTrace_2657234 : CollatzResearch.WordTrace tailWord_2657234 prefixEnd_2657234 909625502312907862303073 := by
  unfold tailWord_2657234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24229321513825628070474689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64611524036868341521265837 24229321513825628070474689)
  ·
    refine ⟨18171991135369221052856017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24229321513825628070474689 18171991135369221052856017)
    ·
      refine ⟨13628993351526915789642013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18171991135369221052856017 13628993351526915789642013)
      ·
        refine ⟨5110872506822593421115755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13628993351526915789642013 5110872506822593421115755)
        ·
          refine ⟨7666308760233890131673633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110872506822593421115755 7666308760233890131673633)
          ·
            refine ⟨5749731570175417598755225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666308760233890131673633 5749731570175417598755225)
            ·
              refine ⟨4312298677631563199066419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749731570175417598755225 4312298677631563199066419)
              ·
                refine ⟨6468448016447344798599629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312298677631563199066419 6468448016447344798599629)
                ·
                  refine ⟨2425668006167754299474861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6468448016447344798599629 2425668006167754299474861)
                  ·
                    refine ⟨909625502312907862303073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425668006167754299474861 909625502312907862303073)
                    ·
                      rfl

theorem cell22_2657234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2657234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657234 prefixEnd_2657234 := by exact prefixLift 2657234
  have htrace : WordTrace (prefixWord ++ tailWord_2657234) baseStart_2657234 baseEnd_2657234 := by
    simpa [prefixWord, tailWord_2657234, baseEnd_2657234] using wordTrace_append hprefix tailTrace_2657234
  have hstable : (prefixWord ++ tailWord_2657234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657234).length < 2 ^ (prefixWord ++ tailWord_2657234).sum := by decide
  have hdescent : baseEnd_2657234 < baseStart_2657234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657292 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_2657292 : Nat := 118140960795 + 2657292 * 2 ^ 59
def prefixEnd_2657292 : Nat := 4983230072969 + 3 ^ 40 * 2657292 * 2
def baseEnd_2657292 : Nat := 303215118966071681450965

theorem tailTrace_2657292 : CollatzResearch.WordTrace tailWord_2657292 prefixEnd_2657292 303215118966071681450965 := by
  unfold tailWord_2657292
  simp only [CollatzResearch.WordTrace]
  refine ⟨48459700744546194093755065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64612934326061592125006753 48459700744546194093755065)
  ·
    refine ⟨36344775558409645570316299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48459700744546194093755065 36344775558409645570316299)
    ·
      refine ⟨54517163337614468355474449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36344775558409645570316299 54517163337614468355474449)
      ·
        refine ⟨40887872503210851266605837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54517163337614468355474449 40887872503210851266605837)
        ·
          refine ⟨15332952188704069224977189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40887872503210851266605837 15332952188704069224977189)
          ·
            refine ⟨2874928535382012979683223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15332952188704069224977189 2874928535382012979683223)
            ·
              refine ⟨4312392803073019469524835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874928535382012979683223 4312392803073019469524835)
              ·
                refine ⟨6468589204609529204287253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312392803073019469524835 6468589204609529204287253)
                ·
                  refine ⟨303215118966071681450965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6468589204609529204287253 303215118966071681450965)
                  ·
                    rfl

theorem cell22_2657292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_2657292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657292 prefixEnd_2657292 := by exact prefixLift 2657292
  have htrace : WordTrace (prefixWord ++ tailWord_2657292) baseStart_2657292 baseEnd_2657292 := by
    simpa [prefixWord, tailWord_2657292, baseEnd_2657292] using wordTrace_append hprefix tailTrace_2657292
  have hstable : (prefixWord ++ tailWord_2657292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657292).length < 2 ^ (prefixWord ++ tailWord_2657292).sum := by decide
  have hdescent : baseEnd_2657292 < baseStart_2657292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657352 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_2657352 : Nat := 118140960795 + 2657352 * 2 ^ 59
def prefixEnd_2657352 : Nat := 4983230072969 + 3 ^ 40 * 2657352 * 2
def baseEnd_2657352 : Nat := 909665896124394887852711

theorem tailTrace_2657352 : CollatzResearch.WordTrace tailWord_2657352 prefixEnd_2657352 909665896124394887852711 := by
  unfold tailWord_2657352
  simp only [CollatzResearch.WordTrace]
  refine ⟨48460794934437509217347155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64614393245916678956462873 48460794934437509217347155)
  ·
    refine ⟨72691192401656263826020733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48460794934437509217347155 72691192401656263826020733)
    ·
      refine ⟨27259197150621098934757775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72691192401656263826020733 27259197150621098934757775)
      ·
        refine ⟨40888795725931648402136663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27259197150621098934757775 40888795725931648402136663)
        ·
          refine ⟨61333193588897472603204995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40888795725931648402136663 61333193588897472603204995)
          ·
            refine ⟨91999790383346208904807493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61333193588897472603204995 91999790383346208904807493)
            ·
              refine ⟨17249960696877414169651405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91999790383346208904807493 17249960696877414169651405)
              ·
                refine ⟨6468735261329030313619277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17249960696877414169651405 6468735261329030313619277)
                ·
                  refine ⟨2425775722998386367607229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6468735261329030313619277 2425775722998386367607229)
                  ·
                    refine ⟨909665896124394887852711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425775722998386367607229 909665896124394887852711)
                    ·
                      rfl

theorem cell22_2657352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_2657352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657352 prefixEnd_2657352 := by exact prefixLift 2657352
  have htrace : WordTrace (prefixWord ++ tailWord_2657352) baseStart_2657352 baseEnd_2657352 := by
    simpa [prefixWord, tailWord_2657352, baseEnd_2657352] using wordTrace_append hprefix tailTrace_2657352
  have hstable : (prefixWord ++ tailWord_2657352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657352).length < 2 ^ (prefixWord ++ tailWord_2657352).sum := by decide
  have hdescent : baseEnd_2657352 < baseStart_2657352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657373 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2657373 : Nat := 118140960795 + 2657373 * 2 ^ 59
def prefixEnd_2657373 : Nat := 4983230072969 + 3 ^ 40 * 2657373 * 2
def baseEnd_2657373 : Nat := 909673084853557833077647

theorem tailTrace_2657373 : CollatzResearch.WordTrace tailWord_2657373 prefixEnd_2657373 909673084853557833077647 := by
  unfold tailWord_2657373
  simp only [CollatzResearch.WordTrace]
  refine ⟨96922355801798939021208773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64614903867865959347472515 96922355801798939021208773)
  ·
    refine ⟨18172941712837301066476645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96922355801798939021208773 18172941712837301066476645)
    ·
      refine ⟨3407426571156993949964371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18172941712837301066476645 3407426571156993949964371)
      ·
        refine ⟨5111139856735490924946557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407426571156993949964371 5111139856735490924946557)
        ·
          refine ⟨1916677446275809096854959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5111139856735490924946557 1916677446275809096854959)
          ·
            refine ⟨2875016169413713645282439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916677446275809096854959 2875016169413713645282439)
            ·
              refine ⟨4312524254120570467923659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875016169413713645282439 4312524254120570467923659)
              ·
                refine ⟨6468786381180855701885489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312524254120570467923659 6468786381180855701885489)
                ·
                  refine ⟨4851589785885641776414117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468786381180855701885489 4851589785885641776414117)
                  ·
                    refine ⟨909673084853557833077647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851589785885641776414117 909673084853557833077647)
                    ·
                      rfl

theorem cell22_2657373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2657373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657373 prefixEnd_2657373 := by exact prefixLift 2657373
  have htrace : WordTrace (prefixWord ++ tailWord_2657373) baseStart_2657373 baseEnd_2657373 := by
    simpa [prefixWord, tailWord_2657373, baseEnd_2657373] using wordTrace_append hprefix tailTrace_2657373
  have hstable : (prefixWord ++ tailWord_2657373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657373).length < 2 ^ (prefixWord ++ tailWord_2657373).sum := by decide
  have hdescent : baseEnd_2657373 < baseStart_2657373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657380 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_2657380 : Nat := 118140960795 + 2657380 * 2 ^ 59
def prefixEnd_2657380 : Nat := 4983230072969 + 3 ^ 40 * 2657380 * 2
def baseEnd_2657380 : Nat := 909675481096612148152625

theorem tailTrace_2657380 : CollatzResearch.WordTrace tailWord_2657380 prefixEnd_2657380 909675481096612148152625 := by
  unfold tailWord_2657380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461305556386789608356797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64615074075182386144475729 48461305556386789608356797)
  ·
    refine ⟨18172989583645046103133799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48461305556386789608356797 18172989583645046103133799)
    ·
      refine ⟨27259484375467569154700699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18172989583645046103133799 27259484375467569154700699)
      ·
        refine ⟨40889226563201353732051049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27259484375467569154700699 40889226563201353732051049)
        ·
          refine ⟨30666919922401015299038287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40889226563201353732051049 30666919922401015299038287)
          ·
            refine ⟨46000379883601522948557431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30666919922401015299038287 46000379883601522948557431)
            ·
              refine ⟨69000569825402284422836147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46000379883601522948557431 69000569825402284422836147)
              ·
                refine ⟨103500854738103426634254221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69000569825402284422836147 103500854738103426634254221)
                ·
                  refine ⟨38812820526788784987845333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103500854738103426634254221 38812820526788784987845333)
                  ·
                    refine ⟨909675481096612148152625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38812820526788784987845333 909675481096612148152625)
                    ·
                      rfl

theorem cell22_2657380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_2657380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657380 prefixEnd_2657380 := by exact prefixLift 2657380
  have htrace : WordTrace (prefixWord ++ tailWord_2657380) baseStart_2657380 baseEnd_2657380 := by
    simpa [prefixWord, tailWord_2657380, baseEnd_2657380] using wordTrace_append hprefix tailTrace_2657380
  have hstable : (prefixWord ++ tailWord_2657380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657380).length < 2 ^ (prefixWord ++ tailWord_2657380).sum := by decide
  have hdescent : baseEnd_2657380 < baseStart_2657380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657386 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2657386 : Nat := 118140960795 + 2657386 * 2 ^ 59
def prefixEnd_2657386 : Nat := 4983230072969 + 3 ^ 40 * 2657386 * 2
def baseEnd_2657386 : Nat := 909677535019230132502607

theorem tailTrace_2657386 : CollatzResearch.WordTrace tailWord_2657386 prefixEnd_2657386 909677535019230132502607 := by
  unfold tailWord_2657386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24230707487687960560358003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64615219967167894827621341 24230707487687960560358003)
  ·
    refine ⟨36346061231531940840537005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24230707487687960560358003 36346061231531940840537005)
    ·
      refine ⟨13629772961824477815201377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36346061231531940840537005 13629772961824477815201377)
      ·
        refine ⟨10222329721368358361401033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13629772961824477815201377 10222329721368358361401033)
        ·
          refine ⟨7666747291026268771050775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10222329721368358361401033 7666747291026268771050775)
          ·
            refine ⟨11500120936539403156576163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666747291026268771050775 11500120936539403156576163)
            ·
              refine ⟨17250181404809104734864245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500120936539403156576163 17250181404809104734864245)
              ·
                refine ⟨1617204506700853568893523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17250181404809104734864245 1617204506700853568893523)
                ·
                  refine ⟨2425806760051280353340285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617204506700853568893523 2425806760051280353340285)
                  ·
                    refine ⟨909677535019230132502607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425806760051280353340285 909677535019230132502607)
                    ·
                      rfl

theorem cell22_2657386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2657386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657386 prefixEnd_2657386 := by exact prefixLift 2657386
  have htrace : WordTrace (prefixWord ++ tailWord_2657386) baseStart_2657386 baseEnd_2657386 := by
    simpa [prefixWord, tailWord_2657386, baseEnd_2657386] using wordTrace_append hprefix tailTrace_2657386
  have hstable : (prefixWord ++ tailWord_2657386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657386).length < 2 ^ (prefixWord ++ tailWord_2657386).sum := by decide
  have hdescent : baseEnd_2657386 < baseStart_2657386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657416 : List Nat := [2, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_2657416 : Nat := 118140960795 + 2657416 * 2 ^ 59
def prefixEnd_2657416 : Nat := 4983230072969 + 3 ^ 40 * 2657416 * 2
def baseEnd_2657416 : Nat := 303229268210773351417505

theorem tailTrace_2657416 : CollatzResearch.WordTrace tailWord_2657416 prefixEnd_2657416 303229268210773351417505 := by
  unfold tailWord_2657416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461962070321578682512051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64615949427095438243349401 48461962070321578682512051)
  ·
    refine ⟨72692943105482368023768077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48461962070321578682512051 72692943105482368023768077)
    ·
      refine ⟨27259853664555888008913029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72692943105482368023768077 27259853664555888008913029)
      ·
        refine ⟨5111222562104229001671193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27259853664555888008913029 5111222562104229001671193)
        ·
          refine ⟨3833416921578171751253395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5111222562104229001671193 3833416921578171751253395)
          ·
            refine ⟨5750125382367257626880093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833416921578171751253395 5750125382367257626880093)
            ·
              refine ⟨2156297018387721610080035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5750125382367257626880093 2156297018387721610080035)
              ·
                refine ⟨3234445527581582415120053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156297018387721610080035 3234445527581582415120053)
                ·
                  refine ⟨303229268210773351417505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234445527581582415120053 303229268210773351417505)
                  ·
                    rfl

theorem cell22_2657416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_2657416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657416 prefixEnd_2657416 := by exact prefixLift 2657416
  have htrace : WordTrace (prefixWord ++ tailWord_2657416) baseStart_2657416 baseEnd_2657416 := by
    simpa [prefixWord, tailWord_2657416, baseEnd_2657416] using wordTrace_append hprefix tailTrace_2657416
  have hstable : (prefixWord ++ tailWord_2657416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657416).length < 2 ^ (prefixWord ++ tailWord_2657416).sum := by decide
  have hdescent : baseEnd_2657416 < baseStart_2657416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657455 : List Nat := [1, 1, 2, 1, 2, 3, 12]
def baseStart_2657455 : Nat := 118140960795 + 2657455 * 2 ^ 59
def prefixEnd_2657455 : Nat := 4983230072969 + 3 ^ 40 * 2657455 * 2
def baseEnd_2657455 : Nat := 33692635375160627871385

theorem tailTrace_2657455 : CollatzResearch.WordTrace tailWord_2657455 prefixEnd_2657455 33692635375160627871385 := by
  unfold tailWord_2657455
  simp only [CollatzResearch.WordTrace]
  refine ⟨96925346587501867025693819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64616897725001244683795879 96925346587501867025693819)
  ·
    refine ⟨145388019881252800538540729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96925346587501867025693819 145388019881252800538540729)
    ·
      refine ⟨109041014910939600403905547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145388019881252800538540729 109041014910939600403905547)
      ·
        refine ⟨163561522366409400605858321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109041014910939600403905547 163561522366409400605858321)
        ·
          refine ⟨122671141774807050454393741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163561522366409400605858321 122671141774807050454393741)
          ·
            refine ⟨46001678165552643920397653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122671141774807050454393741 46001678165552643920397653)
            ·
              refine ⟨33692635375160627871385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46001678165552643920397653 33692635375160627871385)
              ·
                rfl

theorem cell22_2657455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 12].length) (baseStart_2657455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657455 prefixEnd_2657455 := by exact prefixLift 2657455
  have htrace : WordTrace (prefixWord ++ tailWord_2657455) baseStart_2657455 baseEnd_2657455 := by
    simpa [prefixWord, tailWord_2657455, baseEnd_2657455] using wordTrace_append hprefix tailTrace_2657455
  have hstable : (prefixWord ++ tailWord_2657455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657455).length < 2 ^ (prefixWord ++ tailWord_2657455).sum := by decide
  have hdescent : baseEnd_2657455 < baseStart_2657455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657538 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2657538 : Nat := 118140960795 + 2657538 * 2 ^ 59
def prefixEnd_2657538 : Nat := 4983230072969 + 3 ^ 40 * 2657538 * 2
def baseEnd_2657538 : Nat := 909729567725552402702141

theorem tailTrace_2657538 : CollatzResearch.WordTrace tailWord_2657538 prefixEnd_2657538 909729567725552402702141 := by
  unfold tailWord_2657538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232093461550293050241317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64618915897467448133976845 24232093461550293050241317)
  ·
    refine ⟨4543517524040679946920247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24232093461550293050241317 4543517524040679946920247)
    ·
      refine ⟨6815276286061019920380371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543517524040679946920247 6815276286061019920380371)
      ·
        refine ⟨10222914429091529880570557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815276286061019920380371 10222914429091529880570557)
        ·
          refine ⟨3833592910909323705213959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10222914429091529880570557 3833592910909323705213959)
          ·
            refine ⟨5750389366363985557820939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833592910909323705213959 5750389366363985557820939)
            ·
              refine ⟨8625584049545978336731409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750389366363985557820939 8625584049545978336731409)
              ·
                refine ⟨6469188037159483752548557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625584049545978336731409 6469188037159483752548557)
                ·
                  refine ⟨2425945513934806407205709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6469188037159483752548557 2425945513934806407205709)
                  ·
                    refine ⟨909729567725552402702141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425945513934806407205709 909729567725552402702141)
                    ·
                      rfl

theorem cell22_2657538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2657538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657538 prefixEnd_2657538 := by exact prefixLift 2657538
  have htrace : WordTrace (prefixWord ++ tailWord_2657538) baseStart_2657538 baseEnd_2657538 := by
    simpa [prefixWord, tailWord_2657538, baseEnd_2657538] using wordTrace_append hprefix tailTrace_2657538
  have hstable : (prefixWord ++ tailWord_2657538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657538).length < 2 ^ (prefixWord ++ tailWord_2657538).sum := by decide
  have hdescent : baseEnd_2657538 < baseStart_2657538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657568 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_2657568 : Nat := 118140960795 + 2657568 * 2 ^ 59
def prefixEnd_2657568 : Nat := 4983230072969 + 3 ^ 40 * 2657568 * 2
def baseEnd_2657568 : Nat := 303246612446214108150683

theorem tailTrace_2657568 : CollatzResearch.WordTrace tailWord_2657568 prefixEnd_2657568 303246612446214108150683 := by
  unfold tailWord_2657568
  simp only [CollatzResearch.WordTrace]
  refine ⟨48464734018046243662278679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64619645357394991549704905 48464734018046243662278679)
  ·
    refine ⟨72697101027069365493418019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48464734018046243662278679 72697101027069365493418019)
    ·
      refine ⟨109045651540604048240127029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72697101027069365493418019 109045651540604048240127029)
      ·
        refine ⟨10223029831931629522511909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109045651540604048240127029 10223029831931629522511909)
        ·
          refine ⟨1916818093487180535470983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10223029831931629522511909 1916818093487180535470983)
          ·
            refine ⟨2875227140230770803206475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916818093487180535470983 2875227140230770803206475)
            ·
              refine ⟨4312840710346156204809713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875227140230770803206475 4312840710346156204809713)
              ·
                refine ⟨3234630532759617153607285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4312840710346156204809713 3234630532759617153607285)
                ·
                  refine ⟨303246612446214108150683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234630532759617153607285 303246612446214108150683)
                  ·
                    rfl

theorem cell22_2657568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_2657568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657568 prefixEnd_2657568 := by exact prefixLift 2657568
  have htrace : WordTrace (prefixWord ++ tailWord_2657568) baseStart_2657568 baseEnd_2657568 := by
    simpa [prefixWord, tailWord_2657568, baseEnd_2657568] using wordTrace_append hprefix tailTrace_2657568
  have hstable : (prefixWord ++ tailWord_2657568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657568).length < 2 ^ (prefixWord ++ tailWord_2657568).sum := by decide
  have hdescent : baseEnd_2657568 < baseStart_2657568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657606 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2657606 : Nat := 118140960795 + 2657606 * 2 ^ 59
def prefixEnd_2657606 : Nat := 4983230072969 + 3 ^ 40 * 2657606 * 2
def baseEnd_2657606 : Nat := 909752845515222892001933

theorem tailTrace_2657606 : CollatzResearch.WordTrace tailWord_2657606 prefixEnd_2657606 909752845515222892001933 := by
  unfold tailWord_2657606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029089187811088119201271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64620569339969879876293781 3029089187811088119201271)
  ·
    refine ⟨4543633781716632178801907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029089187811088119201271 4543633781716632178801907)
    ·
      refine ⟨6815450672574948268202861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543633781716632178801907 6815450672574948268202861)
      ·
        refine ⟨2555794002215605600576073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6815450672574948268202861 2555794002215605600576073)
        ·
          refine ⟨1916845501661704200432055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555794002215605600576073 1916845501661704200432055)
          ·
            refine ⟨2875268252492556300648083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916845501661704200432055 2875268252492556300648083)
            ·
              refine ⟨4312902378738834450972125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875268252492556300648083 4312902378738834450972125)
              ·
                refine ⟨1617338392027062919114547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4312902378738834450972125 1617338392027062919114547)
                ·
                  refine ⟨2426007588040594378671821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617338392027062919114547 2426007588040594378671821)
                  ·
                    refine ⟨909752845515222892001933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426007588040594378671821 909752845515222892001933)
                    ·
                      rfl

theorem cell22_2657606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2657606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657606 prefixEnd_2657606 := by exact prefixLift 2657606
  have htrace : WordTrace (prefixWord ++ tailWord_2657606) baseStart_2657606 baseEnd_2657606 := by
    simpa [prefixWord, tailWord_2657606, baseEnd_2657606] using wordTrace_append hprefix tailTrace_2657606
  have hstable : (prefixWord ++ tailWord_2657606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657606).length < 2 ^ (prefixWord ++ tailWord_2657606).sum := by decide
  have hdescent : baseEnd_2657606 < baseStart_2657606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657645 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_2657645 : Nat := 118140960795 + 2657645 * 2 ^ 59
def prefixEnd_2657645 : Nat := 4983230072969 + 3 ^ 40 * 2657645 * 2
def baseEnd_2657645 : Nat := 909766196012239790276813

theorem tailTrace_2657645 : CollatzResearch.WordTrace tailWord_2657645 prefixEnd_2657645 909766196012239790276813 := by
  unfold tailWord_2657645
  simp only [CollatzResearch.WordTrace]
  refine ⟨96932276456813529475110389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64621517637875686316740259 96932276456813529475110389)
  ·
    refine ⟨9087400917826268388291599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96932276456813529475110389 9087400917826268388291599)
    ·
      refine ⟨13631101376739402582437399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087400917826268388291599 13631101376739402582437399)
      ·
        refine ⟨20446652065109103873656099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631101376739402582437399 20446652065109103873656099)
        ·
          refine ⟨30669978097663655810484149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20446652065109103873656099 30669978097663655810484149)
          ·
            refine ⟨2875310446655967732232889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30669978097663655810484149 2875310446655967732232889)
            ·
              refine ⟨2156482834991975799174667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2875310446655967732232889 2156482834991975799174667)
              ·
                refine ⟨3234724252487963698762001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156482834991975799174667 3234724252487963698762001)
                ·
                  refine ⟨2426043189365972774071501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3234724252487963698762001 2426043189365972774071501)
                  ·
                    refine ⟨909766196012239790276813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426043189365972774071501 909766196012239790276813)
                    ·
                      rfl

theorem cell22_2657645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_2657645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657645 prefixEnd_2657645 := by exact prefixLift 2657645
  have htrace : WordTrace (prefixWord ++ tailWord_2657645) baseStart_2657645 baseEnd_2657645 := by
    simpa [prefixWord, tailWord_2657645, baseEnd_2657645] using wordTrace_append hprefix tailTrace_2657645
  have hstable : (prefixWord ++ tailWord_2657645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657645).length < 2 ^ (prefixWord ++ tailWord_2657645).sum := by decide
  have hdescent : baseEnd_2657645 < baseStart_2657645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657699 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_2657699 : Nat := 118140960795 + 2657699 * 2 ^ 59
def prefixEnd_2657699 : Nat := 4983230072969 + 3 ^ 40 * 2657699 * 2
def baseEnd_2657699 : Nat := 909784681315801649426647

theorem tailTrace_2657699 : CollatzResearch.WordTrace tailWord_2657699 prefixEnd_2657699 909784681315801649426647 := by
  unfold tailWord_2657699
  simp only [CollatzResearch.WordTrace]
  refine ⟨96934245998617896697576151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64622830665745264465050767 96934245998617896697576151)
  ·
    refine ⟨145401368997926845046364227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96934245998617896697576151 145401368997926845046364227)
    ·
      refine ⟨218102053496890267569546341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145401368997926845046364227 218102053496890267569546341)
      ·
        refine ⟨40894135030666925169289939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218102053496890267569546341 40894135030666925169289939)
        ·
          refine ⟨61341202546000387753934909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40894135030666925169289939 61341202546000387753934909)
          ·
            refine ⟨23002950954750145407725591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61341202546000387753934909 23002950954750145407725591)
            ·
              refine ⟨34504426432125218111588387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23002950954750145407725591 34504426432125218111588387)
              ·
                refine ⟨51756639648187827167382581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34504426432125218111588387 51756639648187827167382581)
                ·
                  refine ⟨4852184967017608796942117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51756639648187827167382581 4852184967017608796942117)
                  ·
                    refine ⟨909784681315801649426647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4852184967017608796942117 909784681315801649426647)
                    ·
                      rfl

theorem cell22_2657699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_2657699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657699 prefixEnd_2657699 := by exact prefixLift 2657699
  have htrace : WordTrace (prefixWord ++ tailWord_2657699) baseStart_2657699 baseEnd_2657699 := by
    simpa [prefixWord, tailWord_2657699, baseEnd_2657699] using wordTrace_append hprefix tailTrace_2657699
  have hstable : (prefixWord ++ tailWord_2657699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657699).length < 2 ^ (prefixWord ++ tailWord_2657699).sum := by decide
  have hdescent : baseEnd_2657699 < baseStart_2657699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657731 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 4]
def baseStart_2657731 : Nat := 118140960795 + 2657731 * 2 ^ 59
def prefixEnd_2657731 : Nat := 4983230072969 + 3 ^ 40 * 2657731 * 2
def baseEnd_2657731 : Nat := 303265211856588077542183

theorem tailTrace_2657731 : CollatzResearch.WordTrace tailWord_2657731 prefixEnd_2657731 303265211856588077542183 := by
  unfold tailWord_2657731
  simp only [CollatzResearch.WordTrace]
  refine ⟨96935413134501966162741047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64623608756334644108494031 96935413134501966162741047)
  ·
    refine ⟨145403119701752949244111571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96935413134501966162741047 145403119701752949244111571)
    ·
      refine ⟨218104679552629423866167357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145403119701752949244111571 218104679552629423866167357)
      ·
        refine ⟨81789254832236033949812759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218104679552629423866167357 81789254832236033949812759)
        ·
          refine ⟨122683882248354050924719139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81789254832236033949812759 122683882248354050924719139)
          ·
            refine ⟨184025823372531076387078709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122683882248354050924719139 184025823372531076387078709)
            ·
              refine ⟨17252420941174788411288629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184025823372531076387078709 17252420941174788411288629)
              ·
                refine ⟨1617414463235136413558309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17252420941174788411288629 1617414463235136413558309)
                ·
                  refine ⟨303265211856588077542183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617414463235136413558309 303265211856588077542183)
                  ·
                    rfl

theorem cell22_2657731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 4].length) (baseStart_2657731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657731 prefixEnd_2657731 := by exact prefixLift 2657731
  have htrace : WordTrace (prefixWord ++ tailWord_2657731) baseStart_2657731 baseEnd_2657731 := by
    simpa [prefixWord, tailWord_2657731, baseEnd_2657731] using wordTrace_append hprefix tailTrace_2657731
  have hstable : (prefixWord ++ tailWord_2657731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657731).length < 2 ^ (prefixWord ++ tailWord_2657731).sum := by decide
  have hdescent : baseEnd_2657731 < baseStart_2657731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657748 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_2657748 : Nat := 118140960795 + 2657748 * 2 ^ 59
def prefixEnd_2657748 : Nat := 4983230072969 + 3 ^ 40 * 2657748 * 2
def baseEnd_2657748 : Nat := 303267151672393951650499

theorem tailTrace_2657748 : CollatzResearch.WordTrace tailWord_2657748 prefixEnd_2657748 303267151672393951650499 := by
  unfold tailWord_2657748
  simp only [CollatzResearch.WordTrace]
  refine ⟨48468016587720189033054949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64624022116960252044073265 48468016587720189033054949)
  ·
    refine ⟨9087753110197535443697803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48468016587720189033054949 9087753110197535443697803)
    ·
      refine ⟨13631629665296303165546705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087753110197535443697803 13631629665296303165546705)
      ·
        refine ⟨10223722248972227374160029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13631629665296303165546705 10223722248972227374160029)
        ·
          refine ⟨3833895843364585265310011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10223722248972227374160029 3833895843364585265310011)
          ·
            refine ⟨5750843765046877897965017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833895843364585265310011 5750843765046877897965017)
            ·
              refine ⟨4313132823785158423473763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5750843765046877897965017 4313132823785158423473763)
              ·
                refine ⟨6469699235677737635210645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313132823785158423473763 6469699235677737635210645)
                ·
                  refine ⟨303267151672393951650499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6469699235677737635210645 303267151672393951650499)
                  ·
                    rfl

theorem cell22_2657748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_2657748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657748 prefixEnd_2657748 := by exact prefixLift 2657748
  have htrace : WordTrace (prefixWord ++ tailWord_2657748) baseStart_2657748 baseEnd_2657748 := by
    simpa [prefixWord, tailWord_2657748, baseEnd_2657748] using wordTrace_append hprefix tailTrace_2657748
  have hstable : (prefixWord ++ tailWord_2657748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657748).length < 2 ^ (prefixWord ++ tailWord_2657748).sum := by decide
  have hdescent : baseEnd_2657748 < baseStart_2657748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657759 : List Nat := [1, 1, 2, 3, 3, 1, 2, 9]
def baseStart_2657759 : Nat := 118140960795 + 2657759 * 2 ^ 59
def prefixEnd_2657759 : Nat := 4983230072969 + 3 ^ 40 * 2657759 * 2
def baseEnd_2657759 : Nat := 101089468949109054769607

theorem tailTrace_2657759 : CollatzResearch.WordTrace tailWord_2657759 prefixEnd_2657759 101089468949109054769607 := by
  unfold tailWord_2657759
  simp only [CollatzResearch.WordTrace]
  refine ⟨96936434378400526944760331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64624289585600351296506887 96936434378400526944760331)
  ·
    refine ⟨145404651567600790417140497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96936434378400526944760331 145404651567600790417140497)
    ·
      refine ⟨109053488675700592812855373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145404651567600790417140497 109053488675700592812855373)
      ·
        refine ⟨40895058253387722304820765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109053488675700592812855373 40895058253387722304820765)
        ·
          refine ⟨15335646845020395864307787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40895058253387722304820765 15335646845020395864307787)
          ·
            refine ⟨23003470267530593796461681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15335646845020395864307787 23003470267530593796461681)
            ·
              refine ⟨17252602700647945347346261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23003470267530593796461681 17252602700647945347346261)
              ·
                refine ⟨101089468949109054769607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17252602700647945347346261 101089468949109054769607)
                ·
                  rfl

theorem cell22_2657759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 9].length) (baseStart_2657759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657759 prefixEnd_2657759 := by exact prefixLift 2657759
  have htrace : WordTrace (prefixWord ++ tailWord_2657759) baseStart_2657759 baseEnd_2657759 := by
    simpa [prefixWord, tailWord_2657759, baseEnd_2657759] using wordTrace_append hprefix tailTrace_2657759
  have hstable : (prefixWord ++ tailWord_2657759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657759).length < 2 ^ (prefixWord ++ tailWord_2657759).sum := by decide
  have hdescent : baseEnd_2657759 < baseStart_2657759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657763 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 5]
def baseStart_2657763 : Nat := 118140960795 + 2657763 * 2 ^ 59
def prefixEnd_2657763 : Nat := 4983230072969 + 3 ^ 40 * 2657763 * 2
def baseEnd_2657763 : Nat := 909806589823726815826451

theorem tailTrace_2657763 : CollatzResearch.WordTrace tailWord_2657763 prefixEnd_2657763 909806589823726815826451 := by
  unfold tailWord_2657763
  simp only [CollatzResearch.WordTrace]
  refine ⟨96936580270386035627905943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64624386846924023751937295 96936580270386035627905943)
  ·
    refine ⟨145404870405579053441858915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96936580270386035627905943 145404870405579053441858915)
    ·
      refine ⟨218107305608368580162788373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145404870405579053441858915 218107305608368580162788373)
      ·
        refine ⟨10223779950392277195130705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218107305608368580162788373 10223779950392277195130705)
        ·
          refine ⟨7667834962794207896348029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223779950392277195130705 7667834962794207896348029)
          ·
            refine ⟨2875438111047827961130511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7667834962794207896348029 2875438111047827961130511)
            ·
              refine ⟨4313157166571741941695767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875438111047827961130511 4313157166571741941695767)
              ·
                refine ⟨6469735749857612912543651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313157166571741941695767 6469735749857612912543651)
                ·
                  refine ⟨9704603624786419368815477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469735749857612912543651 9704603624786419368815477)
                  ·
                    refine ⟨909806589823726815826451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9704603624786419368815477 909806589823726815826451)
                    ·
                      rfl

theorem cell22_2657763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].length) (baseStart_2657763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657763 prefixEnd_2657763 := by exact prefixLift 2657763
  have htrace : WordTrace (prefixWord ++ tailWord_2657763) baseStart_2657763 baseEnd_2657763 := by
    simpa [prefixWord, tailWord_2657763, baseEnd_2657763] using wordTrace_append hprefix tailTrace_2657763
  have hstable : (prefixWord ++ tailWord_2657763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657763).length < 2 ^ (prefixWord ++ tailWord_2657763).sum := by decide
  have hdescent : baseEnd_2657763 < baseStart_2657763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657776 : List Nat := [2, 1, 1, 1, 3, 4, 4, 6]
def baseStart_2657776 : Nat := 118140960795 + 2657776 * 2 ^ 59
def prefixEnd_2657776 : Nat := 4983230072969 + 3 ^ 40 * 2657776 * 2
def baseEnd_2657776 : Nat := 101090115554377679472379

theorem tailTrace_2657776 : CollatzResearch.WordTrace tailWord_2657776 prefixEnd_2657776 101090115554377679472379 := by
  unfold tailWord_2657776
  simp only [CollatzResearch.WordTrace]
  refine ⟨48468527209669469424064591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64624702946225959232086121 48468527209669469424064591)
  ·
    refine ⟨72702790814504204136096887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48468527209669469424064591 72702790814504204136096887)
    ·
      refine ⟨109054186221756306204145331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72702790814504204136096887 109054186221756306204145331)
      ·
        refine ⟨163581279332634459306217997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109054186221756306204145331 163581279332634459306217997)
        ·
          refine ⟨61342979749737922239831749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163581279332634459306217997 61342979749737922239831749)
          ·
            refine ⟨11501808703075860419968453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61342979749737922239831749 11501808703075860419968453)
            ·
              refine ⟨2156589131826723828744085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11501808703075860419968453 2156589131826723828744085)
              ·
                refine ⟨101090115554377679472379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2156589131826723828744085 101090115554377679472379)
                ·
                  rfl

theorem cell22_2657776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_2657776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657776 prefixEnd_2657776 := by exact prefixLift 2657776
  have htrace : WordTrace (prefixWord ++ tailWord_2657776) baseStart_2657776 baseEnd_2657776 := by
    simpa [prefixWord, tailWord_2657776, baseEnd_2657776] using wordTrace_append hprefix tailTrace_2657776
  have hstable : (prefixWord ++ tailWord_2657776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657776).length < 2 ^ (prefixWord ++ tailWord_2657776).sum := by decide
  have hdescent : baseEnd_2657776 < baseStart_2657776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657793 : List Nat := [1, 2, 4, 1, 5, 1, 8]
def baseStart_2657793 : Nat := 118140960795 + 2657793 * 2 ^ 59
def prefixEnd_2657793 : Nat := 4983230072969 + 3 ^ 40 * 2657793 * 2
def baseEnd_2657793 : Nat := 33696920719882101391717

theorem tailTrace_2657793 : CollatzResearch.WordTrace tailWord_2657793 prefixEnd_2657793 33696920719882101391717 := by
  unfold tailWord_2657793
  simp only [CollatzResearch.WordTrace]
  refine ⟨96937674460277350751498033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64625116306851567167665355 96937674460277350751498033)
  ·
    refine ⟨72703255845208013063623525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96937674460277350751498033 72703255845208013063623525)
    ·
      refine ⟨13631860470976502449429411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72703255845208013063623525 13631860470976502449429411)
      ·
        refine ⟨20447790706464753674144117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631860470976502449429411 20447790706464753674144117)
        ·
          refine ⟨1916980378731070656951011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20447790706464753674144117 1916980378731070656951011)
          ·
            refine ⟨2875470568096605985426517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916980378731070656951011 2875470568096605985426517)
            ·
              refine ⟨33696920719882101391717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2875470568096605985426517 33696920719882101391717)
              ·
                rfl

theorem cell22_2657793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 8].length) (baseStart_2657793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657793 prefixEnd_2657793 := by exact prefixLift 2657793
  have htrace : WordTrace (prefixWord ++ tailWord_2657793) baseStart_2657793 baseEnd_2657793 := by
    simpa [prefixWord, tailWord_2657793, baseEnd_2657793] using wordTrace_append hprefix tailTrace_2657793
  have hstable : (prefixWord ++ tailWord_2657793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657793).length < 2 ^ (prefixWord ++ tailWord_2657793).sum := by decide
  have hdescent : baseEnd_2657793 < baseStart_2657793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657866 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_2657866 : Nat := 118140960795 + 2657866 * 2 ^ 59
def prefixEnd_2657866 : Nat := 4983230072969 + 3 ^ 40 * 2657866 * 2
def baseEnd_2657866 : Nat := 303280616276222960167045

theorem tailTrace_2657866 : CollatzResearch.WordTrace tailWord_2657866 prefixEnd_2657866 303280616276222960167045 := by
  unfold tailWord_2657866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24235084247253221054726363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64626891326008589479270301 24235084247253221054726363)
  ·
    refine ⟨36352626370879831582089545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24235084247253221054726363 36352626370879831582089545)
    ·
      refine ⟨27264469778159873686567159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36352626370879831582089545 27264469778159873686567159)
      ·
        refine ⟨40896704667239810529850739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27264469778159873686567159 40896704667239810529850739)
        ·
          refine ⟨61345057000859715794776109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40896704667239810529850739 61345057000859715794776109)
          ·
            refine ⟨23004396375322393423041041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61345057000859715794776109 23004396375322393423041041)
            ·
              refine ⟨17253297281491795067280781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23004396375322393423041041 17253297281491795067280781)
              ·
                refine ⟨6469986480559423150230293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17253297281491795067280781 6469986480559423150230293)
                ·
                  refine ⟨303280616276222960167045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6469986480559423150230293 303280616276222960167045)
                  ·
                    rfl

theorem cell22_2657866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_2657866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657866 prefixEnd_2657866 := by exact prefixLift 2657866
  have htrace : WordTrace (prefixWord ++ tailWord_2657866) baseStart_2657866 baseEnd_2657866 := by
    simpa [prefixWord, tailWord_2657866, baseEnd_2657866] using wordTrace_append hprefix tailTrace_2657866
  have hstable : (prefixWord ++ tailWord_2657866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657866).length < 2 ^ (prefixWord ++ tailWord_2657866).sum := by decide
  have hdescent : baseEnd_2657866 < baseStart_2657866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657898 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2657898 : Nat := 118140960795 + 2657898 * 2 ^ 59
def prefixEnd_2657898 : Nat := 4983230072969 + 3 ^ 40 * 2657898 * 2
def baseEnd_2657898 : Nat := 909852803082631463701037

theorem tailTrace_2657898 : CollatzResearch.WordTrace tailWord_2657898 prefixEnd_2657898 909852803082631463701037 := by
  unfold tailWord_2657898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24235376031224238421017587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64627669416597969122713565 24235376031224238421017587)
  ·
    refine ⟨36353064046836357631526381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24235376031224238421017587 36353064046836357631526381)
    ·
      refine ⟨13632399017563634111822393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36353064046836357631526381 13632399017563634111822393)
      ·
        refine ⟨10224299263172725583866795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13632399017563634111822393 10224299263172725583866795)
        ·
          refine ⟨15336448894759088375800193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224299263172725583866795 15336448894759088375800193)
          ·
            refine ⟨11502336671069316281850145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15336448894759088375800193 11502336671069316281850145)
            ·
              refine ⟨8626752503301987211387609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11502336671069316281850145 8626752503301987211387609)
              ·
                refine ⟨6470064377476490408540707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626752503301987211387609 6470064377476490408540707)
                ·
                  refine ⟨9705096566214735612811061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470064377476490408540707 9705096566214735612811061)
                  ·
                    refine ⟨909852803082631463701037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9705096566214735612811061 909852803082631463701037)
                    ·
                      rfl

theorem cell22_2657898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2657898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657898 prefixEnd_2657898 := by exact prefixLift 2657898
  have htrace : WordTrace (prefixWord ++ tailWord_2657898) baseStart_2657898 baseEnd_2657898 := by
    simpa [prefixWord, tailWord_2657898, baseEnd_2657898] using wordTrace_append hprefix tailTrace_2657898
  have hstable : (prefixWord ++ tailWord_2657898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657898).length < 2 ^ (prefixWord ++ tailWord_2657898).sum := by decide
  have hdescent : baseEnd_2657898 < baseStart_2657898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657941 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2657941 : Nat := 118140960795 + 2657941 * 2 ^ 59
def prefixEnd_2657941 : Nat := 4983230072969 + 3 ^ 40 * 2657941 * 2
def baseEnd_2657941 : Nat := 909867522861393684875905

theorem tailTrace_2657941 : CollatzResearch.WordTrace tailWord_2657941 prefixEnd_2657941 909867522861393684875905 := by
  unfold tailWord_2657941
  simp only [CollatzResearch.WordTrace]
  refine ⟨96943072463741172027885677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64628714975827448018590451 96943072463741172027885677)
  ·
    refine ⟨36353652173902939510457129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96943072463741172027885677 36353652173902939510457129)
    ·
      refine ⟨27265239130427204632842847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36353652173902939510457129 27265239130427204632842847)
      ·
        refine ⟨40897858695640806949264271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27265239130427204632842847 40897858695640806949264271)
        ·
          refine ⟨61346788043461210423896407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40897858695640806949264271 61346788043461210423896407)
          ·
            refine ⟨92020182065191815635844611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61346788043461210423896407 92020182065191815635844611)
            ·
              refine ⟨138030273097787723453766917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92020182065191815635844611 138030273097787723453766917)
              ·
                refine ⟨25880676205835198147581297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138030273097787723453766917 25880676205835198147581297)
                ·
                  refine ⟨19410507154376398610685973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25880676205835198147581297 19410507154376398610685973)
                  ·
                    refine ⟨909867522861393684875905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19410507154376398610685973 909867522861393684875905)
                    ·
                      rfl

theorem cell22_2657941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2657941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657941 prefixEnd_2657941 := by exact prefixLift 2657941
  have htrace : WordTrace (prefixWord ++ tailWord_2657941) baseStart_2657941 baseEnd_2657941 := by
    simpa [prefixWord, tailWord_2657941, baseEnd_2657941] using wordTrace_append hprefix tailTrace_2657941
  have hstable : (prefixWord ++ tailWord_2657941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657941).length < 2 ^ (prefixWord ++ tailWord_2657941).sum := by decide
  have hdescent : baseEnd_2657941 < baseStart_2657941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2657988 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2657988 : Nat := 118140960795 + 2657988 * 2 ^ 59
def prefixEnd_2657988 : Nat := 4983230072969 + 3 ^ 40 * 2657988 * 2
def baseEnd_2657988 : Nat := 909883611921901228950761

theorem tailTrace_2657988 : CollatzResearch.WordTrace tailWord_2657988 prefixEnd_2657988 909883611921901228950761 := by
  unfold tailWord_2657988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48472393347285449527423309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64629857796380599369897745 48472393347285449527423309)
  ·
    refine ⟨18177147505232043572783741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48472393347285449527423309 18177147505232043572783741)
    ·
      refine ⟨6816430314462016339793903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18177147505232043572783741 6816430314462016339793903)
      ·
        refine ⟨10224645471693024509690855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816430314462016339793903 10224645471693024509690855)
        ·
          refine ⟨15336968207539536764536283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224645471693024509690855 15336968207539536764536283)
          ·
            refine ⟨23005452311309305146804425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15336968207539536764536283 23005452311309305146804425)
            ·
              refine ⟨17254089233481978860103319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23005452311309305146804425 17254089233481978860103319)
              ·
                refine ⟨25881133850222968290154979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17254089233481978860103319 25881133850222968290154979)
                ·
                  refine ⟨38821700775334452435232469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25881133850222968290154979 38821700775334452435232469)
                  ·
                    refine ⟨909883611921901228950761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38821700775334452435232469 909883611921901228950761)
                    ·
                      rfl

theorem cell22_2657988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2657988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2657988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2657988 prefixEnd_2657988 := by exact prefixLift 2657988
  have htrace : WordTrace (prefixWord ++ tailWord_2657988) baseStart_2657988 baseEnd_2657988 := by
    simpa [prefixWord, tailWord_2657988, baseEnd_2657988] using wordTrace_append hprefix tailTrace_2657988
  have hstable : (prefixWord ++ tailWord_2657988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2657988).length < 2 ^ (prefixWord ++ tailWord_2657988).sum := by decide
  have hdescent : baseEnd_2657988 < baseStart_2657988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2657988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658084 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2658084 : Nat := 118140960795 + 2658084 * 2 ^ 59
def prefixEnd_2658084 : Nat := 4983230072969 + 3 ^ 40 * 2658084 * 2
def baseEnd_2658084 : Nat := 909916474683788978550467

theorem tailTrace_2658084 : CollatzResearch.WordTrace tailWord_2658084 prefixEnd_2658084 909916474683788978550467 := by
  unfold tailWord_2658084
  simp only [CollatzResearch.WordTrace]
  refine ⟨48474144051111553725170653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64632192068148738300227537 48474144051111553725170653)
  ·
    refine ⟨18177804019166832646938995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48474144051111553725170653 18177804019166832646938995)
    ·
      refine ⟨27266706028750248970408493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18177804019166832646938995 27266706028750248970408493)
      ·
        refine ⟨10225014760781343363903185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27266706028750248970408493 10225014760781343363903185)
        ·
          refine ⟨7668761070586007522927389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10225014760781343363903185 7668761070586007522927389)
          ·
            refine ⟨2875785401469752821097771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7668761070586007522927389 2875785401469752821097771)
            ·
              refine ⟨4313678102204629231646657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875785401469752821097771 4313678102204629231646657)
              ·
                refine ⟨3235258576653471923734993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4313678102204629231646657 3235258576653471923734993)
                ·
                  refine ⟨2426443932490103942801245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235258576653471923734993 2426443932490103942801245)
                  ·
                    refine ⟨909916474683788978550467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426443932490103942801245 909916474683788978550467)
                    ·
                      rfl

theorem cell22_2658084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2658084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658084 prefixEnd_2658084 := by exact prefixLift 2658084
  have htrace : WordTrace (prefixWord ++ tailWord_2658084) baseStart_2658084 baseEnd_2658084 := by
    simpa [prefixWord, tailWord_2658084, baseEnd_2658084] using wordTrace_append hprefix tailTrace_2658084
  have hstable : (prefixWord ++ tailWord_2658084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658084).length < 2 ^ (prefixWord ++ tailWord_2658084).sum := by decide
  have hdescent : baseEnd_2658084 < baseStart_2658084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658129 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2658129 : Nat := 118140960795 + 2658129 * 2 ^ 59
def prefixEnd_2658129 : Nat := 4983230072969 + 3 ^ 40 * 2658129 * 2
def baseEnd_2658129 : Nat := 909931879103423861175329

theorem tailTrace_2658129 : CollatzResearch.WordTrace tailWord_2658129 prefixEnd_2658129 909931879103423861175329 := by
  unfold tailWord_2658129
  simp only [CollatzResearch.WordTrace]
  refine ⟨96949929387060080135729441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64633286258040053423819627 96949929387060080135729441)
  ·
    refine ⟨72712447040295060101797081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96949929387060080135729441 72712447040295060101797081)
    ·
      refine ⟨54534335280221295076347811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72712447040295060101797081 54534335280221295076347811)
      ·
        refine ⟨81801502920331942614521717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54534335280221295076347811 81801502920331942614521717)
        ·
          refine ⟨7668890898781119620111411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81801502920331942614521717 7668890898781119620111411)
          ·
            refine ⟨11503336348171679430167117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7668890898781119620111411 11503336348171679430167117)
            ·
              refine ⟨4313751130564379786312669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11503336348171679430167117 4313751130564379786312669)
              ·
                refine ⟨1617656673961642419867251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4313751130564379786312669 1617656673961642419867251)
                ·
                  refine ⟨2426485010942463629800877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617656673961642419867251 2426485010942463629800877)
                  ·
                    refine ⟨909931879103423861175329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426485010942463629800877 909931879103423861175329)
                    ·
                      rfl

theorem cell22_2658129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2658129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658129 prefixEnd_2658129 := by exact prefixLift 2658129
  have htrace : WordTrace (prefixWord ++ tailWord_2658129) baseStart_2658129 baseEnd_2658129 := by
    simpa [prefixWord, tailWord_2658129, baseEnd_2658129] using wordTrace_append hprefix tailTrace_2658129
  have hstable : (prefixWord ++ tailWord_2658129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658129).length < 2 ^ (prefixWord ++ tailWord_2658129).sum := by decide
  have hdescent : baseEnd_2658129 < baseStart_2658129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658185 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_2658185 : Nat := 118140960795 + 2658185 * 2 ^ 59
def prefixEnd_2658185 : Nat := 4983230072969 + 3 ^ 40 * 2658185 * 2
def baseEnd_2658185 : Nat := 909951049047858381775157

theorem tailTrace_2658185 : CollatzResearch.WordTrace tailWord_2658185 prefixEnd_2658185 909951049047858381775157 := by
  unfold tailWord_2658185
  simp only [CollatzResearch.WordTrace]
  refine ⟨96951971874857201699768009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64634647916571467799845339 96951971874857201699768009)
  ·
    refine ⟨72713978906142901274826007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96951971874857201699768009 72713978906142901274826007)
    ·
      refine ⟨109070968359214351912239011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72713978906142901274826007 109070968359214351912239011)
      ·
        refine ⟨163606452538821527868358517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109070968359214351912239011 163606452538821527868358517)
        ·
          refine ⟨15338104925514518237658611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163606452538821527868358517 15338104925514518237658611)
          ·
            refine ⟨23007157388271777356487917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15338104925514518237658611 23007157388271777356487917)
            ·
              refine ⟨8627684020601916508682969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23007157388271777356487917 8627684020601916508682969)
              ·
                refine ⟨6470763015451437381512227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8627684020601916508682969 6470763015451437381512227)
                ·
                  refine ⟨9706144523177156072268341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6470763015451437381512227 9706144523177156072268341)
                  ·
                    refine ⟨909951049047858381775157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9706144523177156072268341 909951049047858381775157)
                    ·
                      rfl

theorem cell22_2658185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_2658185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658185 prefixEnd_2658185 := by exact prefixLift 2658185
  have htrace : WordTrace (prefixWord ++ tailWord_2658185) baseStart_2658185 baseEnd_2658185 := by
    simpa [prefixWord, tailWord_2658185, baseEnd_2658185] using wordTrace_append hprefix tailTrace_2658185
  have hstable : (prefixWord ++ tailWord_2658185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658185).length < 2 ^ (prefixWord ++ tailWord_2658185).sum := by decide
  have hdescent : baseEnd_2658185 < baseStart_2658185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658204 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_2658204 : Nat := 118140960795 + 2658204 * 2 ^ 59
def prefixEnd_2658204 : Nat := 4983230072969 + 3 ^ 40 * 2658204 * 2
def baseEnd_2658204 : Nat := 303319184378716221850033

theorem tailTrace_2658204 : CollatzResearch.WordTrace tailWord_2658204 prefixEnd_2658204 303319184378716221850033 := by
  unfold tailWord_2658204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48476332430894183972354833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64635109907858911963139777 48476332430894183972354833)
  ·
    refine ⟨36357249323170637979266125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48476332430894183972354833 36357249323170637979266125)
    ·
      refine ⟨13633968496188989242224797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36357249323170637979266125 13633968496188989242224797)
      ·
        refine ⟨5112738186070870965834299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13633968496188989242224797 5112738186070870965834299)
        ·
          refine ⟨7669107279106306448751449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5112738186070870965834299 7669107279106306448751449)
          ·
            refine ⟨5751830459329729836563587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7669107279106306448751449 5751830459329729836563587)
            ·
              refine ⟨8627745688994594754845381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751830459329729836563587 8627745688994594754845381)
              ·
                refine ⟨1617702316686486516533509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8627745688994594754845381 1617702316686486516533509)
                ·
                  refine ⟨303319184378716221850033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617702316686486516533509 303319184378716221850033)
                  ·
                    rfl

theorem cell22_2658204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_2658204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658204 prefixEnd_2658204 := by exact prefixLift 2658204
  have htrace : WordTrace (prefixWord ++ tailWord_2658204) baseStart_2658204 baseEnd_2658204 := by
    simpa [prefixWord, tailWord_2658204, baseEnd_2658204] using wordTrace_append hprefix tailTrace_2658204
  have hstable : (prefixWord ++ tailWord_2658204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658204).length < 2 ^ (prefixWord ++ tailWord_2658204).sum := by decide
  have hdescent : baseEnd_2658204 < baseStart_2658204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658264 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_2658264 : Nat := 118140960795 + 2658264 * 2 ^ 59
def prefixEnd_2658264 : Nat := 4983230072969 + 3 ^ 40 * 2658264 * 2
def baseEnd_2658264 : Nat := 909978092362328509049915

theorem tailTrace_2658264 : CollatzResearch.WordTrace tailWord_2658264 prefixEnd_2658264 909978092362328509049915 := by
  unfold tailWord_2658264
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477426620785499095946923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64636568827713998794595897 48477426620785499095946923)
  ·
    refine ⟨72716139931178248643920385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48477426620785499095946923 72716139931178248643920385)
    ·
      refine ⟨54537104948383686482940289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72716139931178248643920385 54537104948383686482940289)
      ·
        refine ⟨40902828711287764862205217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54537104948383686482940289 40902828711287764862205217)
        ·
          refine ⟨30677121533465823646653913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40902828711287764862205217 30677121533465823646653913)
          ·
            refine ⟨23007841150099367734990435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30677121533465823646653913 23007841150099367734990435)
            ·
              refine ⟨34511761725149051602485653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23007841150099367734990435 34511761725149051602485653)
              ·
                refine ⟨1617738830866361793866515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34511761725149051602485653 1617738830866361793866515)
                ·
                  refine ⟨2426608246299542690799773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617738830866361793866515 2426608246299542690799773)
                  ·
                    refine ⟨909978092362328509049915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426608246299542690799773 909978092362328509049915)
                    ·
                      rfl

theorem cell22_2658264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_2658264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658264 prefixEnd_2658264 := by exact prefixLift 2658264
  have htrace : WordTrace (prefixWord ++ tailWord_2658264) baseStart_2658264 baseEnd_2658264 := by
    simpa [prefixWord, tailWord_2658264, baseEnd_2658264] using wordTrace_append hprefix tailTrace_2658264
  have hstable : (prefixWord ++ tailWord_2658264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658264).length < 2 ^ (prefixWord ++ tailWord_2658264).sum := by decide
  have hdescent : baseEnd_2658264 < baseStart_2658264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2658320 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_2658320 : Nat := 118140960795 + 2658320 * 2 ^ 59
def prefixEnd_2658320 : Nat := 4983230072969 + 3 ^ 40 * 2658320 * 2
def baseEnd_2658320 : Nat := 909997262306763029649743

theorem tailTrace_2658320 : CollatzResearch.WordTrace tailWord_2658320 prefixEnd_2658320 909997262306763029649743 := by
  unfold tailWord_2658320
  simp only [CollatzResearch.WordTrace]
  refine ⟨48478447864684059877966207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64637930486245413170621609 48478447864684059877966207)
  ·
    refine ⟨72717671797026089816949311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48478447864684059877966207 72717671797026089816949311)
    ·
      refine ⟨109076507695539134725423967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72717671797026089816949311 109076507695539134725423967)
      ·
        refine ⟨163614761543308702088135951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109076507695539134725423967 163614761543308702088135951)
        ·
          refine ⟨245422142314963053132203927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163614761543308702088135951 245422142314963053132203927)
          ·
            refine ⟨368133213472444579698305891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245422142314963053132203927 368133213472444579698305891)
            ·
              refine ⟨552199820208666869547458837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368133213472444579698305891 552199820208666869547458837)
              ·
                refine ⟨25884366572281259510037133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552199820208666869547458837 25884366572281259510037133)
                ·
                  refine ⟨9706637464605472316263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25884366572281259510037133 9706637464605472316263925)
                  ·
                    refine ⟨909997262306763029649743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9706637464605472316263925 909997262306763029649743)
                    ·
                      rfl

theorem cell22_2658320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_2658320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2658320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2658320 prefixEnd_2658320 := by exact prefixLift 2658320
  have htrace : WordTrace (prefixWord ++ tailWord_2658320) baseStart_2658320 baseEnd_2658320 := by
    simpa [prefixWord, tailWord_2658320, baseEnd_2658320] using wordTrace_append hprefix tailTrace_2658320
  have hstable : (prefixWord ++ tailWord_2658320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2658320).length < 2 ^ (prefixWord ++ tailWord_2658320).sum := by decide
  have hdescent : baseEnd_2658320 < baseStart_2658320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2658320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
