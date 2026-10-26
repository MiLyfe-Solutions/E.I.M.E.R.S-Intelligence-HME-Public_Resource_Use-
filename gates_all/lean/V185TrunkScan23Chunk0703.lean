import V185TrunkScan23Chunk0702

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4156630 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4156630 : Nat := 118140960795 + 4156630 * 2 ^ 59
def prefixEnd_4156630 : Nat := 4983230072969 + 3 ^ 40 * 4156630 * 2
def baseEnd_4156630 : Nat := 2134349092898177399709013

theorem tailTrace_4156630 : CollatzResearch.WordTrace tailWord_4156630 prefixEnd_4156630 2134349092898177399709013 := by
  unfold tailWord_4156630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475296933202930045713209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101069833954164587154274229 9475296933202930045713209)
  ·
    refine ⟨7106472699902197534284907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9475296933202930045713209 7106472699902197534284907)
    ·
      refine ⟨10659709049853296301427361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106472699902197534284907 10659709049853296301427361)
      ·
        refine ⟨7994781787389972226070521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659709049853296301427361 7994781787389972226070521)
        ·
          refine ⟨5996086340542479169552891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994781787389972226070521 5996086340542479169552891)
          ·
            refine ⟨8994129510813718754329337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996086340542479169552891 8994129510813718754329337)
            ·
              refine ⟨6745597133110289065747003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8994129510813718754329337 6745597133110289065747003)
              ·
                refine ⟨10118395699665433598620505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6745597133110289065747003 10118395699665433598620505)
                ·
                  refine ⟨7588796774749075198965379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10118395699665433598620505 7588796774749075198965379)
                  ·
                    refine ⟨11383195162123612798448069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588796774749075198965379 11383195162123612798448069)
                    ·
                      refine ⟨2134349092898177399709013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11383195162123612798448069 2134349092898177399709013)
                      ·
                        rfl

theorem cell23_4156630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4156630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156630 prefixEnd_4156630 := by exact prefixLift 4156630
  have htrace : WordTrace (prefixWord ++ tailWord_4156630) baseStart_4156630 baseEnd_4156630 := by
    simpa [prefixWord, tailWord_4156630, baseEnd_4156630] using wordTrace_append hprefix tailTrace_4156630
  have hstable : (prefixWord ++ tailWord_4156630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156630).length < 2 ^ (prefixWord ++ tailWord_4156630).sum := by decide
  have hdescent : baseEnd_4156630 < baseStart_4156630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_4156663 : Nat := 118140960795 + 4156663 * 2 ^ 59
def prefixEnd_4156663 : Nat := 4983230072969 + 3 ^ 40 * 4156663 * 2
def baseEnd_4156663 : Nat := 2134366037759775770596361

theorem tailTrace_4156663 : CollatzResearch.WordTrace tailWord_4156663 prefixEnd_4156663 2134366037759775770596361 := by
  unfold tailWord_4156663
  simp only [CollatzResearch.WordTrace]
  refine ⟨151605954540127327367362643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101070636360084884911575095 151605954540127327367362643)
  ·
    refine ⟨227408931810190991051043965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151605954540127327367362643 227408931810190991051043965)
    ·
      refine ⟨85278349428821621644141487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227408931810190991051043965 85278349428821621644141487)
      ·
        refine ⟨127917524143232432466212231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85278349428821621644141487 127917524143232432466212231)
        ·
          refine ⟨191876286214848648699318347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127917524143232432466212231 191876286214848648699318347)
          ·
            refine ⟨287814429322272973048977521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191876286214848648699318347 287814429322272973048977521)
            ·
              refine ⟨215860821991704729786733141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287814429322272973048977521 215860821991704729786733141)
              ·
                refine ⟨2529619007715289802188279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 215860821991704729786733141 2529619007715289802188279)
                ·
                  refine ⟨3794428511572934703282419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529619007715289802188279 3794428511572934703282419)
                  ·
                    refine ⟨5691642767359402054923629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794428511572934703282419 5691642767359402054923629)
                    ·
                      refine ⟨2134366037759775770596361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691642767359402054923629 2134366037759775770596361)
                      ·
                        rfl

theorem cell23_4156663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_4156663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156663 prefixEnd_4156663 := by exact prefixLift 4156663
  have htrace : WordTrace (prefixWord ++ tailWord_4156663) baseStart_4156663 baseEnd_4156663 := by
    simpa [prefixWord, tailWord_4156663, baseEnd_4156663] using wordTrace_append hprefix tailTrace_4156663
  have hstable : (prefixWord ++ tailWord_4156663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156663).length < 2 ^ (prefixWord ++ tailWord_4156663).sum := by decide
  have hdescent : baseEnd_4156663 < baseStart_4156663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156686 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4156686 : Nat := 118140960795 + 4156686 * 2 ^ 59
def prefixEnd_4156686 : Nat := 4983230072969 + 3 ^ 40 * 4156686 * 2
def baseEnd_4156686 : Nat := 2134377847814829180608755

theorem tailTrace_4156686 : CollatzResearch.WordTrace tailWord_4156686 prefixEnd_4156686 2134377847814829180608755 := by
  unfold tailWord_4156686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18950849177380500286931239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101071195612696001530299941 18950849177380500286931239)
  ·
    refine ⟨28426273766070750430396859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18950849177380500286931239 28426273766070750430396859)
    ·
      refine ⟨42639410649106125645595289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28426273766070750430396859 42639410649106125645595289)
      ·
        refine ⟨31979557986829594234196467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42639410649106125645595289 31979557986829594234196467)
        ·
          refine ⟨47969336980244391351294701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31979557986829594234196467 47969336980244391351294701)
          ·
            refine ⟨17988501367591646756735513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47969336980244391351294701 17988501367591646756735513)
            ·
              refine ⟨13491376025693735067551635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17988501367591646756735513 13491376025693735067551635)
              ·
                refine ⟨20237064038540602601327453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491376025693735067551635 20237064038540602601327453)
                ·
                  refine ⟨7588899014452725975497795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20237064038540602601327453 7588899014452725975497795)
                  ·
                    refine ⟨11383348521679088963246693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588899014452725975497795 11383348521679088963246693)
                    ·
                      refine ⟨2134377847814829180608755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11383348521679088963246693 2134377847814829180608755)
                      ·
                        rfl

theorem cell23_4156686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4156686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156686 prefixEnd_4156686 := by exact prefixLift 4156686
  have htrace : WordTrace (prefixWord ++ tailWord_4156686) baseStart_4156686 baseEnd_4156686 := by
    simpa [prefixWord, tailWord_4156686, baseEnd_4156686] using wordTrace_append hprefix tailTrace_4156686
  have hstable : (prefixWord ++ tailWord_4156686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156686).length < 2 ^ (prefixWord ++ tailWord_4156686).sum := by decide
  have hdescent : baseEnd_4156686 < baseStart_4156686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156703 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_4156703 : Nat := 118140960795 + 4156703 * 2 ^ 59
def prefixEnd_4156703 : Nat := 4983230072969 + 3 ^ 40 * 4156703 * 2
def baseEnd_4156703 : Nat := 2134386576985955614096177

theorem tailTrace_4156703 : CollatzResearch.WordTrace tailWord_4156703 prefixEnd_4156703 2134386576985955614096177 := by
  unfold tailWord_4156703
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607413459982414198818763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101071608973321609465879175 151607413459982414198818763)
  ·
    refine ⟨227411120189973621298228145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151607413459982414198818763 227411120189973621298228145)
    ·
      refine ⟨170558340142480215973671109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227411120189973621298228145 170558340142480215973671109)
      ·
        refine ⟨31979688776715040495063333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170558340142480215973671109 31979688776715040495063333)
        ·
          refine ⟨5996191645634070092824375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31979688776715040495063333 5996191645634070092824375)
          ·
            refine ⟨8994287468451105139236563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996191645634070092824375 8994287468451105139236563)
            ·
              refine ⟨13491431202676657708854845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994287468451105139236563 13491431202676657708854845)
              ·
                refine ⟨5059286701003746640820567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13491431202676657708854845 5059286701003746640820567)
                ·
                  refine ⟨7588930051505619961230851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059286701003746640820567 7588930051505619961230851)
                  ·
                    refine ⟨11383395077258429941846277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7588930051505619961230851 11383395077258429941846277)
                    ·
                      refine ⟨2134386576985955614096177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11383395077258429941846277 2134386576985955614096177)
                      ·
                        rfl

theorem cell23_4156703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_4156703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156703 prefixEnd_4156703 := by exact prefixLift 4156703
  have htrace : WordTrace (prefixWord ++ tailWord_4156703) baseStart_4156703 baseEnd_4156703 := by
    simpa [prefixWord, tailWord_4156703, baseEnd_4156703] using wordTrace_append hprefix tailTrace_4156703
  have hstable : (prefixWord ++ tailWord_4156703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156703).length < 2 ^ (prefixWord ++ tailWord_4156703).sum := by decide
  have hdescent : baseEnd_4156703 < baseStart_4156703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156709 : List Nat := [1, 3, 1, 2, 4, 2, 10]
def baseStart_4156709 : Nat := 118140960795 + 4156709 * 2 ^ 59
def prefixEnd_4156709 : Nat := 4983230072969 + 3 ^ 40 * 4156709 * 2
def baseEnd_4156709 : Nat := 26350489603331883834829

theorem tailTrace_4156709 : CollatzResearch.WordTrace tailWord_4156709 prefixEnd_4156709 26350489603331883834829 := by
  unfold tailWord_4156709
  simp only [CollatzResearch.WordTrace]
  refine ⟨151607632297960677223537181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101071754865307118149024787 151607632297960677223537181)
  ·
    refine ⟨56852862111735253958826443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151607632297960677223537181 56852862111735253958826443)
    ·
      refine ⟨85279293167602880938239665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56852862111735253958826443 85279293167602880938239665)
      ·
        refine ⟨63959469875702160703679749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85279293167602880938239665 63959469875702160703679749)
        ·
          refine ⟨11992400601694155131939953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63959469875702160703679749 11992400601694155131939953)
          ·
            refine ⟨8994300451270616348954965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11992400601694155131939953 8994300451270616348954965)
            ·
              refine ⟨26350489603331883834829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8994300451270616348954965 26350489603331883834829)
              ·
                rfl

theorem cell23_4156709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 10].length) (baseStart_4156709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156709 prefixEnd_4156709 := by exact prefixLift 4156709
  have htrace : WordTrace (prefixWord ++ tailWord_4156709) baseStart_4156709 baseEnd_4156709 := by
    simpa [prefixWord, tailWord_4156709, baseEnd_4156709] using wordTrace_append hprefix tailTrace_4156709
  have hstable : (prefixWord ++ tailWord_4156709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156709).length < 2 ^ (prefixWord ++ tailWord_4156709).sum := by decide
  have hdescent : baseEnd_4156709 < baseStart_4156709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156720 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 1, 2, 2]
def baseStart_4156720 : Nat := 118140960795 + 4156720 * 2 ^ 59
def prefixEnd_4156720 : Nat := 4983230072969 + 3 ^ 40 * 4156720 * 2
def baseEnd_4156720 : Nat := 2134395306157082047583599

theorem tailTrace_4156720 : CollatzResearch.WordTrace tailWord_4156720 prefixEnd_4156720 2134395306157082047583599 := by
  unfold tailWord_4156720
  simp only [CollatzResearch.WordTrace]
  refine ⟨75804016750460413051093807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101072022333947217401458409 75804016750460413051093807)
  ·
    refine ⟨113706025125690619576640711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75804016750460413051093807 113706025125690619576640711)
    ·
      refine ⟨170559037688535929364961067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113706025125690619576640711 170559037688535929364961067)
      ·
        refine ⟨255838556532803894047441601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170559037688535929364961067 255838556532803894047441601)
        ·
          refine ⟨191878917399602920535581201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255838556532803894047441601 191878917399602920535581201)
          ·
            refine ⟨143909188049702190401685901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191878917399602920535581201 143909188049702190401685901)
            ·
              refine ⟨53965945518638321400632213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143909188049702190401685901 53965945518638321400632213)
              ·
                refine ⟨2529653696186171315654635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53965945518638321400632213 2529653696186171315654635)
                ·
                  refine ⟨3794480544279256973481953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529653696186171315654635 3794480544279256973481953)
                  ·
                    refine ⟨2845860408209442730111465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3794480544279256973481953 2845860408209442730111465)
                    ·
                      refine ⟨2134395306157082047583599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845860408209442730111465 2134395306157082047583599)
                      ·
                        rfl

theorem cell23_4156720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 1, 2, 2].length) (baseStart_4156720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156720 prefixEnd_4156720 := by exact prefixLift 4156720
  have htrace : WordTrace (prefixWord ++ tailWord_4156720) baseStart_4156720 baseEnd_4156720 := by
    simpa [prefixWord, tailWord_4156720, baseEnd_4156720] using wordTrace_append hprefix tailTrace_4156720
  have hstable : (prefixWord ++ tailWord_4156720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156720).length < 2 ^ (prefixWord ++ tailWord_4156720).sum := by decide
  have hdescent : baseEnd_4156720 < baseStart_4156720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156733 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4156733 : Nat := 118140960795 + 4156733 * 2 ^ 59
def prefixEnd_4156733 : Nat := 4983230072969 + 3 ^ 40 * 4156733 * 2
def baseEnd_4156733 : Nat := 2134401981405590496721039

theorem tailTrace_4156733 : CollatzResearch.WordTrace tailWord_4156733 prefixEnd_4156733 2134401981405590496721039 := by
  unfold tailWord_4156733
  simp only [CollatzResearch.WordTrace]
  refine ⟨151608507649873729322410853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101072338433249152881607235 151608507649873729322410853)
  ·
    refine ⟨28426595184351324247952035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151608507649873729322410853 28426595184351324247952035)
    ·
      refine ⟨42639892776526986371928053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28426595184351324247952035 42639892776526986371928053)
      ·
        refine ⟨3997489947799404972368255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42639892776526986371928053 3997489947799404972368255)
        ·
          refine ⟨5996234921699107458552383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997489947799404972368255 5996234921699107458552383)
          ·
            refine ⟨8994352382548661187828575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996234921699107458552383 8994352382548661187828575)
            ·
              refine ⟨13491528573822991781742863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994352382548661187828575 13491528573822991781742863)
              ·
                refine ⟨20237292860734487672614295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491528573822991781742863 20237292860734487672614295)
                ·
                  refine ⟨30355939291101731508921443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20237292860734487672614295 30355939291101731508921443)
                  ·
                    refine ⟨45533908936652597263382165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30355939291101731508921443 45533908936652597263382165)
                    ·
                      refine ⟨2134401981405590496721039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45533908936652597263382165 2134401981405590496721039)
                      ·
                        rfl

theorem cell23_4156733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4156733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156733 prefixEnd_4156733 := by exact prefixLift 4156733
  have htrace : WordTrace (prefixWord ++ tailWord_4156733) baseStart_4156733 baseEnd_4156733 := by
    simpa [prefixWord, tailWord_4156733, baseEnd_4156733] using wordTrace_append hprefix tailTrace_4156733
  have hstable : (prefixWord ++ tailWord_4156733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156733).length < 2 ^ (prefixWord ++ tailWord_4156733).sum := by decide
  have hdescent : baseEnd_4156733 < baseStart_4156733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156740 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4156740 : Nat := 118140960795 + 4156740 * 2 ^ 59
def prefixEnd_4156740 : Nat := 4983230072969 + 3 ^ 40 * 4156740 * 2
def baseEnd_4156740 : Nat := 2134405575770171969333507

theorem tailTrace_4156740 : CollatzResearch.WordTrace tailWord_4156740 prefixEnd_4156740 2134405575770171969333507 := by
  unfold tailWord_4156740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75804381480424184758957837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101072508640565579678610449 75804381480424184758957837)
  ·
    refine ⟨28426643055159069284609189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75804381480424184758957837 28426643055159069284609189)
    ·
      refine ⟨5329995572842325490864223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28426643055159069284609189 5329995572842325490864223)
      ·
        refine ⟨7994993359263488236296335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329995572842325490864223 7994993359263488236296335)
        ·
          refine ⟨11992490038895232354444503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994993359263488236296335 11992490038895232354444503)
          ·
            refine ⟨17988735058342848531666755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11992490038895232354444503 17988735058342848531666755)
            ·
              refine ⟨26983102587514272797500133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17988735058342848531666755 26983102587514272797500133)
              ·
                refine ⟨5059331735158926149531275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26983102587514272797500133 5059331735158926149531275)
                ·
                  refine ⟨7588997602738389224296913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059331735158926149531275 7588997602738389224296913)
                  ·
                    refine ⟨5691748202053791918222685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7588997602738389224296913 5691748202053791918222685)
                    ·
                      refine ⟨2134405575770171969333507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691748202053791918222685 2134405575770171969333507)
                      ·
                        rfl

theorem cell23_4156740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4156740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156740 prefixEnd_4156740 := by exact prefixLift 4156740
  have htrace : WordTrace (prefixWord ++ tailWord_4156740) baseStart_4156740 baseEnd_4156740 := by
    simpa [prefixWord, tailWord_4156740, baseEnd_4156740] using wordTrace_append hprefix tailTrace_4156740
  have hstable : (prefixWord ++ tailWord_4156740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156740).length < 2 ^ (prefixWord ++ tailWord_4156740).sum := by decide
  have hdescent : baseEnd_4156740 < baseStart_4156740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156746 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_4156746 : Nat := 118140960795 + 4156746 * 2 ^ 59
def prefixEnd_4156746 : Nat := 4983230072969 + 3 ^ 40 * 4156746 * 2
def baseEnd_4156746 : Nat := 2134408656654098945858479

theorem tailTrace_4156746 : CollatzResearch.WordTrace tailWord_4156746 prefixEnd_4156746 2134408656654098945858479 := by
  unfold tailWord_4156746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902245449706658135658523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101072654532551088361756061 37902245449706658135658523)
  ·
    refine ⟨56853368174559987203487785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37902245449706658135658523 56853368174559987203487785)
    ·
      refine ⟨42640026130919990402615839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56853368174559987203487785 42640026130919990402615839)
      ·
        refine ⟨63960039196379985603923759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42640026130919990402615839 63960039196379985603923759)
        ·
          refine ⟨95940058794569978405885639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63960039196379985603923759 95940058794569978405885639)
          ·
            refine ⟨143910088191854967608828459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95940058794569978405885639 143910088191854967608828459)
            ·
              refine ⟨215865132287782451413242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143910088191854967608828459 215865132287782451413242689)
              ·
                refine ⟨161898849215836838559932017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215865132287782451413242689 161898849215836838559932017)
                ·
                  refine ⟨121424136911877628919949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161898849215836838559932017 121424136911877628919949013)
                  ·
                    refine ⟨2845878208872131927811305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121424136911877628919949013 2845878208872131927811305)
                    ·
                      refine ⟨2134408656654098945858479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845878208872131927811305 2134408656654098945858479)
                      ·
                        rfl

theorem cell23_4156746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_4156746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156746 prefixEnd_4156746 := by exact prefixLift 4156746
  have htrace : WordTrace (prefixWord ++ tailWord_4156746) baseStart_4156746 baseEnd_4156746 := by
    simpa [prefixWord, tailWord_4156746, baseEnd_4156746] using wordTrace_append hprefix tailTrace_4156746
  have hstable : (prefixWord ++ tailWord_4156746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156746).length < 2 ^ (prefixWord ++ tailWord_4156746).sum := by decide
  have hdescent : baseEnd_4156746 < baseStart_4156746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156769 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4156769 : Nat := 118140960795 + 4156769 * 2 ^ 59
def prefixEnd_4156769 : Nat := 4983230072969 + 3 ^ 40 * 4156769 * 2
def baseEnd_4156769 : Nat := 711473488903050785290291

theorem tailTrace_4156769 : CollatzResearch.WordTrace tailWord_4156769 prefixEnd_4156769 711473488903050785290291 := by
  unfold tailWord_4156769
  simp only [CollatzResearch.WordTrace]
  refine ⟨151609820677743307470721361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101073213785162204980480907 151609820677743307470721361)
  ·
    refine ⟨113707365508307480603041021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151609820677743307470721361 113707365508307480603041021)
    ·
      refine ⟨42640262065615305226140383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113707365508307480603041021 42640262065615305226140383)
      ·
        refine ⟨63960393098422957839210575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42640262065615305226140383 63960393098422957839210575)
        ·
          refine ⟨95940589647634436758815863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63960393098422957839210575 95940589647634436758815863)
          ·
            refine ⟨143910884471451655138223795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95940589647634436758815863 143910884471451655138223795)
            ·
              refine ⟨215866326707177482707335693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143910884471451655138223795 215866326707177482707335693)
              ·
                refine ⟨80949872515191556015250885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215866326707177482707335693 80949872515191556015250885)
                ·
                  refine ⟨15178101096598416752859541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80949872515191556015250885 15178101096598416752859541)
                  ·
                    refine ⟨711473488903050785290291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15178101096598416752859541 711473488903050785290291)
                    ·
                      rfl

theorem cell23_4156769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4156769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156769 prefixEnd_4156769 := by exact prefixLift 4156769
  have htrace : WordTrace (prefixWord ++ tailWord_4156769) baseStart_4156769 baseEnd_4156769 := by
    simpa [prefixWord, tailWord_4156769, baseEnd_4156769] using wordTrace_append hprefix tailTrace_4156769
  have hstable : (prefixWord ++ tailWord_4156769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156769).length < 2 ^ (prefixWord ++ tailWord_4156769).sum := by decide
  have hdescent : baseEnd_4156769 < baseStart_4156769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156770 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4156770 : Nat := 118140960795 + 4156770 * 2 ^ 59
def prefixEnd_4156770 : Nat := 4983230072969 + 3 ^ 40 * 4156770 * 2
def baseEnd_4156770 : Nat := 2134420980189806851958369

theorem tailTrace_4156770 : CollatzResearch.WordTrace tailWord_4156770 prefixEnd_4156770 2134420980189806851958369 := by
  unfold tailWord_4156770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37902464287684921160376941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101073238100493123094338509 37902464287684921160376941)
  ·
    refine ⟨14213424107881845435141353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37902464287684921160376941 14213424107881845435141353)
    ·
      refine ⟨10660068080911384076356015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14213424107881845435141353 10660068080911384076356015)
      ·
        refine ⟨15990102121367076114534023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660068080911384076356015 15990102121367076114534023)
        ·
          refine ⟨23985153182050614171801035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990102121367076114534023 23985153182050614171801035)
          ·
            refine ⟨35977729773075921257701553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23985153182050614171801035 35977729773075921257701553)
            ·
              refine ⟨26983297329806940943276165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35977729773075921257701553 26983297329806940943276165)
              ·
                refine ⟨5059368249338801426864281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26983297329806940943276165 5059368249338801426864281)
                ·
                  refine ⟨3794526187004101070148211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5059368249338801426864281 3794526187004101070148211)
                  ·
                    refine ⟨5691789280506151605222317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794526187004101070148211 5691789280506151605222317)
                    ·
                      refine ⟨2134420980189806851958369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691789280506151605222317 2134420980189806851958369)
                      ·
                        rfl

theorem cell23_4156770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4156770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156770 prefixEnd_4156770 := by exact prefixLift 4156770
  have htrace : WordTrace (prefixWord ++ tailWord_4156770) baseStart_4156770 baseEnd_4156770 := by
    simpa [prefixWord, tailWord_4156770, baseEnd_4156770] using wordTrace_append hprefix tailTrace_4156770
  have hstable : (prefixWord ++ tailWord_4156770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156770).length < 2 ^ (prefixWord ++ tailWord_4156770).sum := by decide
  have hdescent : baseEnd_4156770 < baseStart_4156770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156779 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_4156779 : Nat := 118140960795 + 4156779 * 2 ^ 59
def prefixEnd_4156779 : Nat := 4983230072969 + 3 ^ 40 * 4156779 * 2
def baseEnd_4156779 : Nat := 2134425601515697316745827

theorem tailTrace_4156779 : CollatzResearch.WordTrace tailWord_4156779 prefixEnd_4156779 2134425601515697316745827 := by
  unfold tailWord_4156779
  simp only [CollatzResearch.WordTrace]
  refine ⟨151610185407707079178585391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101073456938471386119056927 151610185407707079178585391)
  ·
    refine ⟨227415278111560618767878087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151610185407707079178585391 227415278111560618767878087)
    ·
      refine ⟨341122917167340928151817131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227415278111560618767878087 341122917167340928151817131)
      ·
        refine ⟨511684375751011392227725697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341122917167340928151817131 511684375751011392227725697)
        ·
          refine ⟨383763281813258544170794273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511684375751011392227725697 383763281813258544170794273)
          ·
            refine ⟨287822461359943908128095705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383763281813258544170794273 287822461359943908128095705)
            ·
              refine ⟨215866846019957931096071779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287822461359943908128095705 215866846019957931096071779)
              ·
                refine ⟨323800269029936896644107669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215866846019957931096071779 323800269029936896644107669)
                ·
                  refine ⟨15178137610778292030192547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323800269029936896644107669 15178137610778292030192547)
                  ·
                    refine ⟨22767206416167438045288821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15178137610778292030192547 22767206416167438045288821)
                    ·
                      refine ⟨2134425601515697316745827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22767206416167438045288821 2134425601515697316745827)
                      ·
                        rfl

theorem cell23_4156779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_4156779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156779 prefixEnd_4156779 := by exact prefixLift 4156779
  have htrace : WordTrace (prefixWord ++ tailWord_4156779) baseStart_4156779 baseEnd_4156779 := by
    simpa [prefixWord, tailWord_4156779, baseEnd_4156779] using wordTrace_append hprefix tailTrace_4156779
  have hstable : (prefixWord ++ tailWord_4156779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156779).length < 2 ^ (prefixWord ++ tailWord_4156779).sum := by decide
  have hdescent : baseEnd_4156779 < baseStart_4156779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156814 : List Nat := [4, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4156814 : Nat := 118140960795 + 4156814 * 2 ^ 59
def prefixEnd_4156814 : Nat := 4983230072969 + 3 ^ 40 * 4156814 * 2
def baseEnd_4156814 : Nat := 2134443573338604679808167

theorem tailTrace_4156814 : CollatzResearch.WordTrace tailWord_4156814 prefixEnd_4156814 2134443573338604679808167 := by
  unfold tailWord_4156814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18951432745322535019513687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101074307975053520104072997 18951432745322535019513687)
  ·
    refine ⟨28427149117983802529270531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18951432745322535019513687 28427149117983802529270531)
    ·
      refine ⟨42640723676975703793905797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28427149117983802529270531 42640723676975703793905797)
      ·
        refine ⟨7995135689432944461357337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42640723676975703793905797 7995135689432944461357337)
        ·
          refine ⟨5996351767074708346018003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995135689432944461357337 5996351767074708346018003)
          ·
            refine ⟨8994527650612062519027005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996351767074708346018003 8994527650612062519027005)
            ·
              refine ⟨3372947868979523444635127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8994527650612062519027005 3372947868979523444635127)
              ·
                refine ⟨5059421803469285166952691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372947868979523444635127 5059421803469285166952691)
                ·
                  refine ⟨7589132705203927750429037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059421803469285166952691 7589132705203927750429037)
                  ·
                    refine ⟨2845924764451472906410889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7589132705203927750429037 2845924764451472906410889)
                    ·
                      refine ⟨2134443573338604679808167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2845924764451472906410889 2134443573338604679808167)
                      ·
                        rfl

theorem cell23_4156814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4156814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156814 prefixEnd_4156814 := by exact prefixLift 4156814
  have htrace : WordTrace (prefixWord ++ tailWord_4156814) baseStart_4156814 baseEnd_4156814 := by
    simpa [prefixWord, tailWord_4156814, baseEnd_4156814] using wordTrace_append hprefix tailTrace_4156814
  have hstable : (prefixWord ++ tailWord_4156814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156814).length < 2 ^ (prefixWord ++ tailWord_4156814).sum := by decide
  have hdescent : baseEnd_4156814 < baseStart_4156814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156840 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4156840 : Nat := 118140960795 + 4156840 * 2 ^ 59
def prefixEnd_4156840 : Nat := 4983230072969 + 3 ^ 40 * 4156840 * 2
def baseEnd_4156840 : Nat := 2134456923835621578083047

theorem tailTrace_4156840 : CollatzResearch.WordTrace tailWord_4156840 prefixEnd_4156840 2134456923835621578083047 := by
  unfold tailWord_4156840
  simp only [CollatzResearch.WordTrace]
  refine ⟨75806205130243043298277987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101074940173657391064370649 75806205130243043298277987)
  ·
    refine ⟨113709307695364564947416981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75806205130243043298277987 113709307695364564947416981)
    ·
      refine ⟨5330123798220213981910171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113709307695364564947416981 5330123798220213981910171)
      ·
        refine ⟨7995185697330320972865257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330123798220213981910171 7995185697330320972865257)
        ·
          refine ⟨5996389272997740729648943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7995185697330320972865257 5996389272997740729648943)
          ·
            refine ⟨8994583909496611094473415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996389272997740729648943 8994583909496611094473415)
            ·
              refine ⟨13491875864244916641710123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994583909496611094473415 13491875864244916641710123)
              ·
                refine ⟨20237813796367374962565185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13491875864244916641710123 20237813796367374962565185)
                ·
                  refine ⟨15178360347275531221923889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20237813796367374962565185 15178360347275531221923889)
                  ·
                    refine ⟨11383770260456648416442917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15178360347275531221923889 11383770260456648416442917)
                    ·
                      refine ⟨2134456923835621578083047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11383770260456648416442917 2134456923835621578083047)
                      ·
                        rfl

theorem cell23_4156840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4156840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156840 prefixEnd_4156840 := by exact prefixLift 4156840
  have htrace : WordTrace (prefixWord ++ tailWord_4156840) baseStart_4156840 baseEnd_4156840 := by
    simpa [prefixWord, tailWord_4156840, baseEnd_4156840] using wordTrace_append hprefix tailTrace_4156840
  have hstable : (prefixWord ++ tailWord_4156840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156840).length < 2 ^ (prefixWord ++ tailWord_4156840).sum := by decide
  have hdescent : baseEnd_4156840 < baseStart_4156840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156903 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4156903 : Nat := 118140960795 + 4156903 * 2 ^ 59
def prefixEnd_4156903 : Nat := 4983230072969 + 3 ^ 40 * 4156903 * 2
def baseEnd_4156903 : Nat := 2134489273116854831595257

theorem tailTrace_4156903 : CollatzResearch.WordTrace tailWord_4156903 prefixEnd_4156903 2134489273116854831595257 := by
  unfold tailWord_4156903
  simp only [CollatzResearch.WordTrace]
  refine ⟨151614708059257848356099363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101076472039505232237399575 151614708059257848356099363)
  ·
    refine ⟨227422062088886772534149045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151614708059257848356099363 227422062088886772534149045)
    ·
      refine ⟨21320818320833134925076473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227422062088886772534149045 21320818320833134925076473)
      ·
        refine ⟨15990613740624851193807355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21320818320833134925076473 15990613740624851193807355)
        ·
          refine ⟨23985920610937276790711033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15990613740624851193807355 23985920610937276790711033)
          ·
            refine ⟨17989440458202957593033275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23985920610937276790711033 17989440458202957593033275)
            ·
              refine ⟨26984160687304436389549913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989440458202957593033275 26984160687304436389549913)
              ·
                refine ⟨20238120515478327292162435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26984160687304436389549913 20238120515478327292162435)
                ·
                  refine ⟨30357180773217490938243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20238120515478327292162435 30357180773217490938243653)
                  ·
                    refine ⟨5691971394978279550920685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30357180773217490938243653 5691971394978279550920685)
                    ·
                      refine ⟨2134489273116854831595257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5691971394978279550920685 2134489273116854831595257)
                      ·
                        rfl

theorem cell23_4156903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4156903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156903 prefixEnd_4156903 := by exact prefixLift 4156903
  have htrace : WordTrace (prefixWord ++ tailWord_4156903) baseStart_4156903 baseEnd_4156903 := by
    simpa [prefixWord, tailWord_4156903, baseEnd_4156903] using wordTrace_append hprefix tailTrace_4156903
  have hstable : (prefixWord ++ tailWord_4156903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156903).length < 2 ^ (prefixWord ++ tailWord_4156903).sum := by decide
  have hdescent : baseEnd_4156903 < baseStart_4156903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4156983 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 6]
def baseStart_4156983 : Nat := 118140960795 + 4156983 * 2 ^ 59
def prefixEnd_4156983 : Nat := 4983230072969 + 3 ^ 40 * 4156983 * 2
def baseEnd_4156983 : Nat := 711510117189738172864963

theorem tailTrace_4156983 : CollatzResearch.WordTrace tailWord_4156983 prefixEnd_4156983 711510117189738172864963 := by
  unfold tailWord_4156983
  simp only [CollatzResearch.WordTrace]
  refine ⟨151617625898968022019011603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101078417265978681346007735 151617625898968022019011603)
  ·
    refine ⟨227426438848452033028517405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151617625898968022019011603 227426438848452033028517405)
    ·
      refine ⟨85284914568169512385694027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227426438848452033028517405 85284914568169512385694027)
      ·
        refine ⟨127927371852254268578541041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85284914568169512385694027 127927371852254268578541041)
        ·
          refine ⟨95945528889190701433905781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127927371852254268578541041 95945528889190701433905781)
          ·
            refine ⟨8994893333361628259428667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95945528889190701433905781 8994893333361628259428667)
            ·
              refine ⟨13492340000042442389143001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8994893333361628259428667 13492340000042442389143001)
              ·
                refine ⟨10119255000031831791857251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492340000042442389143001 10119255000031831791857251)
                ·
                  refine ⟨15178882500047747687785877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119255000031831791857251 15178882500047747687785877)
                  ·
                    refine ⟨711510117189738172864963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15178882500047747687785877 711510117189738172864963)
                    ·
                      rfl

theorem cell23_4156983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_4156983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4156983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4156983 prefixEnd_4156983 := by exact prefixLift 4156983
  have htrace : WordTrace (prefixWord ++ tailWord_4156983) baseStart_4156983 baseEnd_4156983 := by
    simpa [prefixWord, tailWord_4156983, baseEnd_4156983] using wordTrace_append hprefix tailTrace_4156983
  have hstable : (prefixWord ++ tailWord_4156983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4156983).length < 2 ^ (prefixWord ++ tailWord_4156983).sum := by decide
  have hdescent : baseEnd_4156983 < baseStart_4156983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4156983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157010 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4157010 : Nat := 118140960795 + 4157010 * 2 ^ 59
def prefixEnd_4157010 : Nat := 4983230072969 + 3 ^ 40 * 4157010 * 2
def baseEnd_4157010 : Nat := 2134544215546885912957265

theorem tailTrace_4157010 : CollatzResearch.WordTrace tailWord_4157010 prefixEnd_4157010 2134544215546885912957265 := by
  unfold tailWord_4157010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37904652667467551407561121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101079073779913470420162989 37904652667467551407561121)
  ·
    refine ⟨28428489500600663555670841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37904652667467551407561121 28428489500600663555670841)
    ·
      refine ⟨21321367125450497666753131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28428489500600663555670841 21321367125450497666753131)
      ·
        refine ⟨31982050688175746500129697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21321367125450497666753131 31982050688175746500129697)
        ·
          refine ⟨23986538016131809875097273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31982050688175746500129697 23986538016131809875097273)
          ·
            refine ⟨17989903512098857406322955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23986538016131809875097273 17989903512098857406322955)
            ·
              refine ⟨26984855268148286109484433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989903512098857406322955 26984855268148286109484433)
              ·
                refine ⟨20238641451111214582113325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26984855268148286109484433 20238641451111214582113325)
                ·
                  refine ⟨7589490544166705468292497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20238641451111214582113325 7589490544166705468292497)
                  ·
                    refine ⟨5692117908125029101219373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7589490544166705468292497 5692117908125029101219373)
                    ·
                      refine ⟨2134544215546885912957265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692117908125029101219373 2134544215546885912957265)
                      ·
                        rfl

theorem cell23_4157010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4157010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157010 prefixEnd_4157010 := by exact prefixLift 4157010
  have htrace : WordTrace (prefixWord ++ tailWord_4157010) baseStart_4157010 baseEnd_4157010 := by
    simpa [prefixWord, tailWord_4157010, baseEnd_4157010] using wordTrace_append hprefix tailTrace_4157010
  have hstable : (prefixWord ++ tailWord_4157010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157010).length < 2 ^ (prefixWord ++ tailWord_4157010).sum := by decide
  have hdescent : baseEnd_4157010 < baseStart_4157010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157020 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4157020 : Nat := 118140960795 + 4157020 * 2 ^ 59
def prefixEnd_4157020 : Nat := 4983230072969 + 3 ^ 40 * 4157020 * 2
def baseEnd_4157020 : Nat := 2134549350353430873832219

theorem tailTrace_4157020 : CollatzResearch.WordTrace tailWord_4157020 prefixEnd_4157020 2134549350353430873832219 := by
  unfold tailWord_4157020
  simp only [CollatzResearch.WordTrace]
  refine ⟨75809487699916988669054257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101079316933222651558739009 75809487699916988669054257)
  ·
    refine ⟨56857115774937741501790693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75809487699916988669054257 56857115774937741501790693)
    ·
      refine ⟨10660709207800826531585755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56857115774937741501790693 10660709207800826531585755)
      ·
        refine ⟨15991063811701239797378633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660709207800826531585755 15991063811701239797378633)
        ·
          refine ⟨11993297858775929848033975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15991063811701239797378633 11993297858775929848033975)
          ·
            refine ⟨17989946788163894772050963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993297858775929848033975 17989946788163894772050963)
            ·
              refine ⟨26984920182245842158076445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17989946788163894772050963 26984920182245842158076445)
              ·
                refine ⟨10119345068342190809278667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26984920182245842158076445 10119345068342190809278667)
                ·
                  refine ⟨15179017602513286213918001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119345068342190809278667 15179017602513286213918001)
                  ·
                    refine ⟨11384263201884964660438501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15179017602513286213918001 11384263201884964660438501)
                    ·
                      refine ⟨2134549350353430873832219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11384263201884964660438501 2134549350353430873832219)
                      ·
                        rfl

theorem cell23_4157020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4157020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157020 prefixEnd_4157020 := by exact prefixLift 4157020
  have htrace : WordTrace (prefixWord ++ tailWord_4157020) baseStart_4157020 baseEnd_4157020 := by
    simpa [prefixWord, tailWord_4157020, baseEnd_4157020] using wordTrace_append hprefix tailTrace_4157020
  have hstable : (prefixWord ++ tailWord_4157020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157020).length < 2 ^ (prefixWord ++ tailWord_4157020).sum := by decide
  have hdescent : baseEnd_4157020 < baseStart_4157020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157040 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_4157040 : Nat := 118140960795 + 4157040 * 2 ^ 59
def prefixEnd_4157040 : Nat := 4983230072969 + 3 ^ 40 * 4157040 * 2
def baseEnd_4157040 : Nat := 2134559619966520795582127

theorem tailTrace_4157040 : CollatzResearch.WordTrace tailWord_4157040 prefixEnd_4157040 2134559619966520795582127 := by
  unfold tailWord_4157040
  simp only [CollatzResearch.WordTrace]
  refine ⟨75809852429880760376918287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101079803239841013835891049 75809852429880760376918287)
  ·
    refine ⟨113714778644821140565377431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75809852429880760376918287 113714778644821140565377431)
    ·
      refine ⟨170572167967231710848066147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113714778644821140565377431 170572167967231710848066147)
      ·
        refine ⟨255858251950847566272099221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170572167967231710848066147 255858251950847566272099221)
        ·
          refine ⟨11993355560195979669004651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255858251950847566272099221 11993355560195979669004651)
          ·
            refine ⟨17990033340293969503506977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993355560195979669004651 17990033340293969503506977)
            ·
              refine ⟨13492525005220477127630233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17990033340293969503506977 13492525005220477127630233)
              ·
                refine ⟨10119393753915357845722675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13492525005220477127630233 10119393753915357845722675)
                ·
                  refine ⟨15179090630873036768584013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119393753915357845722675 15179090630873036768584013)
                  ·
                    refine ⟨5692158986577388788219005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15179090630873036768584013 5692158986577388788219005)
                    ·
                      refine ⟨2134559619966520795582127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692158986577388788219005 2134559619966520795582127)
                      ·
                        rfl

theorem cell23_4157040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_4157040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157040 prefixEnd_4157040 := by exact prefixLift 4157040
  have htrace : WordTrace (prefixWord ++ tailWord_4157040) baseStart_4157040 baseEnd_4157040 := by
    simpa [prefixWord, tailWord_4157040, baseEnd_4157040] using wordTrace_append hprefix tailTrace_4157040
  have hstable : (prefixWord ++ tailWord_4157040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157040).length < 2 ^ (prefixWord ++ tailWord_4157040).sum := by decide
  have hdescent : baseEnd_4157040 < baseStart_4157040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_4157050 : Nat := 118140960795 + 4157050 * 2 ^ 59
def prefixEnd_4157050 : Nat := 4983230072969 + 3 ^ 40 * 4157050 * 2
def baseEnd_4157050 : Nat := 2134564754773065756457081

theorem tailTrace_4157050 : CollatzResearch.WordTrace tailWord_4157050 prefixEnd_4157050 2134564754773065756457081 := by
  unfold tailWord_4157050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905017397431323115425151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101080046393150194974467069 37905017397431323115425151)
  ·
    refine ⟨56857526096146984673137727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37905017397431323115425151 56857526096146984673137727)
    ·
      refine ⟨85286289144220477009706591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56857526096146984673137727 85286289144220477009706591)
      ·
        refine ⟨127929433716330715514559887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85286289144220477009706591 127929433716330715514559887)
        ·
          refine ⟨191894150574496073271839831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127929433716330715514559887 191894150574496073271839831)
          ·
            refine ⟨287841225861744109907759747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191894150574496073271839831 287841225861744109907759747)
            ·
              refine ⟨431761838792616164861639621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287841225861744109907759747 431761838792616164861639621)
              ·
                refine ⟨80955344773615530911557429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431761838792616164861639621 80955344773615530911557429)
                ·
                  refine ⟨7589563572526456022958509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80955344773615530911557429 7589563572526456022958509)
                  ·
                    refine ⟨2846086339697421008609441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7589563572526456022958509 2846086339697421008609441)
                    ·
                      refine ⟨2134564754773065756457081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846086339697421008609441 2134564754773065756457081)
                      ·
                        rfl

theorem cell23_4157050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_4157050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157050 prefixEnd_4157050 := by exact prefixLift 4157050
  have htrace : WordTrace (prefixWord ++ tailWord_4157050) baseStart_4157050 baseEnd_4157050 := by
    simpa [prefixWord, tailWord_4157050, baseEnd_4157050] using wordTrace_append hprefix tailTrace_4157050
  have hstable : (prefixWord ++ tailWord_4157050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157050).length < 2 ^ (prefixWord ++ tailWord_4157050).sum := by decide
  have hdescent : baseEnd_4157050 < baseStart_4157050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157057 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4157057 : Nat := 118140960795 + 4157057 * 2 ^ 59
def prefixEnd_4157057 : Nat := 4983230072969 + 3 ^ 40 * 4157057 * 2
def baseEnd_4157057 : Nat := 2134568349137647229069549

theorem tailTrace_4157057 : CollatzResearch.WordTrace tailWord_4157057 prefixEnd_4157057 2134568349137647229069549 := by
  unfold tailWord_4157057
  simp only [CollatzResearch.WordTrace]
  refine ⟨151620324900699932657205425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101080216600466621771470283 151620324900699932657205425)
  ·
    refine ⟨113715243675524949492904069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151620324900699932657205425 113715243675524949492904069)
    ·
      refine ⟨21321608189160928029919513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113715243675524949492904069 21321608189160928029919513)
      ·
        refine ⟨15991206141870696022439635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21321608189160928029919513 15991206141870696022439635)
        ·
          refine ⟨23986809212806044033659453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15991206141870696022439635 23986809212806044033659453)
          ·
            refine ⟨8995053454802266512622295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23986809212806044033659453 8995053454802266512622295)
            ·
              refine ⟨13492580182203399768933443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995053454802266512622295 13492580182203399768933443)
              ·
                refine ⟨20238870273305099653400165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13492580182203399768933443 20238870273305099653400165)
                ·
                  refine ⟨3794788176244706185012531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20238870273305099653400165 3794788176244706185012531)
                  ·
                    refine ⟨5692182264367059277518797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794788176244706185012531 5692182264367059277518797)
                    ·
                      refine ⟨2134568349137647229069549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692182264367059277518797 2134568349137647229069549)
                      ·
                        rfl

theorem cell23_4157057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4157057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157057 prefixEnd_4157057 := by exact prefixLift 4157057
  have htrace : WordTrace (prefixWord ++ tailWord_4157057) baseStart_4157057 baseEnd_4157057 := by
    simpa [prefixWord, tailWord_4157057, baseEnd_4157057] using wordTrace_append hprefix tailTrace_4157057
  have hstable : (prefixWord ++ tailWord_4157057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157057).length < 2 ^ (prefixWord ++ tailWord_4157057).sum := by decide
  have hdescent : baseEnd_4157057 < baseStart_4157057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157074 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4157074 : Nat := 118140960795 + 4157074 * 2 ^ 59
def prefixEnd_4157074 : Nat := 4983230072969 + 3 ^ 40 * 4157074 * 2
def baseEnd_4157074 : Nat := 2134577078308773662556971

theorem tailTrace_4157074 : CollatzResearch.WordTrace tailWord_4157074 prefixEnd_4157074 2134577078308773662556971 := by
  unfold tailWord_4157074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905236235409586140143569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101080629961092229707049517 37905236235409586140143569)
  ·
    refine ⟨28428927176557189605107677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37905236235409586140143569 28428927176557189605107677)
    ·
      refine ⟨10660847691208946101915379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28428927176557189605107677 10660847691208946101915379)
      ·
        refine ⟨15991271536813419152873069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10660847691208946101915379 15991271536813419152873069)
        ·
          refine ⟨5996726826305032182327401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15991271536813419152873069 5996726826305032182327401)
          ·
            refine ⟨4497545119728774136745551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5996726826305032182327401 4497545119728774136745551)
            ·
              refine ⟨6746317679593161205118327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497545119728774136745551 6746317679593161205118327)
              ·
                refine ⟨10119476519389741807677491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6746317679593161205118327 10119476519389741807677491)
                ·
                  refine ⟨15179214779084612711516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10119476519389741807677491 15179214779084612711516237)
                  ·
                    refine ⟨5692205542156729766818589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15179214779084612711516237 5692205542156729766818589)
                    ·
                      refine ⟨2134577078308773662556971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692205542156729766818589 2134577078308773662556971)
                      ·
                        rfl

theorem cell23_4157074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4157074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157074 prefixEnd_4157074 := by exact prefixLift 4157074
  have htrace : WordTrace (prefixWord ++ tailWord_4157074) baseStart_4157074 baseEnd_4157074 := by
    simpa [prefixWord, tailWord_4157074, baseEnd_4157074] using wordTrace_append hprefix tailTrace_4157074
  have hstable : (prefixWord ++ tailWord_4157074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157074).length < 2 ^ (prefixWord ++ tailWord_4157074).sum := by decide
  have hdescent : baseEnd_4157074 < baseStart_4157074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157093 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_4157093 : Nat := 118140960795 + 4157093 * 2 ^ 59
def prefixEnd_4157093 : Nat := 4983230072969 + 3 ^ 40 * 4157093 * 2
def baseEnd_4157093 : Nat := 2134586834441209088219383

theorem tailTrace_4157093 : CollatzResearch.WordTrace tailWord_4157093 prefixEnd_4157093 2134586834441209088219383 := by
  unfold tailWord_4157093
  simp only [CollatzResearch.WordTrace]
  refine ⟨151621637928569510805515933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101081091952379673870343955 151621637928569510805515933)
  ·
    refine ⟨56858114223213566552068475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151621637928569510805515933 56858114223213566552068475)
    ·
      refine ⟨85287171334820349828102713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56858114223213566552068475 85287171334820349828102713)
      ·
        refine ⟨63965378501115262371077035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85287171334820349828102713 63965378501115262371077035)
        ·
          refine ⟨95948067751672893556615553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63965378501115262371077035 95948067751672893556615553)
          ·
            refine ⟨71961050813754670167461665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95948067751672893556615553 71961050813754670167461665)
            ·
              refine ⟨53970788110316002625596249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71961050813754670167461665 53970788110316002625596249)
              ·
                refine ⟨40478091082737001969197187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53970788110316002625596249 40478091082737001969197187)
                ·
                  refine ⟨60717136624105502953795781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40478091082737001969197187 60717136624105502953795781)
                  ·
                    refine ⟨11384463117019781803836709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60717136624105502953795781 11384463117019781803836709)
                    ·
                      refine ⟨2134586834441209088219383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11384463117019781803836709 2134586834441209088219383)
                      ·
                        rfl

theorem cell23_4157093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_4157093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157093 prefixEnd_4157093 := by exact prefixLift 4157093
  have htrace : WordTrace (prefixWord ++ tailWord_4157093) baseStart_4157093 baseEnd_4157093 := by
    simpa [prefixWord, tailWord_4157093, baseEnd_4157093] using wordTrace_append hprefix tailTrace_4157093
  have hstable : (prefixWord ++ tailWord_4157093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157093).length < 2 ^ (prefixWord ++ tailWord_4157093).sum := by decide
  have hdescent : baseEnd_4157093 < baseStart_4157093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157143 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_4157143 : Nat := 118140960795 + 4157143 * 2 ^ 59
def prefixEnd_4157143 : Nat := 4983230072969 + 3 ^ 40 * 4157143 * 2
def baseEnd_4157143 : Nat := 2134612508473933892594153

theorem tailTrace_4157143 : CollatzResearch.WordTrace tailWord_4157143 prefixEnd_4157143 2134612508473933892594153 := by
  unfold tailWord_4157143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151623461578388369344836083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101082307718925579563224055 151623461578388369344836083)
  ·
    refine ⟨227435192367582554017254125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151623461578388369344836083 227435192367582554017254125)
    ·
      refine ⟨85288197137843457756470297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227435192367582554017254125 85288197137843457756470297)
      ·
        refine ⟨63966147853382593317352723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85288197137843457756470297 63966147853382593317352723)
        ·
          refine ⟨95949221780073889976029085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63966147853382593317352723 95949221780073889976029085)
          ·
            refine ⟨35980958167527708741010907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95949221780073889976029085 35980958167527708741010907)
            ·
              refine ⟨53971437251291563111516361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35980958167527708741010907 53971437251291563111516361)
              ·
                refine ⟨40478577938468672333637271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53971437251291563111516361 40478577938468672333637271)
                ·
                  refine ⟨60717866907703008500455907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40478577938468672333637271 60717866907703008500455907)
                  ·
                    refine ⟨91076800361554512750683861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60717866907703008500455907 91076800361554512750683861)
                    ·
                      refine ⟨2134612508473933892594153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91076800361554512750683861 2134612508473933892594153)
                      ·
                        rfl

theorem cell23_4157143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_4157143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157143 prefixEnd_4157143 := by exact prefixLift 4157143
  have htrace : WordTrace (prefixWord ++ tailWord_4157143) baseStart_4157143 baseEnd_4157143 := by
    simpa [prefixWord, tailWord_4157143, baseEnd_4157143] using wordTrace_append hprefix tailTrace_4157143
  have hstable : (prefixWord ++ tailWord_4157143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157143).length < 2 ^ (prefixWord ++ tailWord_4157143).sum := by decide
  have hdescent : baseEnd_4157143 < baseStart_4157143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157160 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4157160 : Nat := 118140960795 + 4157160 * 2 ^ 59
def prefixEnd_4157160 : Nat := 4983230072969 + 3 ^ 40 * 4157160 * 2
def baseEnd_4157160 : Nat := 2134621237645060326081575

theorem tailTrace_4157160 : CollatzResearch.WordTrace tailWord_4157160 prefixEnd_4157160 2134621237645060326081575 := by
  unfold tailWord_4157160
  simp only [CollatzResearch.WordTrace]
  refine ⟨75812040809663390624102467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101082721079551187498803289 75812040809663390624102467)
  ·
    refine ⟨113718061214495085936153701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75812040809663390624102467 113718061214495085936153701)
    ·
      refine ⟨21322136477717828613028819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113718061214495085936153701 21322136477717828613028819)
      ·
        refine ⟨31983204716576742919543229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21322136477717828613028819 31983204716576742919543229)
        ·
          refine ⟨11993701768716278594828711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31983204716576742919543229 11993701768716278594828711)
          ·
            refine ⟨17990552653074417892243067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11993701768716278594828711 17990552653074417892243067)
            ·
              refine ⟨26985828979611626838364601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17990552653074417892243067 26985828979611626838364601)
              ·
                refine ⟨20239371734708720128773451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26985828979611626838364601 20239371734708720128773451)
                ·
                  refine ⟨30359057602063080193160177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20239371734708720128773451 30359057602063080193160177)
                  ·
                    refine ⟨22769293201547310144870133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30359057602063080193160177 22769293201547310144870133)
                    ·
                      refine ⟨2134621237645060326081575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22769293201547310144870133 2134621237645060326081575)
                      ·
                        rfl

theorem cell23_4157160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4157160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157160 prefixEnd_4157160 := by exact prefixLift 4157160
  have htrace : WordTrace (prefixWord ++ tailWord_4157160) baseStart_4157160 baseEnd_4157160 := by
    simpa [prefixWord, tailWord_4157160, baseEnd_4157160] using wordTrace_append hprefix tailTrace_4157160
  have hstable : (prefixWord ++ tailWord_4157160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157160).length < 2 ^ (prefixWord ++ tailWord_4157160).sum := by decide
  have hdescent : baseEnd_4157160 < baseStart_4157160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157193 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 10]
def baseStart_4157193 : Nat := 118140960795 + 4157193 * 2 ^ 59
def prefixEnd_4157193 : Nat := 4983230072969 + 3 ^ 40 * 4157193 * 2
def baseEnd_4157193 : Nat := 237182020278517632996547

theorem tailTrace_4157193 : CollatzResearch.WordTrace tailWord_4157193 prefixEnd_4157193 237182020278517632996547 := by
  unfold tailWord_4157193
  simp only [CollatzResearch.WordTrace]
  refine ⟨151625285228207227884156233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101083523485471485256104155 151625285228207227884156233)
  ·
    refine ⟨113718963921155420913117175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151625285228207227884156233 113718963921155420913117175)
    ·
      refine ⟨170578445881733131369675763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113718963921155420913117175 170578445881733131369675763)
      ·
        refine ⟨255867668822599697054513645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170578445881733131369675763 255867668822599697054513645)
        ·
          refine ⟨95950375808474886395442617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255867668822599697054513645 95950375808474886395442617)
          ·
            refine ⟨71962781856356164796581963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95950375808474886395442617 71962781856356164796581963)
            ·
              refine ⟨107944172784534247194872945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71962781856356164796581963 107944172784534247194872945)
              ·
                refine ⟨80958129588400685396154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107944172784534247194872945 80958129588400685396154709)
                ·
                  refine ⟨237182020278517632996547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80958129588400685396154709 237182020278517632996547)
                  ·
                    rfl

theorem cell23_4157193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_4157193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157193 prefixEnd_4157193 := by exact prefixLift 4157193
  have htrace : WordTrace (prefixWord ++ tailWord_4157193) baseStart_4157193 baseEnd_4157193 := by
    simpa [prefixWord, tailWord_4157193, baseEnd_4157193] using wordTrace_append hprefix tailTrace_4157193
  have hstable : (prefixWord ++ tailWord_4157193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157193).length < 2 ^ (prefixWord ++ tailWord_4157193).sum := by decide
  have hdescent : baseEnd_4157193 < baseStart_4157193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157207 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4157207 : Nat := 118140960795 + 4157207 * 2 ^ 59
def prefixEnd_4157207 : Nat := 4983230072969 + 3 ^ 40 * 4157207 * 2
def baseEnd_4157207 : Nat := 2134645371235821642193859

theorem tailTrace_4157207 : CollatzResearch.WordTrace tailWord_4157207 prefixEnd_4157207 2134645371235821642193859 := by
  unfold tailWord_4157207
  simp only [CollatzResearch.WordTrace]
  refine ⟨151625795850156508275165875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101083863900104338850110583 151625795850156508275165875)
  ·
    refine ⟨227438693775234762412748813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151625795850156508275165875 227438693775234762412748813)
    ·
      refine ⟨85289510165713035904780805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227438693775234762412748813 85289510165713035904780805)
      ·
        refine ⟨15991783156071194232146401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85289510165713035904780805 15991783156071194232146401)
        ·
          refine ⟨11993837367053395674109801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15991783156071194232146401 11993837367053395674109801)
          ·
            refine ⟨8995378025290046755582351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11993837367053395674109801 8995378025290046755582351)
            ·
              refine ⟨13493067037935070133373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995378025290046755582351 13493067037935070133373527)
              ·
                refine ⟨20239600556902605200060291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493067037935070133373527 20239600556902605200060291)
                ·
                  refine ⟨30359400835353907800090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20239600556902605200060291 30359400835353907800090437)
                  ·
                    refine ⟨5692387656628857712516957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30359400835353907800090437 5692387656628857712516957)
                    ·
                      refine ⟨2134645371235821642193859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692387656628857712516957 2134645371235821642193859)
                      ·
                        rfl

theorem cell23_4157207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4157207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157207 prefixEnd_4157207 := by exact prefixLift 4157207
  have htrace : WordTrace (prefixWord ++ tailWord_4157207) baseStart_4157207 baseEnd_4157207 := by
    simpa [prefixWord, tailWord_4157207, baseEnd_4157207] using wordTrace_append hprefix tailTrace_4157207
  have hstable : (prefixWord ++ tailWord_4157207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157207).length < 2 ^ (prefixWord ++ tailWord_4157207).sum := by decide
  have hdescent : baseEnd_4157207 < baseStart_4157207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157257 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_4157257 : Nat := 118140960795 + 4157257 * 2 ^ 59
def prefixEnd_4157257 : Nat := 4983230072969 + 3 ^ 40 * 4157257 * 2
def baseEnd_4157257 : Nat := 711557015089515482189543

theorem tailTrace_4157257 : CollatzResearch.WordTrace tailWord_4157257 prefixEnd_4157257 711557015089515482189543 := by
  unfold tailWord_4157257
  simp only [CollatzResearch.WordTrace]
  refine ⟨151627619499975366814486025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101085079666650244542990683 151627619499975366814486025)
  ·
    refine ⟨113720714624981525110864519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151627619499975366814486025 113720714624981525110864519)
    ·
      refine ⟨170581071937472287666296779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113720714624981525110864519 170581071937472287666296779)
      ·
        refine ⟨255871607906208431499445169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170581071937472287666296779 255871607906208431499445169)
        ·
          refine ⟨191903705929656323624583877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255871607906208431499445169 191903705929656323624583877)
          ·
            refine ⟨35981944861810560679609477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191903705929656323624583877 35981944861810560679609477)
            ·
              refine ⟨6746614661589480127426777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35981944861810560679609477 6746614661589480127426777)
              ·
                refine ⟨5059960996192110095570083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6746614661589480127426777 5059960996192110095570083)
                ·
                  refine ⟨7589941494288165143355125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5059960996192110095570083 7589941494288165143355125)
                  ·
                    refine ⟨711557015089515482189543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7589941494288165143355125 711557015089515482189543)
                    ·
                      rfl

theorem cell23_4157257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_4157257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157257 prefixEnd_4157257 := by exact prefixLift 4157257
  have htrace : WordTrace (prefixWord ++ tailWord_4157257) baseStart_4157257 baseEnd_4157257 := by
    simpa [prefixWord, tailWord_4157257, baseEnd_4157257] using wordTrace_append hprefix tailTrace_4157257
  have hstable : (prefixWord ++ tailWord_4157257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157257).length < 2 ^ (prefixWord ++ tailWord_4157257).sum := by decide
  have hdescent : baseEnd_4157257 < baseStart_4157257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157287 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 4, 4]
def baseStart_4157287 : Nat := 118140960795 + 4157287 * 2 ^ 59
def prefixEnd_4157287 : Nat := 4983230072969 + 3 ^ 40 * 4157287 * 2
def baseEnd_4157287 : Nat := 711562149896060443064497

theorem tailTrace_4157287 : CollatzResearch.WordTrace tailWord_4157287 prefixEnd_4157287 711562149896060443064497 := by
  unfold tailWord_4157287
  simp only [CollatzResearch.WordTrace]
  refine ⟨151628713689866681938078115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101085809126577787958718743 151628713689866681938078115)
  ·
    refine ⟨227443070534800022907117173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151628713689866681938078115 227443070534800022907117173)
    ·
      refine ⟨21322787862637502147542235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227443070534800022907117173 21322787862637502147542235)
      ·
        refine ⟨31984181793956253221313353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21322787862637502147542235 31984181793956253221313353)
        ·
          refine ⟨23988136345467189915985015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31984181793956253221313353 23988136345467189915985015)
          ·
            refine ⟨35982204518200784873977523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23988136345467189915985015 35982204518200784873977523)
            ·
              refine ⟨53973306777301177310966285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35982204518200784873977523 53973306777301177310966285)
              ·
                refine ⟨20239990041487941491612357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53973306777301177310966285 20239990041487941491612357)
                ·
                  refine ⟨3794998132778989029677317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20239990041487941491612357 3794998132778989029677317)
                  ·
                    refine ⟨711562149896060443064497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3794998132778989029677317 711562149896060443064497)
                    ·
                      rfl

theorem cell23_4157287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_4157287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157287 prefixEnd_4157287 := by exact prefixLift 4157287
  have htrace : WordTrace (prefixWord ++ tailWord_4157287) baseStart_4157287 baseEnd_4157287 := by
    simpa [prefixWord, tailWord_4157287, baseEnd_4157287] using wordTrace_append hprefix tailTrace_4157287
  have hstable : (prefixWord ++ tailWord_4157287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157287).length < 2 ^ (prefixWord ++ tailWord_4157287).sum := by decide
  have hdescent : baseEnd_4157287 < baseStart_4157287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157288 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4157288 : Nat := 118140960795 + 4157288 * 2 ^ 59
def prefixEnd_4157288 : Nat := 4983230072969 + 3 ^ 40 * 4157288 * 2
def baseEnd_4157288 : Nat := 2134686963168835825280987

theorem tailTrace_4157288 : CollatzResearch.WordTrace tailWord_4157288 prefixEnd_4157288 2134686963168835825280987 := by
  unfold tailWord_4157288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75814375081431529554432259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101085833441908706072576345 75814375081431529554432259)
  ·
    refine ⟨113721562622147294331648389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75814375081431529554432259 113721562622147294331648389)
    ·
      refine ⟨21322792991652617687184073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113721562622147294331648389 21322792991652617687184073)
      ·
        refine ⟨15992094743739463265388055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21322792991652617687184073 15992094743739463265388055)
        ·
          refine ⟨23988142115609194898082083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992094743739463265388055 23988142115609194898082083)
          ·
            refine ⟨35982213173413792347123125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23988142115609194898082083 35982213173413792347123125)
            ·
              refine ⟨3373332485007543032542793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35982213173413792347123125 3373332485007543032542793)
              ·
                refine ⟨2529999363755657274407095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3373332485007543032542793 2529999363755657274407095)
                ·
                  refine ⟨3794999045633485911610643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2529999363755657274407095 3794999045633485911610643)
                  ·
                    refine ⟨5692498568450228867415965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3794999045633485911610643 5692498568450228867415965)
                    ·
                      refine ⟨2134686963168835825280987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692498568450228867415965 2134686963168835825280987)
                      ·
                        rfl

theorem cell23_4157288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4157288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157288 prefixEnd_4157288 := by exact prefixLift 4157288
  have htrace : WordTrace (prefixWord ++ tailWord_4157288) baseStart_4157288 baseEnd_4157288 := by
    simpa [prefixWord, tailWord_4157288, baseEnd_4157288] using wordTrace_append hprefix tailTrace_4157288
  have hstable : (prefixWord ++ tailWord_4157288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157288).length < 2 ^ (prefixWord ++ tailWord_4157288).sum := by decide
  have hdescent : baseEnd_4157288 < baseStart_4157288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157297 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_4157297 : Nat := 118140960795 + 4157297 * 2 ^ 59
def prefixEnd_4157297 : Nat := 4983230072969 + 3 ^ 40 * 4157297 * 2
def baseEnd_4157297 : Nat := 2134691584494726290068445

theorem tailTrace_4157297 : CollatzResearch.WordTrace tailWord_4157297 prefixEnd_4157297 2134691584494726290068445 := by
  unfold tailWord_4157297
  simp only [CollatzResearch.WordTrace]
  refine ⟨151629078419830453645942145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101086052279886969097294763 151629078419830453645942145)
  ·
    refine ⟨113721808814872840234456609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151629078419830453645942145 113721808814872840234456609)
    ·
      refine ⟨85291356611154630175842457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113721808814872840234456609 85291356611154630175842457)
      ·
        refine ⟨63968517458365972631881843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85291356611154630175842457 63968517458365972631881843)
        ·
          refine ⟨95952776187548958947822765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63968517458365972631881843 95952776187548958947822765)
          ·
            refine ⟨35982291070330859605433537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95952776187548958947822765 35982291070330859605433537)
            ·
              refine ⟨26986718302748144704075153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35982291070330859605433537 26986718302748144704075153)
              ·
                refine ⟨20240038727061108528056365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26986718302748144704075153 20240038727061108528056365)
                ·
                  refine ⟨7590014522647915698021137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20240038727061108528056365 7590014522647915698021137)
                  ·
                    refine ⟨5692510891985936773515853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7590014522647915698021137 5692510891985936773515853)
                    ·
                      refine ⟨2134691584494726290068445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692510891985936773515853 2134691584494726290068445)
                      ·
                        rfl

theorem cell23_4157297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_4157297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157297 prefixEnd_4157297 := by exact prefixLift 4157297
  have htrace : WordTrace (prefixWord ++ tailWord_4157297) baseStart_4157297 baseEnd_4157297 := by
    simpa [prefixWord, tailWord_4157297, baseEnd_4157297] using wordTrace_append hprefix tailTrace_4157297
  have hstable : (prefixWord ++ tailWord_4157297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157297).length < 2 ^ (prefixWord ++ tailWord_4157297).sum := by decide
  have hdescent : baseEnd_4157297 < baseStart_4157297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157334 : List Nat := [5, 3, 1, 1, 13]
def baseStart_4157334 : Nat := 118140960795 + 4157334 * 2 ^ 59
def prefixEnd_4157334 : Nat := 4983230072969 + 3 ^ 40 * 4157334 * 2
def baseEnd_4157334 : Nat := 2928272405046560555975

theorem tailTrace_4157334 : CollatzResearch.WordTrace tailWord_4157334 prefixEnd_4157334 2928272405046560555975 := by
  unfold tailWord_4157334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476901745043525560314941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101086951947130939310026037 9476901745043525560314941)
  ·
    refine ⟨3553838154391322085118103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9476901745043525560314941 3553838154391322085118103)
    ·
      refine ⟨5330757231586983127677155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553838154391322085118103 5330757231586983127677155)
      ·
        refine ⟨7996135847380474691515733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330757231586983127677155 7996135847380474691515733)
        ·
          refine ⟨2928272405046560555975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7996135847380474691515733 2928272405046560555975)
          ·
            rfl

theorem cell23_4157334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 13].length) (baseStart_4157334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157334 prefixEnd_4157334 := by exact prefixLift 4157334
  have htrace : WordTrace (prefixWord ++ tailWord_4157334) baseStart_4157334 baseEnd_4157334 := by
    simpa [prefixWord, tailWord_4157334, baseEnd_4157334] using wordTrace_append hprefix tailTrace_4157334
  have hstable : (prefixWord ++ tailWord_4157334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157334).length < 2 ^ (prefixWord ++ tailWord_4157334).sum := by decide
  have hdescent : baseEnd_4157334 < baseStart_4157334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157345 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4157345 : Nat := 118140960795 + 4157345 * 2 ^ 59
def prefixEnd_4157345 : Nat := 4983230072969 + 3 ^ 40 * 4157345 * 2
def baseEnd_4157345 : Nat := 2134716231566142102268225

theorem tailTrace_4157345 : CollatzResearch.WordTrace tailWord_4157345 prefixEnd_4157345 2134716231566142102268225 := by
  unfold tailWord_4157345
  simp only [CollatzResearch.WordTrace]
  refine ⟨151630829123656557843689489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101087219415771038562459659 151630829123656557843689489)
  ·
    refine ⟨113723121842742418382767117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151630829123656557843689489 113723121842742418382767117)
    ·
      refine ⟨42646170691028406893537669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113723121842742418382767117 42646170691028406893537669)
      ·
        refine ⟨7996157004567826292538313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42646170691028406893537669 7996157004567826292538313)
        ·
          refine ⟨5997117753425869719403735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7996157004567826292538313 5997117753425869719403735)
          ·
            refine ⟨8995676630138804579105603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5997117753425869719403735 8995676630138804579105603)
            ·
              refine ⟨13493514945208206868658405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8995676630138804579105603 13493514945208206868658405)
              ·
                refine ⟨2530034052226538787873451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13493514945208206868658405 2530034052226538787873451)
                ·
                  refine ⟨3795051078339808181810177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530034052226538787873451 3795051078339808181810177)
                  ·
                    refine ⟨2846288308754856136357633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3795051078339808181810177 2846288308754856136357633)
                    ·
                      refine ⟨2134716231566142102268225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846288308754856136357633 2134716231566142102268225)
                      ·
                        rfl

theorem cell23_4157345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4157345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157345 prefixEnd_4157345 := by exact prefixLift 4157345
  have htrace : WordTrace (prefixWord ++ tailWord_4157345) baseStart_4157345 baseEnd_4157345 := by
    simpa [prefixWord, tailWord_4157345, baseEnd_4157345] using wordTrace_append hprefix tailTrace_4157345
  have hstable : (prefixWord ++ tailWord_4157345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157345).length < 2 ^ (prefixWord ++ tailWord_4157345).sum := by decide
  have hdescent : baseEnd_4157345 < baseStart_4157345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157361 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4157361 : Nat := 118140960795 + 4157361 * 2 ^ 59
def prefixEnd_4157361 : Nat := 4983230072969 + 3 ^ 40 * 4157361 * 2
def baseEnd_4157361 : Nat := 2134724447256614039668151

theorem tailTrace_4157361 : CollatzResearch.WordTrace tailWord_4157361 prefixEnd_4157361 2134724447256614039668151 := by
  unfold tailWord_4157361
  simp only [CollatzResearch.WordTrace]
  refine ⟨151631412691598592576271937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101087608461065728384181291 151631412691598592576271937)
  ·
    refine ⟨113723559518698944432203953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151631412691598592576271937 113723559518698944432203953)
    ·
      refine ⟨85292669639024208324152965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113723559518698944432203953 85292669639024208324152965)
      ·
        refine ⟨15992375557317039060778681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85292669639024208324152965 15992375557317039060778681)
        ·
          refine ⟨11994281667987779295584011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15992375557317039060778681 11994281667987779295584011)
          ·
            refine ⟨17991422501981668943376017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994281667987779295584011 17991422501981668943376017)
            ·
              refine ⟨13493566876486251707532013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17991422501981668943376017 13493566876486251707532013)
              ·
                refine ⟨5060087578682344390324505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13493566876486251707532013 5060087578682344390324505)
                ·
                  refine ⟨3795065684011758292743379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060087578682344390324505 3795065684011758292743379)
                  ·
                    refine ⟨5692598526017637439115069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3795065684011758292743379 5692598526017637439115069)
                    ·
                      refine ⟨2134724447256614039668151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692598526017637439115069 2134724447256614039668151)
                      ·
                        rfl

theorem cell23_4157361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4157361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157361 prefixEnd_4157361 := by exact prefixLift 4157361
  have htrace : WordTrace (prefixWord ++ tailWord_4157361) baseStart_4157361 baseEnd_4157361 := by
    simpa [prefixWord, tailWord_4157361, baseEnd_4157361] using wordTrace_append hprefix tailTrace_4157361
  have hstable : (prefixWord ++ tailWord_4157361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157361).length < 2 ^ (prefixWord ++ tailWord_4157361).sum := by decide
  have hdescent : baseEnd_4157361 < baseStart_4157361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157388 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4157388 : Nat := 118140960795 + 4157388 * 2 ^ 59
def prefixEnd_4157388 : Nat := 4983230072969 + 3 ^ 40 * 4157388 * 2
def baseEnd_4157388 : Nat := 2134738311234285434030527

theorem tailTrace_4157388 : CollatzResearch.WordTrace tailWord_4157388 prefixEnd_4157388 2134738311234285434030527 := by
  unfold tailWord_4157388
  simp only [CollatzResearch.WordTrace]
  refine ⟨75816198731250388093752409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101088264975000517458336545 75816198731250388093752409)
  ·
    refine ⟨56862149048437791070314307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75816198731250388093752409 56862149048437791070314307)
    ·
      refine ⟨85293223572656686605471461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56862149048437791070314307 85293223572656686605471461)
      ·
        refine ⟨15992479419873128738525899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85293223572656686605471461 15992479419873128738525899)
        ·
          refine ⟨23988719129809693107788849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992479419873128738525899 23988719129809693107788849)
          ·
            refine ⟨17991539347357269830841637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23988719129809693107788849 17991539347357269830841637)
            ·
              refine ⟨3373413627629488093282807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17991539347357269830841637 3373413627629488093282807)
              ·
                refine ⟨5060120441444232139924211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373413627629488093282807 5060120441444232139924211)
                ·
                  refine ⟨7590180662166348209886317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060120441444232139924211 7590180662166348209886317)
                  ·
                    refine ⟨2846317748312380578707369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7590180662166348209886317 2846317748312380578707369)
                    ·
                      refine ⟨2134738311234285434030527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846317748312380578707369 2134738311234285434030527)
                      ·
                        rfl

theorem cell23_4157388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4157388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157388 prefixEnd_4157388 := by exact prefixLift 4157388
  have htrace : WordTrace (prefixWord ++ tailWord_4157388) baseStart_4157388 baseEnd_4157388 := by
    simpa [prefixWord, tailWord_4157388, baseEnd_4157388] using wordTrace_append hprefix tailTrace_4157388
  have hstable : (prefixWord ++ tailWord_4157388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157388).length < 2 ^ (prefixWord ++ tailWord_4157388).sum := by decide
  have hdescent : baseEnd_4157388 < baseStart_4157388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157407 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 7]
def baseStart_4157407 : Nat := 118140960795 + 4157407 * 2 ^ 59
def prefixEnd_4157407 : Nat := 4983230072969 + 3 ^ 40 * 4157407 * 2
def baseEnd_4157407 : Nat := 237194229707413428854771

theorem tailTrace_4157407 : CollatzResearch.WordTrace tailWord_4157407 prefixEnd_4157407 237194229707413428854771 := by
  unfold tailWord_4157407
  simp only [CollatzResearch.WordTrace]
  refine ⟨151633090449431942432446475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101088726966287961621630983 151633090449431942432446475)
  ·
    refine ⟨227449635674147913648669713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151633090449431942432446475 227449635674147913648669713)
    ·
      refine ⟨170587226755610935236502285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227449635674147913648669713 170587226755610935236502285)
      ·
        refine ⟨63970210033354100713688357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170587226755610935236502285 63970210033354100713688357)
        ·
          refine ⟨11994414381253893883816567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63970210033354100713688357 11994414381253893883816567)
          ·
            refine ⟨17991621571880840825724851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11994414381253893883816567 17991621571880840825724851)
            ·
              refine ⟨26987432357821261238587277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17991621571880840825724851 26987432357821261238587277)
              ·
                refine ⟨10120287134182972964470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26987432357821261238587277 10120287134182972964470229)
                ·
                  refine ⟨237194229707413428854771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10120287134182972964470229 237194229707413428854771)
                  ·
                    rfl

theorem cell23_4157407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 7].length) (baseStart_4157407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157407 prefixEnd_4157407 := by exact prefixLift 4157407
  have htrace : WordTrace (prefixWord ++ tailWord_4157407) baseStart_4157407 baseEnd_4157407 := by
    simpa [prefixWord, tailWord_4157407, baseEnd_4157407] using wordTrace_append hprefix tailTrace_4157407
  have hstable : (prefixWord ++ tailWord_4157407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157407).length < 2 ^ (prefixWord ++ tailWord_4157407).sum := by decide
  have hdescent : baseEnd_4157407 < baseStart_4157407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157437 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_4157437 : Nat := 118140960795 + 4157437 * 2 ^ 59
def prefixEnd_4157437 : Nat := 4983230072969 + 3 ^ 40 * 4157437 * 2
def baseEnd_4157437 : Nat := 711587823928785247439267

theorem tailTrace_4157437 : CollatzResearch.WordTrace tailWord_4157437 prefixEnd_4157437 711587823928785247439267 := by
  unfold tailWord_4157437
  simp only [CollatzResearch.WordTrace]
  refine ⟨151634184639323257556038565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101089456426215505037359043 151634184639323257556038565)
  ·
    refine ⟨28431409619873110791757231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151634184639323257556038565 28431409619873110791757231)
    ·
      refine ⟨42647114429809666187635847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28431409619873110791757231 42647114429809666187635847)
      ·
        refine ⟨63970671644714499281453771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42647114429809666187635847 63970671644714499281453771)
        ·
          refine ⟨95956007467071748922180657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63970671644714499281453771 95956007467071748922180657)
          ·
            refine ⟨71967005600303811691635493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95956007467071748922180657 71967005600303811691635493)
            ·
              refine ⟨13493813550056964692181655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71967005600303811691635493 13493813550056964692181655)
              ·
                refine ⟨20240720325085447038272483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13493813550056964692181655 20240720325085447038272483)
                ·
                  refine ⟨30361080487628170557408725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20240720325085447038272483 30361080487628170557408725)
                  ·
                    refine ⟨711587823928785247439267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30361080487628170557408725 711587823928785247439267)
                    ·
                      rfl

theorem cell23_4157437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_4157437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157437 prefixEnd_4157437 := by exact prefixLift 4157437
  have htrace : WordTrace (prefixWord ++ tailWord_4157437) baseStart_4157437 baseEnd_4157437 := by
    simpa [prefixWord, tailWord_4157437, baseEnd_4157437] using wordTrace_append hprefix tailTrace_4157437
  have hstable : (prefixWord ++ tailWord_4157437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157437).length < 2 ^ (prefixWord ++ tailWord_4157437).sum := by decide
  have hdescent : baseEnd_4157437 < baseStart_4157437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157454 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4157454 : Nat := 118140960795 + 4157454 * 2 ^ 59
def prefixEnd_4157454 : Nat := 4983230072969 + 3 ^ 40 * 4157454 * 2
def baseEnd_4157454 : Nat := 711590733652494058601741

theorem tailTrace_4157454 : CollatzResearch.WordTrace tailWord_4157454 prefixEnd_4157454 711590733652494058601741 := by
  unfold tailWord_4157454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954350585032708682425927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101089869786841112972938277 18954350585032708682425927)
  ·
    refine ⟨28431525877549063023638891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18954350585032708682425927 28431525877549063023638891)
    ·
      refine ⟨42647288816323594535458337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28431525877549063023638891 42647288816323594535458337)
      ·
        refine ⟨31985466612242695901593753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42647288816323594535458337 31985466612242695901593753)
        ·
          refine ⟨23989099959182021926195315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31985466612242695901593753 23989099959182021926195315)
          ·
            refine ⟨35983649938773032889292973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23989099959182021926195315 35983649938773032889292973)
            ·
              refine ⟨13493868727039887333484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35983649938773032889292973 13493868727039887333484865)
              ·
                refine ⟨10120401545279915500113649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13493868727039887333484865 10120401545279915500113649)
                ·
                  refine ⟨7590301158959936625085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10120401545279915500113649 7590301158959936625085237)
                  ·
                    refine ⟨711590733652494058601741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7590301158959936625085237 711590733652494058601741)
                    ·
                      rfl

theorem cell23_4157454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4157454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157454 prefixEnd_4157454 := by exact prefixLift 4157454
  have htrace : WordTrace (prefixWord ++ tailWord_4157454) baseStart_4157454 baseEnd_4157454 := by
    simpa [prefixWord, tailWord_4157454, baseEnd_4157454] using wordTrace_append hprefix tailTrace_4157454
  have hstable : (prefixWord ++ tailWord_4157454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157454).length < 2 ^ (prefixWord ++ tailWord_4157454).sum := by decide
  have hdescent : baseEnd_4157454 < baseStart_4157454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157474 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4157474 : Nat := 118140960795 + 4157474 * 2 ^ 59
def prefixEnd_4157474 : Nat := 4983230072969 + 3 ^ 40 * 4157474 * 2
def baseEnd_4157474 : Nat := 2134782470570572097555131

theorem tailTrace_4157474 : CollatzResearch.WordTrace tailWord_4157474 prefixEnd_4157474 2134782470570572097555131 := by
  unfold tailWord_4157474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37908883535047303218783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101090356093459475250090317 37908883535047303218783869)
  ·
    refine ⟨14215831325642738707043951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37908883535047303218783869 14215831325642738707043951)
    ·
      refine ⟨21323746988464108060565927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14215831325642738707043951 21323746988464108060565927)
      ·
        refine ⟨31985620482696162090848891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21323746988464108060565927 31985620482696162090848891)
        ·
          refine ⟨47978430724044243136273337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31985620482696162090848891 47978430724044243136273337)
          ·
            refine ⟨35983823043033182352205003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47978430724044243136273337 35983823043033182352205003)
            ·
              refine ⟨53975734564549773528307505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35983823043033182352205003 53975734564549773528307505)
              ·
                refine ⟨40481800923412330146230629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53975734564549773528307505 40481800923412330146230629)
                ·
                  refine ⟨7590337673139811902418243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40481800923412330146230629 7590337673139811902418243)
                  ·
                    refine ⟨11385506509709717853627365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7590337673139811902418243 11385506509709717853627365)
                    ·
                      refine ⟨2134782470570572097555131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11385506509709717853627365 2134782470570572097555131)
                      ·
                        rfl

theorem cell23_4157474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4157474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157474 prefixEnd_4157474 := by exact prefixLift 4157474
  have htrace : WordTrace (prefixWord ++ tailWord_4157474) baseStart_4157474 baseEnd_4157474 := by
    simpa [prefixWord, tailWord_4157474, baseEnd_4157474] using wordTrace_append hprefix tailTrace_4157474
  have hstable : (prefixWord ++ tailWord_4157474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157474).length < 2 ^ (prefixWord ++ tailWord_4157474).sum := by decide
  have hdescent : baseEnd_4157474 < baseStart_4157474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157518 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_4157518 : Nat := 118140960795 + 4157518 * 2 ^ 59
def prefixEnd_4157518 : Nat := 4983230072969 + 3 ^ 40 * 4157518 * 2
def baseEnd_4157518 : Nat := 711601687906456641801643

theorem tailTrace_4157518 : CollatzResearch.WordTrace tailWord_4157518 prefixEnd_4157518 711601687906456641801643 := by
  unfold tailWord_4157518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954642369003726048717151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101091425968019872259824805 18954642369003726048717151)
  ·
    refine ⟨28431963553505589073075727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18954642369003726048717151 28431963553505589073075727)
    ·
      refine ⟨42647945330258383609613591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28431963553505589073075727 42647945330258383609613591)
      ·
        refine ⟨63971917995387575414420387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42647945330258383609613591 63971917995387575414420387)
        ·
          refine ⟨95957876993081363121630581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63971917995387575414420387 95957876993081363121630581)
          ·
            refine ⟨8996050968101377792652867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95957876993081363121630581 8996050968101377792652867)
            ·
              refine ⟨13494076452152066688979301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996050968101377792652867 13494076452152066688979301)
              ·
                refine ⟨2530139334778512504183619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13494076452152066688979301 2530139334778512504183619)
                ·
                  refine ⟨3795209002167768756275429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530139334778512504183619 3795209002167768756275429)
                  ·
                    refine ⟨711601687906456641801643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795209002167768756275429 711601687906456641801643)
                    ·
                      rfl

theorem cell23_4157518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_4157518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157518 prefixEnd_4157518 := by exact prefixLift 4157518
  have htrace : WordTrace (prefixWord ++ tailWord_4157518) baseStart_4157518 baseEnd_4157518 := by
    simpa [prefixWord, tailWord_4157518, baseEnd_4157518] using wordTrace_append hprefix tailTrace_4157518
  have hstable : (prefixWord ++ tailWord_4157518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157518).length < 2 ^ (prefixWord ++ tailWord_4157518).sum := by decide
  have hdescent : baseEnd_4157518 < baseStart_4157518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157524 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_4157524 : Nat := 118140960795 + 4157524 * 2 ^ 59
def prefixEnd_4157524 : Nat := 4983230072969 + 3 ^ 40 * 4157524 * 2
def baseEnd_4157524 : Nat := 2134808144603296901929901

theorem tailTrace_4157524 : CollatzResearch.WordTrace tailWord_4157524 prefixEnd_4157524 2134808144603296901929901 := by
  unfold tailWord_4157524
  simp only [CollatzResearch.WordTrace]
  refine ⟨75818678895004035707227813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101091571860005380942970417 75818678895004035707227813)
  ·
    refine ⟨14216002292813256695105215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75818678895004035707227813 14216002292813256695105215)
    ·
      refine ⟨21324003439219885042657823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14216002292813256695105215 21324003439219885042657823)
      ·
        refine ⟨31986005158829827563986735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21324003439219885042657823 31986005158829827563986735)
        ·
          refine ⟨47979007738244741345980103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31986005158829827563986735 47979007738244741345980103)
          ·
            refine ⟨71968511607367112018970155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47979007738244741345980103 71968511607367112018970155)
            ·
              refine ⟨107952767411050668028455233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71968511607367112018970155 107952767411050668028455233)
              ·
                refine ⟨80964575558288001021341425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107952767411050668028455233 80964575558288001021341425)
                ·
                  refine ⟨60723431668716000766006069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80964575558288001021341425 60723431668716000766006069)
                  ·
                    refine ⟨5692821718942125071813069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60723431668716000766006069 5692821718942125071813069)
                    ·
                      refine ⟨2134808144603296901929901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692821718942125071813069 2134808144603296901929901)
                      ·
                        rfl

theorem cell23_4157524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_4157524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157524 prefixEnd_4157524 := by exact prefixLift 4157524
  have htrace : WordTrace (prefixWord ++ tailWord_4157524) baseStart_4157524 baseEnd_4157524 := by
    simpa [prefixWord, tailWord_4157524, baseEnd_4157524] using wordTrace_append hprefix tailTrace_4157524
  have hstable : (prefixWord ++ tailWord_4157524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157524).length < 2 ^ (prefixWord ++ tailWord_4157524).sum := by decide
  have hdescent : baseEnd_4157524 < baseStart_4157524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157537 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4157537 : Nat := 118140960795 + 4157537 * 2 ^ 59
def prefixEnd_4157537 : Nat := 4983230072969 + 3 ^ 40 * 4157537 * 2
def baseEnd_4157537 : Nat := 2134814819851805351067341

theorem tailTrace_4157537 : CollatzResearch.WordTrace tailWord_4157537 prefixEnd_4157537 2134814819851805351067341 := by
  unfold tailWord_4157537
  simp only [CollatzResearch.WordTrace]
  refine ⟨151637831938960974634678865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101091887959307316423119243 151637831938960974634678865)
  ·
    refine ⟨113728373954220730976009149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151637831938960974634678865 113728373954220730976009149)
    ·
      refine ⟨42648140232832774116003431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113728373954220730976009149 42648140232832774116003431)
      ·
        refine ⟨63972210349249161174005147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42648140232832774116003431 63972210349249161174005147)
        ·
          refine ⟨95958315523873741761007721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63972210349249161174005147 95958315523873741761007721)
          ·
            refine ⟨71968736642905306320755791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95958315523873741761007721 71968736642905306320755791)
            ·
              refine ⟨107953104964357959481133687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71968736642905306320755791 107953104964357959481133687)
              ·
                refine ⟨161929657446536939221700531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107953104964357959481133687 161929657446536939221700531)
                ·
                  refine ⟨242894486169805408832550797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161929657446536939221700531 242894486169805408832550797)
                  ·
                    refine ⟨91085432313677028312206549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242894486169805408832550797 91085432313677028312206549)
                    ·
                      refine ⟨2134814819851805351067341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91085432313677028312206549 2134814819851805351067341)
                      ·
                        rfl

theorem cell23_4157537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4157537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157537 prefixEnd_4157537 := by exact prefixLift 4157537
  have htrace : WordTrace (prefixWord ++ tailWord_4157537) baseStart_4157537 baseEnd_4157537 := by
    simpa [prefixWord, tailWord_4157537, baseEnd_4157537] using wordTrace_append hprefix tailTrace_4157537
  have hstable : (prefixWord ++ tailWord_4157537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157537).length < 2 ^ (prefixWord ++ tailWord_4157537).sum := by decide
  have hdescent : baseEnd_4157537 < baseStart_4157537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157541 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_4157541 : Nat := 118140960795 + 4157541 * 2 ^ 59
def prefixEnd_4157541 : Nat := 4983230072969 + 3 ^ 40 * 4157541 * 2
def baseEnd_4157541 : Nat := 2134816873774423335417323

theorem tailTrace_4157541 : CollatzResearch.WordTrace tailWord_4157541 prefixEnd_4157541 2134816873774423335417323 := by
  unfold tailWord_4157541
  simp only [CollatzResearch.WordTrace]
  refine ⟨151637977830946483317824477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101091985220630988878549651 151637977830946483317824477)
  ·
    refine ⟨56864241686604931244184179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151637977830946483317824477 56864241686604931244184179)
    ·
      refine ⟨85296362529907396866276269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56864241686604931244184179 85296362529907396866276269)
      ·
        refine ⟨31986135948715273824853601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85296362529907396866276269 31986135948715273824853601)
        ·
          refine ⟨23989601961536455368640201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31986135948715273824853601 23989601961536455368640201)
          ·
            refine ⟨17992201471152341526480151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23989601961536455368640201 17992201471152341526480151)
            ·
              refine ⟨26988302206728512289720227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17992201471152341526480151 26988302206728512289720227)
              ·
                refine ⟨40482453310092768434580341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26988302206728512289720227 40482453310092768434580341)
                ·
                  refine ⟨3795229997821197040741907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40482453310092768434580341 3795229997821197040741907)
                  ·
                    refine ⟨5692844996731795561112861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3795229997821197040741907 5692844996731795561112861)
                    ·
                      refine ⟨2134816873774423335417323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5692844996731795561112861 2134816873774423335417323)
                      ·
                        rfl

theorem cell23_4157541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_4157541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157541 prefixEnd_4157541 := by exact prefixLift 4157541
  have htrace : WordTrace (prefixWord ++ tailWord_4157541) baseStart_4157541 baseEnd_4157541 := by
    simpa [prefixWord, tailWord_4157541, baseEnd_4157541] using wordTrace_append hprefix tailTrace_4157541
  have hstable : (prefixWord ++ tailWord_4157541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157541).length < 2 ^ (prefixWord ++ tailWord_4157541).sum := by decide
  have hdescent : baseEnd_4157541 < baseStart_4157541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157551 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 5, 2]
def baseStart_4157551 : Nat := 118140960795 + 4157551 * 2 ^ 59
def prefixEnd_4157551 : Nat := 4983230072969 + 3 ^ 40 * 4157551 * 2
def baseEnd_4157551 : Nat := 2134822008580968296292277

theorem tailTrace_4157551 : CollatzResearch.WordTrace tailWord_4157551 prefixEnd_4157551 2134822008580968296292277 := by
  unfold tailWord_4157551
  simp only [CollatzResearch.WordTrace]
  refine ⟨151638342560910255025688507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101092228373940170017125671 151638342560910255025688507)
  ·
    refine ⟨227457513841365382538532761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151638342560910255025688507 227457513841365382538532761)
    ·
      refine ⟨170593135381024036903899571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227457513841365382538532761 170593135381024036903899571)
      ·
        refine ⟨255889703071536055355849357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170593135381024036903899571 255889703071536055355849357)
        ·
          refine ⟨95958638651826020758443509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255889703071536055355849357 95958638651826020758443509)
          ·
            refine ⟨8996122373608689446104079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95958638651826020758443509 8996122373608689446104079)
            ·
              refine ⟨13494183560413034169156119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996122373608689446104079 13494183560413034169156119)
              ·
                refine ⟨20241275340619551253734179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494183560413034169156119 20241275340619551253734179)
                ·
                  refine ⟨30361913010929326880601269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20241275340619551253734179 30361913010929326880601269)
                  ·
                    refine ⟨2846429344774624395056369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30361913010929326880601269 2846429344774624395056369)
                    ·
                      refine ⟨2134822008580968296292277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846429344774624395056369 2134822008580968296292277)
                      ·
                        rfl

theorem cell23_4157551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5, 2].length) (baseStart_4157551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157551 prefixEnd_4157551 := by exact prefixLift 4157551
  have htrace : WordTrace (prefixWord ++ tailWord_4157551) baseStart_4157551 baseEnd_4157551 := by
    simpa [prefixWord, tailWord_4157551, baseEnd_4157551] using wordTrace_append hprefix tailTrace_4157551
  have hstable : (prefixWord ++ tailWord_4157551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157551).length < 2 ^ (prefixWord ++ tailWord_4157551).sum := by decide
  have hdescent : baseEnd_4157551 < baseStart_4157551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157561 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_4157561 : Nat := 118140960795 + 4157561 * 2 ^ 59
def prefixEnd_4157561 : Nat := 4983230072969 + 3 ^ 40 * 4157561 * 2
def baseEnd_4157561 : Nat := 711609047795837752389077

theorem tailTrace_4157561 : CollatzResearch.WordTrace tailWord_4157561 prefixEnd_4157561 711609047795837752389077 := by
  unfold tailWord_4157561
  simp only [CollatzResearch.WordTrace]
  refine ⟨151638707290874026733552537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101092471527249351155701691 151638707290874026733552537)
  ·
    refine ⟨113729030468155520050164403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151638707290874026733552537 113729030468155520050164403)
    ·
      refine ⟨170593545702233280075246605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113729030468155520050164403 170593545702233280075246605)
      ·
        refine ⟨63972579638337480028217477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170593545702233280075246605 63972579638337480028217477)
        ·
          refine ⟨11994858682188277505290777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63972579638337480028217477 11994858682188277505290777)
          ·
            refine ⟨8996144011641208128968083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11994858682188277505290777 8996144011641208128968083)
            ·
              refine ⟨13494216017461812193452125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996144011641208128968083 13494216017461812193452125)
              ·
                refine ⟨5060331006548179572544547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13494216017461812193452125 5060331006548179572544547)
                ·
                  refine ⟨7590496509822269358816821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060331006548179572544547 7590496509822269358816821)
                  ·
                    refine ⟨711609047795837752389077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7590496509822269358816821 711609047795837752389077)
                    ·
                      rfl

theorem cell23_4157561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_4157561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157561 prefixEnd_4157561 := by exact prefixLift 4157561
  have htrace : WordTrace (prefixWord ++ tailWord_4157561) baseStart_4157561 baseEnd_4157561 := by
    simpa [prefixWord, tailWord_4157561, baseEnd_4157561] using wordTrace_append hprefix tailTrace_4157561
  have hstable : (prefixWord ++ tailWord_4157561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157561).length < 2 ^ (prefixWord ++ tailWord_4157561).sum := by decide
  have hdescent : baseEnd_4157561 < baseStart_4157561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157584 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_4157584 : Nat := 118140960795 + 4157584 * 2 ^ 59
def prefixEnd_4157584 : Nat := 4983230072969 + 3 ^ 40 * 4157584 * 2
def baseEnd_4157584 : Nat := 2134838953442566667179625

theorem tailTrace_4157584 : CollatzResearch.WordTrace tailWord_4157584 prefixEnd_4157584 2134838953442566667179625 := by
  unfold tailWord_4157584
  simp only [CollatzResearch.WordTrace]
  refine ⟨75819773084895350830819903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101093030779860467774426537 75819773084895350830819903)
  ·
    refine ⟨113729659627343026246229855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75819773084895350830819903 113729659627343026246229855)
    ·
      refine ⟨170594489441014539369344783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113729659627343026246229855 170594489441014539369344783)
      ·
        refine ⟨255891734161521809054017175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170594489441014539369344783 255891734161521809054017175)
        ·
          refine ⟨383837601242282713581025763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255891734161521809054017175 383837601242282713581025763)
          ·
            refine ⟨575756401863424070371538645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383837601242282713581025763 575756401863424070371538645)
            ·
              refine ⟨13494290668674001649332937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 575756401863424070371538645 13494290668674001649332937)
              ·
                refine ⟨10120718001505501236999703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13494290668674001649332937 10120718001505501236999703)
                ·
                  refine ⟨15181077002258251855499555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10120718001505501236999703 15181077002258251855499555)
                  ·
                    refine ⟨22771615503387377783249333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15181077002258251855499555 22771615503387377783249333)
                    ·
                      refine ⟨2134838953442566667179625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22771615503387377783249333 2134838953442566667179625)
                      ·
                        rfl

theorem cell23_4157584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_4157584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157584 prefixEnd_4157584 := by exact prefixLift 4157584
  have htrace : WordTrace (prefixWord ++ tailWord_4157584) baseStart_4157584 baseEnd_4157584 := by
    simpa [prefixWord, tailWord_4157584, baseEnd_4157584] using wordTrace_append hprefix tailTrace_4157584
  have hstable : (prefixWord ++ tailWord_4157584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157584).length < 2 ^ (prefixWord ++ tailWord_4157584).sum := by decide
  have hdescent : baseEnd_4157584 < baseStart_4157584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157587 : List Nat := [1, 1, 1, 2, 1, 2, 3, 12]
def baseStart_4157587 : Nat := 118140960795 + 4157587 * 2 ^ 59
def prefixEnd_4157587 : Nat := 4983230072969 + 3 ^ 40 * 4157587 * 2
def baseEnd_4157587 : Nat := 79068166440167783534893

theorem tailTrace_4157587 : CollatzResearch.WordTrace tailWord_4157587 prefixEnd_4157587 79068166440167783534893 := by
  unfold tailWord_4157587
  simp only [CollatzResearch.WordTrace]
  refine ⟨151639655588779833173999015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101093103725853222115999343 151639655588779833173999015)
  ·
    refine ⟨227459483383169749760998523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151639655588779833173999015 227459483383169749760998523)
    ·
      refine ⟨341189225074754624641497785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227459483383169749760998523 341189225074754624641497785)
      ·
        refine ⟨255891918806065968481123339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341189225074754624641497785 255891918806065968481123339)
        ·
          refine ⟨383837878209098952721685009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255891918806065968481123339 383837878209098952721685009)
          ·
            refine ⟨287878408656824214541263757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383837878209098952721685009 287878408656824214541263757)
            ·
              refine ⟨107954403246309080452973909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287878408656824214541263757 107954403246309080452973909)
              ·
                refine ⟨79068166440167783534893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 107954403246309080452973909 79068166440167783534893)
                ·
                  rfl

theorem cell23_4157587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 12].length) (baseStart_4157587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157587 prefixEnd_4157587 := by exact prefixLift 4157587
  have htrace : WordTrace (prefixWord ++ tailWord_4157587) baseStart_4157587 baseEnd_4157587 := by
    simpa [prefixWord, tailWord_4157587, baseEnd_4157587] using wordTrace_append hprefix tailTrace_4157587
  have hstable : (prefixWord ++ tailWord_4157587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157587).length < 2 ^ (prefixWord ++ tailWord_4157587).sum := by decide
  have hdescent : baseEnd_4157587 < baseStart_4157587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157675 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 1, 3, 2]
def baseStart_4157675 : Nat := 118140960795 + 4157675 * 2 ^ 59
def prefixEnd_4157675 : Nat := 4983230072969 + 3 ^ 40 * 4157675 * 2
def baseEnd_4157675 : Nat := 2134885680182125811141707

theorem tailTrace_4157675 : CollatzResearch.WordTrace tailWord_4157675 prefixEnd_4157675 2134885680182125811141707 := by
  unfold tailWord_4157675
  simp only [CollatzResearch.WordTrace]
  refine ⟨151642865212461024203202479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101095243474974016135468319 151642865212461024203202479)
  ·
    refine ⟨227464297818691536304803719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151642865212461024203202479 227464297818691536304803719)
    ·
      refine ⟨341196446728037304457205579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227464297818691536304803719 341196446728037304457205579)
      ·
        refine ⟨511794670092055956685808369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341196446728037304457205579 511794670092055956685808369)
        ·
          refine ⟨383846002569041967514356277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511794670092055956685808369 383846002569041967514356277)
          ·
            refine ⟨35985562740847684454470901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383846002569041967514356277 35985562740847684454470901)
            ·
              refine ⟨3373646506954470417606647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35985562740847684454470901 3373646506954470417606647)
              ·
                refine ⟨5060469760431705626409971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373646506954470417606647 5060469760431705626409971)
                ·
                  refine ⟨7590704640647558439614957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060469760431705626409971 7590704640647558439614957)
                  ·
                    refine ⟨2846514240242834414855609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7590704640647558439614957 2846514240242834414855609)
                    ·
                      refine ⟨2134885680182125811141707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846514240242834414855609 2134885680182125811141707)
                      ·
                        rfl

theorem cell23_4157675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 3, 2].length) (baseStart_4157675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157675 prefixEnd_4157675 := by exact prefixLift 4157675
  have htrace : WordTrace (prefixWord ++ tailWord_4157675) baseStart_4157675 baseEnd_4157675 := by
    simpa [prefixWord, tailWord_4157675, baseEnd_4157675] using wordTrace_append hprefix tailTrace_4157675
  have hstable : (prefixWord ++ tailWord_4157675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157675).length < 2 ^ (prefixWord ++ tailWord_4157675).sum := by decide
  have hdescent : baseEnd_4157675 < baseStart_4157675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157688 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_4157688 : Nat := 118140960795 + 4157688 * 2 ^ 59
def prefixEnd_4157688 : Nat := 4983230072969 + 3 ^ 40 * 4157688 * 2
def baseEnd_4157688 : Nat := 2134892355430634260279147

theorem tailTrace_4157688 : CollatzResearch.WordTrace tailWord_4157688 prefixEnd_4157688 2134892355430634260279147 := by
  unfold tailWord_4157688
  simp only [CollatzResearch.WordTrace]
  refine ⟨75821669680706963711712859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101095559574275951615617145 75821669680706963711712859)
  ·
    refine ⟨113732504521060445567569289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75821669680706963711712859 113732504521060445567569289)
    ·
      refine ⟨85299378390795334175676967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113732504521060445567569289 85299378390795334175676967)
      ·
        refine ⟨127949067586193001263515451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85299378390795334175676967 127949067586193001263515451)
        ·
          refine ⟨191923601379289501895273177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127949067586193001263515451 191923601379289501895273177)
          ·
            refine ⟨143942701034467126421454883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191923601379289501895273177 143942701034467126421454883)
            ·
              refine ⟨215914051551700689632182325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143942701034467126421454883 215914051551700689632182325)
              ·
                refine ⟨20241942332971939653017093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215914051551700689632182325 20241942332971939653017093)
                ·
                  refine ⟨3795364187432238684940705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20241942332971939653017093 3795364187432238684940705)
                  ·
                    refine ⟨2846523140574179013705529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3795364187432238684940705 2846523140574179013705529)
                    ·
                      refine ⟨2134892355430634260279147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846523140574179013705529 2134892355430634260279147)
                      ·
                        rfl

theorem cell23_4157688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_4157688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157688 prefixEnd_4157688 := by exact prefixLift 4157688
  have htrace : WordTrace (prefixWord ++ tailWord_4157688) baseStart_4157688 baseEnd_4157688 := by
    simpa [prefixWord, tailWord_4157688, baseEnd_4157688] using wordTrace_append hprefix tailTrace_4157688
  have hstable : (prefixWord ++ tailWord_4157688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157688).length < 2 ^ (prefixWord ++ tailWord_4157688).sum := by decide
  have hdescent : baseEnd_4157688 < baseStart_4157688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157698 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4157698 : Nat := 118140960795 + 4157698 * 2 ^ 59
def prefixEnd_4157698 : Nat := 4983230072969 + 3 ^ 40 * 4157698 * 2
def baseEnd_4157698 : Nat := 711632496745726407051367

theorem tailTrace_4157698 : CollatzResearch.WordTrace tailWord_4157698 prefixEnd_4157698 711632496745726407051367 := by
  unfold tailWord_4157698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37910926022844424782822437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101095802727585132754193165 37910926022844424782822437)
  ·
    refine ⟨7108298629283329646779207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37910926022844424782822437 7108298629283329646779207)
    ·
      refine ⟨10662447943924994470168811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7108298629283329646779207 10662447943924994470168811)
      ·
        refine ⟨15993671915887491705253217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10662447943924994470168811 15993671915887491705253217)
        ·
          refine ⟨11995253936915618778939913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15993671915887491705253217 11995253936915618778939913)
          ·
            refine ⟨8996440452686714084204935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11995253936915618778939913 8996440452686714084204935)
            ·
              refine ⟨13494660679030071126307403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8996440452686714084204935 13494660679030071126307403)
              ·
                refine ⟨20241991018545106689461105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13494660679030071126307403 20241991018545106689461105)
                ·
                  refine ⟨15181493263908830017095829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20241991018545106689461105 15181493263908830017095829)
                  ·
                    refine ⟨711632496745726407051367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15181493263908830017095829 711632496745726407051367)
                    ·
                      rfl

theorem cell23_4157698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4157698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157698 prefixEnd_4157698 := by exact prefixLift 4157698
  have htrace : WordTrace (prefixWord ++ tailWord_4157698) baseStart_4157698 baseEnd_4157698 := by
    simpa [prefixWord, tailWord_4157698, baseEnd_4157698] using wordTrace_append hprefix tailTrace_4157698
  have hstable : (prefixWord ++ tailWord_4157698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157698).length < 2 ^ (prefixWord ++ tailWord_4157698).sum := by decide
  have hdescent : baseEnd_4157698 < baseStart_4157698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157705 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 2, 2, 2]
def baseStart_4157705 : Nat := 118140960795 + 4157705 * 2 ^ 59
def prefixEnd_4157705 : Nat := 4983230072969 + 3 ^ 40 * 4157705 * 2
def baseEnd_4157705 : Nat := 2134901084601760693766569

theorem tailTrace_4157705 : CollatzResearch.WordTrace tailWord_4157705 prefixEnd_4157705 2134901084601760693766569 := by
  unfold tailWord_4157705
  simp only [CollatzResearch.WordTrace]
  refine ⟨151643959402352339326794569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101095972934901559551196379 151643959402352339326794569)
  ·
    refine ⟨113732969551764254495095927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151643959402352339326794569 113732969551764254495095927)
    ·
      refine ⟨170599454327646381742643891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113732969551764254495095927 170599454327646381742643891)
      ·
        refine ⟨255899181491469572613965837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170599454327646381742643891 255899181491469572613965837)
        ·
          refine ⟨95962193059301089730237189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255899181491469572613965837 95962193059301089730237189)
          ·
            refine ⟨17992911198618954324419473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95962193059301089730237189 17992911198618954324419473)
            ·
              refine ⟨13494683398964215743314605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17992911198618954324419473 13494683398964215743314605)
              ·
                refine ⟨5060506274611580903742977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13494683398964215743314605 5060506274611580903742977)
                ·
                  refine ⟨3795379705958685677807233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5060506274611580903742977 3795379705958685677807233)
                  ·
                    refine ⟨2846534779469014258355425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3795379705958685677807233 2846534779469014258355425)
                    ·
                      refine ⟨2134901084601760693766569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846534779469014258355425 2134901084601760693766569)
                      ·
                        rfl

theorem cell23_4157705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2, 2].length) (baseStart_4157705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157705 prefixEnd_4157705 := by exact prefixLift 4157705
  have htrace : WordTrace (prefixWord ++ tailWord_4157705) baseStart_4157705 baseEnd_4157705 := by
    simpa [prefixWord, tailWord_4157705, baseEnd_4157705] using wordTrace_append hprefix tailTrace_4157705
  have hstable : (prefixWord ++ tailWord_4157705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157705).length < 2 ^ (prefixWord ++ tailWord_4157705).sum := by decide
  have hdescent : baseEnd_4157705 < baseStart_4157705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157726 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4157726 : Nat := 118140960795 + 4157726 * 2 ^ 59
def prefixEnd_4157726 : Nat := 4983230072969 + 3 ^ 40 * 4157726 * 2
def baseEnd_4157726 : Nat := 2134911867695505111603973

theorem tailTrace_4157726 : CollatzResearch.WordTrace tailWord_4157726 prefixEnd_4157726 2134911867695505111603973 := by
  unfold tailWord_4157726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955590666909532489163629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101096483556850839942206021 18955590666909532489163629)
  ·
    refine ⟨7108346500091074683436361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18955590666909532489163629 7108346500091074683436361)
    ·
      refine ⟨5331259875068306012577271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7108346500091074683436361 5331259875068306012577271)
      ·
        refine ⟨7996889812602459018865907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331259875068306012577271 7996889812602459018865907)
        ·
          refine ⟨11995334718903688528298861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7996889812602459018865907 11995334718903688528298861)
          ·
            refine ⟨4498250519588883198112073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11995334718903688528298861 4498250519588883198112073)
            ·
              refine ⟨3373687889691662398584055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4498250519588883198112073 3373687889691662398584055)
              ·
                refine ⟨5060531834537493597876083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373687889691662398584055 5060531834537493597876083)
                ·
                  refine ⟨7590797751806240396814125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060531834537493597876083 7590797751806240396814125)
                  ·
                    refine ⟨2846549156927340148805297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7590797751806240396814125 2846549156927340148805297)
                    ·
                      refine ⟨2134911867695505111603973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846549156927340148805297 2134911867695505111603973)
                      ·
                        rfl

theorem cell23_4157726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4157726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157726 prefixEnd_4157726 := by exact prefixLift 4157726
  have htrace : WordTrace (prefixWord ++ tailWord_4157726) baseStart_4157726 baseEnd_4157726 := by
    simpa [prefixWord, tailWord_4157726, baseEnd_4157726] using wordTrace_append hprefix tailTrace_4157726
  have hstable : (prefixWord ++ tailWord_4157726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157726).length < 2 ^ (prefixWord ++ tailWord_4157726).sum := by decide
  have hdescent : baseEnd_4157726 < baseStart_4157726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157728 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 5]
def baseStart_4157728 : Nat := 118140960795 + 4157728 * 2 ^ 59
def prefixEnd_4157728 : Nat := 4983230072969 + 3 ^ 40 * 4157728 * 2
def baseEnd_4157728 : Nat := 237212543850757122642107

theorem tailTrace_4157728 : CollatzResearch.WordTrace tailWord_4157728 prefixEnd_4157728 237212543850757122642107 := by
  unfold tailWord_4157728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75822399140634507127440919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101096532187512676169921225 75822399140634507127440919)
  ·
    refine ⟨113733598710951760691161379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75822399140634507127440919 113733598710951760691161379)
    ·
      refine ⟨170600398066427641036742069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113733598710951760691161379 170600398066427641036742069)
      ·
        refine ⟨15993787318727591347194569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170600398066427641036742069 15993787318727591347194569)
        ·
          refine ⟨11995340489045693510395927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15993787318727591347194569 11995340489045693510395927)
          ·
            refine ⟨17993010733568540265593891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11995340489045693510395927 17993010733568540265593891)
            ·
              refine ⟨26989516100352810398390837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17993010733568540265593891 26989516100352810398390837)
              ·
                refine ⟨2530267134408075974849141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26989516100352810398390837 2530267134408075974849141)
                ·
                  refine ⟨237212543850757122642107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530267134408075974849141 237212543850757122642107)
                  ·
                    rfl

theorem cell23_4157728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 5].length) (baseStart_4157728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157728 prefixEnd_4157728 := by exact prefixLift 4157728
  have htrace : WordTrace (prefixWord ++ tailWord_4157728) baseStart_4157728 baseEnd_4157728 := by
    simpa [prefixWord, tailWord_4157728, baseEnd_4157728] using wordTrace_append hprefix tailTrace_4157728
  have hstable : (prefixWord ++ tailWord_4157728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157728).length < 2 ^ (prefixWord ++ tailWord_4157728).sum := by decide
  have hdescent : baseEnd_4157728 < baseStart_4157728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157771 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 5, 4]
def baseStart_4157771 : Nat := 118140960795 + 4157771 * 2 ^ 59
def prefixEnd_4157771 : Nat := 4983230072969 + 3 ^ 40 * 4157771 * 2
def baseEnd_4157771 : Nat := 711644991441652478513755

theorem tailTrace_4157771 : CollatzResearch.WordTrace tailWord_4157771 prefixEnd_4157771 711644991441652478513755 := by
  unfold tailWord_4157771
  simp only [CollatzResearch.WordTrace]
  refine ⟨151646366620113232598697167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101097577746742155065798111 151646366620113232598697167)
  ·
    refine ⟨227469549930169848898045751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151646366620113232598697167 227469549930169848898045751)
    ·
      refine ⟨341204324895254773347068627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227469549930169848898045751 341204324895254773347068627)
      ·
        refine ⟨511806487342882160020602941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341204324895254773347068627 511806487342882160020602941)
        ·
          refine ⟨191927432753580810007726103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511806487342882160020602941 191927432753580810007726103)
          ·
            refine ⟨287891149130371215011589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191927432753580810007726103 287891149130371215011589155)
            ·
              refine ⟨431836723695556822517383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287891149130371215011589155 431836723695556822517383733)
              ·
                refine ⟨40484692846458452111004725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 431836723695556822517383733 40484692846458452111004725)
                ·
                  refine ⟨3795439954355479885406693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40484692846458452111004725 3795439954355479885406693)
                  ·
                    refine ⟨711644991441652478513755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795439954355479885406693 711644991441652478513755)
                    ·
                      rfl

theorem cell23_4157771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 4].length) (baseStart_4157771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157771 prefixEnd_4157771 := by exact prefixLift 4157771
  have htrace : WordTrace (prefixWord ++ tailWord_4157771) baseStart_4157771 baseEnd_4157771 := by
    simpa [prefixWord, tailWord_4157771, baseEnd_4157771] using wordTrace_append hprefix tailTrace_4157771
  have hstable : (prefixWord ++ tailWord_4157771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157771).length < 2 ^ (prefixWord ++ tailWord_4157771).sum := by decide
  have hdescent : baseEnd_4157771 < baseStart_4157771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157778 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_4157778 : Nat := 118140960795 + 4157778 * 2 ^ 59
def prefixEnd_4157778 : Nat := 4983230072969 + 3 ^ 40 * 4157778 * 2
def baseEnd_4157778 : Nat := 2134938568689538908153733

theorem tailTrace_4157778 : CollatzResearch.WordTrace tailWord_4157778 prefixEnd_4157778 2134938568689538908153733 := by
  unfold tailWord_4157778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37911655482771968198550497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101097747954058581862801325 37911655482771968198550497)
  ·
    refine ⟨28433741612078976148912873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37911655482771968198550497 28433741612078976148912873)
    ·
      refine ⟨21325306209059232111684655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28433741612078976148912873 21325306209059232111684655)
      ·
        refine ⟨31987959313588848167526983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21325306209059232111684655 31987959313588848167526983)
        ·
          refine ⟨47981938970383272251290475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31987959313588848167526983 47981938970383272251290475)
          ·
            refine ⟨71972908455574908376935713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47981938970383272251290475 71972908455574908376935713)
            ·
              refine ⟨53979681341681181282701785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71972908455574908376935713 53979681341681181282701785)
              ·
                refine ⟨40484761006260885962026339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53979681341681181282701785 40484761006260885962026339)
                ·
                  refine ⟨60727141509391328943039509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40484761006260885962026339 60727141509391328943039509)
                  ·
                    refine ⟨2846584758252718544204977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60727141509391328943039509 2846584758252718544204977)
                    ·
                      refine ⟨2134938568689538908153733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846584758252718544204977 2134938568689538908153733)
                      ·
                        rfl

theorem cell23_4157778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_4157778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157778 prefixEnd_4157778 := by exact prefixLift 4157778
  have htrace : WordTrace (prefixWord ++ tailWord_4157778) baseStart_4157778 baseEnd_4157778 := by
    simpa [prefixWord, tailWord_4157778, baseEnd_4157778] using wordTrace_append hprefix tailTrace_4157778
  have hstable : (prefixWord ++ tailWord_4157778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157778).length < 2 ^ (prefixWord ++ tailWord_4157778).sum := by decide
  have hdescent : baseEnd_4157778 < baseStart_4157778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157801 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 6]
def baseStart_4157801 : Nat := 118140960795 + 4157801 * 2 ^ 59
def prefixEnd_4157801 : Nat := 4983230072969 + 3 ^ 40 * 4157801 * 2
def baseEnd_4157801 : Nat := 237216708749399146462903

theorem tailTrace_4157801 : CollatzResearch.WordTrace tailWord_4157801 prefixEnd_4157801 237216708749399146462903 := by
  unfold tailWord_4157801
  simp only [CollatzResearch.WordTrace]
  refine ⟨151647460810004547722289257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101098307206669698481526171 151647460810004547722289257)
  ·
    refine ⟨113735595607503410791716943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151647460810004547722289257 113735595607503410791716943)
    ·
      refine ⟨170603393411255116187575415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113735595607503410791716943 170603393411255116187575415)
      ·
        refine ⟨255905090116882674281363123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170603393411255116187575415 255905090116882674281363123)
        ·
          refine ⟨383857635175324011422044685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255905090116882674281363123 383857635175324011422044685)
          ·
            refine ⟨143946613190746504283266757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383857635175324011422044685 143946613190746504283266757)
            ·
              refine ⟨26989989973264969553112517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143946613190746504283266757 26989989973264969553112517)
              ·
                refine ⟨5060623119987181791208597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26989989973264969553112517 5060623119987181791208597)
                ·
                  refine ⟨237216708749399146462903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5060623119987181791208597 237216708749399146462903)
                  ·
                    rfl

theorem cell23_4157801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_4157801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157801 prefixEnd_4157801 := by exact prefixLift 4157801
  have htrace : WordTrace (prefixWord ++ tailWord_4157801) baseStart_4157801 baseEnd_4157801 := by
    simpa [prefixWord, tailWord_4157801, baseEnd_4157801] using wordTrace_append hprefix tailTrace_4157801
  have hstable : (prefixWord ++ tailWord_4157801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157801).length < 2 ^ (prefixWord ++ tailWord_4157801).sum := by decide
  have hdescent : baseEnd_4157801 < baseStart_4157801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157855 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4157855 : Nat := 118140960795 + 4157855 * 2 ^ 59
def prefixEnd_4157855 : Nat := 4983230072969 + 3 ^ 40 * 4157855 * 2
def baseEnd_4157855 : Nat := 2134978106699935106890879

theorem tailTrace_4157855 : CollatzResearch.WordTrace tailWord_4157855 prefixEnd_4157855 2134978106699935106890879 := by
  unfold tailWord_4157855
  simp only [CollatzResearch.WordTrace]
  refine ⟨151649430351808914944755019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101099620234539276629836679 151649430351808914944755019)
  ·
    refine ⟨227474145527713372417132529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151649430351808914944755019 227474145527713372417132529)
    ·
      refine ⟨170605609145785029312849397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227474145527713372417132529 170605609145785029312849397)
      ·
        refine ⟨15994275857417346498079631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170605609145785029312849397 15994275857417346498079631)
        ·
          refine ⟨23991413786126019747119447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15994275857417346498079631 23991413786126019747119447)
          ·
            refine ⟨35987120679189029620679171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23991413786126019747119447 35987120679189029620679171)
            ·
              refine ⟨53980681018783544431018757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35987120679189029620679171 53980681018783544431018757)
              ·
                refine ⟨10121377691021914580816017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53980681018783544431018757 10121377691021914580816017)
                ·
                  refine ⟨7591033268266435935612013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10121377691021914580816017 7591033268266435935612013)
                  ·
                    refine ⟨2846637475599913475854505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7591033268266435935612013 2846637475599913475854505)
                    ·
                      refine ⟨2134978106699935106890879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846637475599913475854505 2134978106699935106890879)
                      ·
                        rfl

theorem cell23_4157855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4157855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157855 prefixEnd_4157855 := by exact prefixLift 4157855
  have htrace : WordTrace (prefixWord ++ tailWord_4157855) baseStart_4157855 baseEnd_4157855 := by
    simpa [prefixWord, tailWord_4157855, baseEnd_4157855] using wordTrace_append hprefix tailTrace_4157855
  have hstable : (prefixWord ++ tailWord_4157855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157855).length < 2 ^ (prefixWord ++ tailWord_4157855).sum := by decide
  have hdescent : baseEnd_4157855 < baseStart_4157855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157861 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_4157861 : Nat := 118140960795 + 4157861 * 2 ^ 59
def prefixEnd_4157861 : Nat := 4983230072969 + 3 ^ 40 * 4157861 * 2
def baseEnd_4157861 : Nat := 711660395861287361138617

theorem tailTrace_4157861 : CollatzResearch.WordTrace tailWord_4157861 prefixEnd_4157861 711660395861287361138617 := by
  unfold tailWord_4157861
  simp only [CollatzResearch.WordTrace]
  refine ⟨151649649189787177969473437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101099766126524785312982291 151649649189787177969473437)
  ·
    refine ⟨56868618446170191738552539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151649649189787177969473437 56868618446170191738552539)
    ·
      refine ⟨85302927669255287607828809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56868618446170191738552539 85302927669255287607828809)
      ·
        refine ⟨63977195751941465705871607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85302927669255287607828809 63977195751941465705871607)
        ·
          refine ⟨95965793627912198558807411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63977195751941465705871607 95965793627912198558807411)
          ·
            refine ⟨143948690441868297838211117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95965793627912198558807411 143948690441868297838211117)
            ·
              refine ⟨53980758915700611689329169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143948690441868297838211117 53980758915700611689329169)
              ·
                refine ⟨40485569186775458766996877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53980758915700611689329169 40485569186775458766996877)
                ·
                  refine ⟨15182088445040797037623829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40485569186775458766996877 15182088445040797037623829)
                  ·
                    refine ⟨711660395861287361138617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15182088445040797037623829 711660395861287361138617)
                    ·
                      rfl

theorem cell23_4157861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_4157861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157861 prefixEnd_4157861 := by exact prefixLift 4157861
  have htrace : WordTrace (prefixWord ++ tailWord_4157861) baseStart_4157861 baseEnd_4157861 := by
    simpa [prefixWord, tailWord_4157861, baseEnd_4157861] using wordTrace_append hprefix tailTrace_4157861
  have hstable : (prefixWord ++ tailWord_4157861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157861).length < 2 ^ (prefixWord ++ tailWord_4157861).sum := by decide
  have hdescent : baseEnd_4157861 < baseStart_4157861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157868 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_4157868 : Nat := 118140960795 + 4157868 * 2 ^ 59
def prefixEnd_4157868 : Nat := 4983230072969 + 3 ^ 40 * 4157868 * 2
def baseEnd_4157868 : Nat := 2134984781948443556028319

theorem tailTrace_4157868 : CollatzResearch.WordTrace tailWord_4157868 prefixEnd_4157868 2134984781948443556028319 := by
  unfold tailWord_4157868
  simp only [CollatzResearch.WordTrace]
  refine ⟨75824952250380909082489129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101099936333841212109985505 75824952250380909082489129)
  ·
    refine ⟨56868714187785681811866847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75824952250380909082489129 56868714187785681811866847)
    ·
      refine ⟨85303071281678522717800271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56868714187785681811866847 85303071281678522717800271)
      ·
        refine ⟨127954606922517784076700407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85303071281678522717800271 127954606922517784076700407)
        ·
          refine ⟨191931910383776676115050611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127954606922517784076700407 191931910383776676115050611)
          ·
            refine ⟨287897865575665014172575917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191931910383776676115050611 287897865575665014172575917)
            ·
              refine ⟨107961699590874380314715969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287897865575665014172575917 107961699590874380314715969)
              ·
                refine ⟨80971274693155785236036977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107961699590874380314715969 80971274693155785236036977)
                ·
                  refine ⟨60728456019866838927027733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80971274693155785236036977 60728456019866838927027733)
                  ·
                    refine ⟨2846646375931258074704425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60728456019866838927027733 2846646375931258074704425)
                    ·
                      refine ⟨2134984781948443556028319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846646375931258074704425 2134984781948443556028319)
                      ·
                        rfl

theorem cell23_4157868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_4157868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157868 prefixEnd_4157868 := by exact prefixLift 4157868
  have htrace : WordTrace (prefixWord ++ tailWord_4157868) baseStart_4157868 baseEnd_4157868 := by
    simpa [prefixWord, tailWord_4157868, baseEnd_4157868] using wordTrace_append hprefix tailTrace_4157868
  have hstable : (prefixWord ++ tailWord_4157868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157868).length < 2 ^ (prefixWord ++ tailWord_4157868).sum := by decide
  have hdescent : baseEnd_4157868 < baseStart_4157868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157898 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4157898 : Nat := 118140960795 + 4157898 * 2 ^ 59
def prefixEnd_4157898 : Nat := 4983230072969 + 3 ^ 40 * 4157898 * 2
def baseEnd_4157898 : Nat := 2135000186368078438653181

theorem tailTrace_4157898 : CollatzResearch.WordTrace tailWord_4157898 prefixEnd_4157898 2135000186368078438653181 := by
  unfold tailWord_4157898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37912749672663283322142587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101100665793768755525713565 37912749672663283322142587)
  ·
    refine ⟨56869124508994924983213881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37912749672663283322142587 56869124508994924983213881)
    ·
      refine ⟨42651843381746193737410411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56869124508994924983213881 42651843381746193737410411)
      ·
        refine ⟨63977765072619290606115617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42651843381746193737410411 63977765072619290606115617)
        ·
          refine ⟨47983323804464467954586713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63977765072619290606115617 47983323804464467954586713)
          ·
            refine ⟨35987492853348350965940035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47983323804464467954586713 35987492853348350965940035)
            ·
              refine ⟨53981239280022526448910053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35987492853348350965940035 53981239280022526448910053)
              ·
                refine ⟨10121482365004223709170635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53981239280022526448910053 10121482365004223709170635)
                ·
                  refine ⟨15182223547506335563755953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10121482365004223709170635 15182223547506335563755953)
                  ·
                    refine ⟨11386667660629751672816965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15182223547506335563755953 11386667660629751672816965)
                    ·
                      refine ⟨2135000186368078438653181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11386667660629751672816965 2135000186368078438653181)
                      ·
                        rfl

theorem cell23_4157898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4157898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157898 prefixEnd_4157898 := by exact prefixLift 4157898
  have htrace : WordTrace (prefixWord ++ tailWord_4157898) baseStart_4157898 baseEnd_4157898 := by
    simpa [prefixWord, tailWord_4157898, baseEnd_4157898] using wordTrace_append hprefix tailTrace_4157898
  have hstable : (prefixWord ++ tailWord_4157898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157898).length < 2 ^ (prefixWord ++ tailWord_4157898).sum := by decide
  have hdescent : baseEnd_4157898 < baseStart_4157898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157908 : List Nat := [2, 4, 1, 2, 2, 2, 10]
def baseStart_4157908 : Nat := 118140960795 + 4157908 * 2 ^ 59
def prefixEnd_4157908 : Nat := 4983230072969 + 3 ^ 40 * 4157908 * 2
def baseEnd_4157908 : Nat := 26358090384871893821335

theorem tailTrace_4157908 : CollatzResearch.WordTrace tailWord_4157908 prefixEnd_4157908 26358090384871893821335 := by
  unfold tailWord_4157908
  simp only [CollatzResearch.WordTrace]
  refine ⟨75825681710308452498217189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101100908947077936664289585 75825681710308452498217189)
  ·
    refine ⟨14217315320682834843415723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75825681710308452498217189 14217315320682834843415723)
    ·
      refine ⟨21325972981024252265123585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14217315320682834843415723 21325972981024252265123585)
      ·
        refine ⟨15994479735768189198842689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21325972981024252265123585 15994479735768189198842689)
        ·
          refine ⟨11995859801826141899132017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15994479735768189198842689 11995859801826141899132017)
          ·
            refine ⟨8996894851369606424349013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11995859801826141899132017 8996894851369606424349013)
            ·
              refine ⟨26358090384871893821335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8996894851369606424349013 26358090384871893821335)
              ·
                rfl

theorem cell23_4157908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 10].length) (baseStart_4157908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157908 prefixEnd_4157908 := by exact prefixLift 4157908
  have htrace : WordTrace (prefixWord ++ tailWord_4157908) baseStart_4157908 baseEnd_4157908 := by
    simpa [prefixWord, tailWord_4157908, baseEnd_4157908] using wordTrace_append hprefix tailTrace_4157908
  have hstable : (prefixWord ++ tailWord_4157908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157908).length < 2 ^ (prefixWord ++ tailWord_4157908).sum := by decide
  have hdescent : baseEnd_4157908 < baseStart_4157908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157911 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_4157911 : Nat := 118140960795 + 4157911 * 2 ^ 59
def prefixEnd_4157911 : Nat := 4983230072969 + 3 ^ 40 * 4157911 * 2
def baseEnd_4157911 : Nat := 2135006861616586887790621

theorem tailTrace_4157911 : CollatzResearch.WordTrace tailWord_4157911 prefixEnd_4157911 2135006861616586887790621 := by
  unfold tailWord_4157911
  simp only [CollatzResearch.WordTrace]
  refine ⟨151651472839606036508793587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101100981893070691005862391 151651472839606036508793587)
  ·
    refine ⟨227477209259409054763190381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151651472839606036508793587 227477209259409054763190381)
    ·
      refine ⟨85303953472278395536196393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227477209259409054763190381 85303953472278395536196393)
      ·
        refine ⟨63977965104208796652147295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85303953472278395536196393 63977965104208796652147295)
        ·
          refine ⟨95966947656313194978220943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63977965104208796652147295 95966947656313194978220943)
          ·
            refine ⟨143950421484469792467331415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95966947656313194978220943 143950421484469792467331415)
            ·
              refine ⟨215925632226704688700997123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143950421484469792467331415 215925632226704688700997123)
              ·
                refine ⟨323888448340057033051495685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215925632226704688700997123 323888448340057033051495685)
                ·
                  refine ⟨60729084063760693697155441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323888448340057033051495685 60729084063760693697155441)
                  ·
                    refine ⟨45546813047820520272866581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60729084063760693697155441 45546813047820520272866581)
                    ·
                      refine ⟨2135006861616586887790621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45546813047820520272866581 2135006861616586887790621)
                      ·
                        rfl

theorem cell23_4157911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_4157911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157911 prefixEnd_4157911 := by exact prefixLift 4157911
  have htrace : WordTrace (prefixWord ++ tailWord_4157911) baseStart_4157911 baseEnd_4157911 := by
    simpa [prefixWord, tailWord_4157911, baseEnd_4157911] using wordTrace_append hprefix tailTrace_4157911
  have hstable : (prefixWord ++ tailWord_4157911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157911).length < 2 ^ (prefixWord ++ tailWord_4157911).sum := by decide
  have hdescent : baseEnd_4157911 < baseStart_4157911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157919 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 1, 2, 2]
def baseStart_4157919 : Nat := 118140960795 + 4157919 * 2 ^ 59
def prefixEnd_4157919 : Nat := 4983230072969 + 3 ^ 40 * 4157919 * 2
def baseEnd_4157919 : Nat := 2135010969461822856490585

theorem tailTrace_4157919 : CollatzResearch.WordTrace tailWord_4157919 prefixEnd_4157919 2135010969461822856490585 := by
  unfold tailWord_4157919
  simp only [CollatzResearch.WordTrace]
  refine ⟨151651764623577053875084811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101101176415718035916723207 151651764623577053875084811)
  ·
    refine ⟨227477646935365580812627217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151651764623577053875084811 227477646935365580812627217)
    ·
      refine ⟨170608235201524185609470413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227477646935365580812627217 170608235201524185609470413)
      ·
        refine ⟨63978088200571569603551405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170608235201524185609470413 63978088200571569603551405)
        ·
          refine ⟨23991783075214338601331777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63978088200571569603551405 23991783075214338601331777)
          ·
            refine ⟨17993837306410753950998833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23991783075214338601331777 17993837306410753950998833)
            ·
              refine ⟨13495377979808065463249125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17993837306410753950998833 13495377979808065463249125)
              ·
                refine ⟨2530383371214012274359211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13495377979808065463249125 2530383371214012274359211)
                ·
                  refine ⟨3795575056821018411538817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530383371214012274359211 3795575056821018411538817)
                  ·
                    refine ⟨2846681292615763808654113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3795575056821018411538817 2846681292615763808654113)
                    ·
                      refine ⟨2135010969461822856490585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846681292615763808654113 2135010969461822856490585)
                      ·
                        rfl

theorem cell23_4157919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_4157919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157919 prefixEnd_4157919 := by exact prefixLift 4157919
  have htrace : WordTrace (prefixWord ++ tailWord_4157919) baseStart_4157919 baseEnd_4157919 := by
    simpa [prefixWord, tailWord_4157919, baseEnd_4157919] using wordTrace_append hprefix tailTrace_4157919
  have hstable : (prefixWord ++ tailWord_4157919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157919).length < 2 ^ (prefixWord ++ tailWord_4157919).sum := by decide
  have hdescent : baseEnd_4157919 < baseStart_4157919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157945 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 3, 3, 2]
def baseStart_4157945 : Nat := 118140960795 + 4157945 * 2 ^ 59
def prefixEnd_4157945 : Nat := 4983230072969 + 3 ^ 40 * 4157945 * 2
def baseEnd_4157945 : Nat := 2135024319958839754765465

theorem tailTrace_4157945 : CollatzResearch.WordTrace tailWord_4157945 prefixEnd_4157945 2135024319958839754765465 := by
  unfold tailWord_4157945
  simp only [CollatzResearch.WordTrace]
  refine ⟨151652712921482860315531289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101101808614321906877020859 151652712921482860315531289)
  ·
    refine ⟨113739534691112145236648467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151652712921482860315531289 113739534691112145236648467)
    ·
      refine ⟨170609302036668217854972701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113739534691112145236648467 170609302036668217854972701)
      ·
        refine ⟨63978488263750581695614763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170609302036668217854972701 63978488263750581695614763)
        ·
          refine ⟨95967732395625872543422145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63978488263750581695614763 95967732395625872543422145)
          ·
            refine ⟨71975799296719404407566609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95967732395625872543422145 71975799296719404407566609)
            ·
              refine ⟨53981849472539553305674957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71975799296719404407566609 53981849472539553305674957)
              ·
                refine ⟨20243193552202332489628109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53981849472539553305674957 20243193552202332489628109)
                ·
                  refine ⟨7591197582075874683610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20243193552202332489628109 7591197582075874683610541)
                  ·
                    refine ⟨2846699093278453006353953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7591197582075874683610541 2846699093278453006353953)
                    ·
                      refine ⟨2135024319958839754765465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846699093278453006353953 2135024319958839754765465)
                      ·
                        rfl

theorem cell23_4157945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_4157945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157945 prefixEnd_4157945 := by exact prefixLift 4157945
  have htrace : WordTrace (prefixWord ++ tailWord_4157945) baseStart_4157945 baseEnd_4157945 := by
    simpa [prefixWord, tailWord_4157945, baseEnd_4157945] using wordTrace_append hprefix tailTrace_4157945
  have hstable : (prefixWord ++ tailWord_4157945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157945).length < 2 ^ (prefixWord ++ tailWord_4157945).sum := by decide
  have hdescent : baseEnd_4157945 < baseStart_4157945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4157962 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_4157962 : Nat := 118140960795 + 4157962 * 2 ^ 59
def prefixEnd_4157962 : Nat := 4983230072969 + 3 ^ 40 * 4157962 * 2
def baseEnd_4157962 : Nat := 2135033049129966188252887

theorem tailTrace_4157962 : CollatzResearch.WordTrace tailWord_4157962 prefixEnd_4157962 2135033049129966188252887 := by
  unfold tailWord_4157962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37913333240605318054725035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101102221974947514812600093 37913333240605318054725035)
  ·
    refine ⟨56869999860907977082087553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37913333240605318054725035 56869999860907977082087553)
    ·
      refine ⟨42652499895680982811565665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56869999860907977082087553 42652499895680982811565665)
      ·
        refine ⟨31989374921760737108674249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42652499895680982811565665 31989374921760737108674249)
        ·
          refine ⟨23992031191320552831505687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31989374921760737108674249 23992031191320552831505687)
          ·
            refine ⟨35988046786980829247258531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23992031191320552831505687 35988046786980829247258531)
            ·
              refine ⟨53982070180471243870887797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35988046786980829247258531 53982070180471243870887797)
              ·
                refine ⟨5060819079419179112895731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53982070180471243870887797 5060819079419179112895731)
                ·
                  refine ⟨7591228619128768669343597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5060819079419179112895731 7591228619128768669343597)
                  ·
                    refine ⟨2846710732173288251003849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7591228619128768669343597 2846710732173288251003849)
                    ·
                      refine ⟨2135033049129966188252887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846710732173288251003849 2135033049129966188252887)
                      ·
                        rfl

theorem cell23_4157962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_4157962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4157962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4157962 prefixEnd_4157962 := by exact prefixLift 4157962
  have htrace : WordTrace (prefixWord ++ tailWord_4157962) baseStart_4157962 baseEnd_4157962 := by
    simpa [prefixWord, tailWord_4157962, baseEnd_4157962] using wordTrace_append hprefix tailTrace_4157962
  have hstable : (prefixWord ++ tailWord_4157962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4157962).length < 2 ^ (prefixWord ++ tailWord_4157962).sum := by decide
  have hdescent : baseEnd_4157962 < baseStart_4157962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4157962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158015 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 5]
def baseStart_4158015 : Nat := 118140960795 + 4158015 * 2 ^ 59
def prefixEnd_4158015 : Nat := 4983230072969 + 3 ^ 40 * 4158015 * 2
def baseEnd_4158015 : Nat := 237228918178294942321127

theorem tailTrace_4158015 : CollatzResearch.WordTrace tailWord_4158015 prefixEnd_4158015 237228918178294942321127 := by
  unfold tailWord_4158015
  simp only [CollatzResearch.WordTrace]
  refine ⟨151655266031229262270579499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101103510687486174847052999 151655266031229262270579499)
  ·
    refine ⟨227482899046843893405869249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151655266031229262270579499 227482899046843893405869249)
    ·
      refine ⟨170612174285132920054401937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227482899046843893405869249 170612174285132920054401937)
      ·
        refine ⟨127959130713849690040801453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170612174285132920054401937 127959130713849690040801453)
        ·
          refine ⟨47984674017693633765300545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127959130713849690040801453 47984674017693633765300545)
          ·
            refine ⟨35988505513270225323975409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47984674017693633765300545 35988505513270225323975409)
            ·
              refine ⟨26991379134952668992981557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35988505513270225323975409 26991379134952668992981557)
              ·
                refine ⟨2530441793901812718092021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26991379134952668992981557 2530441793901812718092021)
                ·
                  refine ⟨237228918178294942321127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530441793901812718092021 237228918178294942321127)
                  ·
                    rfl

theorem cell23_4158015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 5].length) (baseStart_4158015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158015 prefixEnd_4158015 := by exact prefixLift 4158015
  have htrace : WordTrace (prefixWord ++ tailWord_4158015) baseStart_4158015 baseEnd_4158015 := by
    simpa [prefixWord, tailWord_4158015, baseEnd_4158015] using wordTrace_append hprefix tailTrace_4158015
  have hstable : (prefixWord ++ tailWord_4158015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158015).length < 2 ^ (prefixWord ++ tailWord_4158015).sum := by decide
  have hdescent : baseEnd_4158015 < baseStart_4158015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158062 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4158062 : Nat := 118140960795 + 4158062 * 2 ^ 59
def prefixEnd_4158062 : Nat := 4983230072969 + 3 ^ 40 * 4158062 * 2
def baseEnd_4158062 : Nat := 711694799065138599000809

theorem tailTrace_4158062 : CollatzResearch.WordTrace tailWord_4158062 prefixEnd_4158062 711694799065138599000809 := by
  unfold tailWord_4158062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18957122532757373662192555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101104653508039326198360293 18957122532757373662192555)
  ·
    refine ⟨28435683799136060493288833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18957122532757373662192555 28435683799136060493288833)
    ·
      refine ⟨21326762849352045369966625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28435683799136060493288833 21326762849352045369966625)
      ·
        refine ⟨15995072137014034027474969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21326762849352045369966625 15995072137014034027474969)
        ·
          refine ⟨11996304102760525520606227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15995072137014034027474969 11996304102760525520606227)
          ·
            refine ⟨17994456154140788280909341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11996304102760525520606227 17994456154140788280909341)
            ·
              refine ⟨6747921057802795605341003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17994456154140788280909341 6747921057802795605341003)
              ·
                refine ⟨10121881586704193408011505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6747921057802795605341003 10121881586704193408011505)
                ·
                  refine ⟨7591411190028145056008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10121881586704193408011505 7591411190028145056008629)
                  ·
                    refine ⟨711694799065138599000809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7591411190028145056008629 711694799065138599000809)
                    ·
                      rfl

theorem cell23_4158062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4158062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158062 prefixEnd_4158062 := by exact prefixLift 4158062
  have htrace : WordTrace (prefixWord ++ tailWord_4158062) baseStart_4158062 baseEnd_4158062 := by
    simpa [prefixWord, tailWord_4158062, baseEnd_4158062] using wordTrace_append hprefix tailTrace_4158062
  have hstable : (prefixWord ++ tailWord_4158062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158062).length < 2 ^ (prefixWord ++ tailWord_4158062).sum := by decide
  have hdescent : baseEnd_4158062 < baseStart_4158062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158185 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_4158185 : Nat := 118140960795 + 4158185 * 2 ^ 59
def prefixEnd_4158185 : Nat := 4983230072969 + 3 ^ 40 * 4158185 * 2
def baseEnd_4158185 : Nat := 2135147555315918815764361

theorem tailTrace_4158185 : CollatzResearch.WordTrace tailWord_4158185 prefixEnd_4158185 2135147555315918815764361 := by
  unfold tailWord_4158185
  simp only [CollatzResearch.WordTrace]
  refine ⟨151661466440613381304268009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101107644293742254202845339 151661466440613381304268009)
  ·
    refine ⟨113746099830460035978201007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151661466440613381304268009 113746099830460035978201007)
    ·
      refine ⟨170619149745690053967301511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113746099830460035978201007 170619149745690053967301511)
      ·
        refine ⟨255928724618535080950952267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170619149745690053967301511 255928724618535080950952267)
        ·
          refine ⟨383893086927802621426428401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255928724618535080950952267 383893086927802621426428401)
          ·
            refine ⟨287919815195851966069821301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383893086927802621426428401 287919815195851966069821301)
            ·
              refine ⟨26992482674611121819045747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287919815195851966069821301 26992482674611121819045747)
              ·
                refine ⟨40488724011916682728568621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26992482674611121819045747 40488724011916682728568621)
                ·
                  refine ⟨15183271504468756023213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40488724011916682728568621 15183271504468756023213233)
                  ·
                    refine ⟨11387453628351567017409925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15183271504468756023213233 11387453628351567017409925)
                    ·
                      refine ⟨2135147555315918815764361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11387453628351567017409925 2135147555315918815764361)
                      ·
                        rfl

theorem cell23_4158185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_4158185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158185 prefixEnd_4158185 := by exact prefixLift 4158185
  have htrace : WordTrace (prefixWord ++ tailWord_4158185) baseStart_4158185 baseEnd_4158185 := by
    simpa [prefixWord, tailWord_4158185, baseEnd_4158185] using wordTrace_append hprefix tailTrace_4158185
  have hstable : (prefixWord ++ tailWord_4158185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158185).length < 2 ^ (prefixWord ++ tailWord_4158185).sum := by decide
  have hdescent : baseEnd_4158185 < baseStart_4158185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158249 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 1, 3, 2]
def baseStart_4158249 : Nat := 118140960795 + 4158249 * 2 ^ 59
def prefixEnd_4158249 : Nat := 4983230072969 + 3 ^ 40 * 4158249 * 2
def baseEnd_4158249 : Nat := 2135180418077806565364067

theorem tailTrace_4158249 : CollatzResearch.WordTrace tailWord_4158249 prefixEnd_4158249 2135180418077806565364067 := by
  unfold tailWord_4158249
  simp only [CollatzResearch.WordTrace]
  refine ⟨151663800712381520234597801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101109200474921013489731867 151663800712381520234597801)
  ·
    refine ⟨113747850534286140175948351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151663800712381520234597801 113747850534286140175948351)
    ·
      refine ⟨170621775801429210263922527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113747850534286140175948351 170621775801429210263922527)
      ·
        refine ⟨255932663702143815395883791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170621775801429210263922527 255932663702143815395883791)
        ·
          refine ⟨383898995553215723093825687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255932663702143815395883791 383898995553215723093825687)
          ·
            refine ⟨575848493329823584640738531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383898995553215723093825687 575848493329823584640738531)
            ·
              refine ⟨863772739994735376961107797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575848493329823584640738531 863772739994735376961107797)
              ·
                refine ⟨5061168398406652599381491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 863772739994735376961107797 5061168398406652599381491)
                ·
                  refine ⟨7591752597609978899072237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061168398406652599381491 7591752597609978899072237)
                  ·
                    refine ⟨2846907224103742087152089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7591752597609978899072237 2846907224103742087152089)
                    ·
                      refine ⟨2135180418077806565364067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2846907224103742087152089 2135180418077806565364067)
                      ·
                        rfl

theorem cell23_4158249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3, 2].length) (baseStart_4158249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158249 prefixEnd_4158249 := by exact prefixLift 4158249
  have htrace : WordTrace (prefixWord ++ tailWord_4158249) baseStart_4158249 baseEnd_4158249 := by
    simpa [prefixWord, tailWord_4158249, baseEnd_4158249] using wordTrace_append hprefix tailTrace_4158249
  have hstable : (prefixWord ++ tailWord_4158249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158249).length < 2 ^ (prefixWord ++ tailWord_4158249).sum := by decide
  have hdescent : baseEnd_4158249 < baseStart_4158249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158250 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4158250 : Nat := 118140960795 + 4158250 * 2 ^ 59
def prefixEnd_4158250 : Nat := 4983230072969 + 3 ^ 40 * 4158250 * 2
def baseEnd_4158250 : Nat := 711726977186153687150521

theorem tailTrace_4158250 : CollatzResearch.WordTrace tailWord_4158250 prefixEnd_4158250 711726977186153687150521 := by
  unfold tailWord_4158250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37915959296344474351346051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101109224790251931603589469 37915959296344474351346051)
  ·
    refine ⟨56873938944516711527019077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37915959296344474351346051 56873938944516711527019077)
    ·
      refine ⟨10663863552096883411316077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56873938944516711527019077 10663863552096883411316077)
      ·
        refine ⟨3998948832036331279243529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10663863552096883411316077 3998948832036331279243529)
        ·
          refine ⟨2999211624027248459432647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3998948832036331279243529 2999211624027248459432647)
          ·
            refine ⟨4498817436040872689148971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999211624027248459432647 4498817436040872689148971)
            ·
              refine ⟨6748226154061309033723457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498817436040872689148971 6748226154061309033723457)
              ·
                refine ⟨5061169615545981775292593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748226154061309033723457 5061169615545981775292593)
                ·
                  refine ⟨3795877211659486331469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5061169615545981775292593 3795877211659486331469445)
                  ·
                    refine ⟨711726977186153687150521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3795877211659486331469445 711726977186153687150521)
                    ·
                      rfl

theorem cell23_4158250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4158250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158250 prefixEnd_4158250 := by exact prefixLift 4158250
  have htrace : WordTrace (prefixWord ++ tailWord_4158250) baseStart_4158250 baseEnd_4158250 := by
    simpa [prefixWord, tailWord_4158250, baseEnd_4158250] using wordTrace_append hprefix tailTrace_4158250
  have hstable : (prefixWord ++ tailWord_4158250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158250).length < 2 ^ (prefixWord ++ tailWord_4158250).sum := by decide
  have hdescent : baseEnd_4158250 < baseStart_4158250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158273 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4158273 : Nat := 118140960795 + 4158273 * 2 ^ 59
def prefixEnd_4158273 : Nat := 4983230072969 + 3 ^ 40 * 4158273 * 2
def baseEnd_4158273 : Nat := 2135192741613514471463957

theorem tailTrace_4158273 : CollatzResearch.WordTrace tailWord_4158273 prefixEnd_4158273 2135192741613514471463957 := by
  unfold tailWord_4158273
  simp only [CollatzResearch.WordTrace]
  refine ⟨151664676064294572333471473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101109784042863048222314315 151664676064294572333471473)
  ·
    refine ⟨113748507048220929250103605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151664676064294572333471473 113748507048220929250103605)
    ·
      refine ⟨10663922535770712117197213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113748507048220929250103605 10663922535770712117197213)
      ·
        refine ⟨3998970950914017043948955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10663922535770712117197213 3998970950914017043948955)
        ·
          refine ⟨5998456426371025565923433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998970950914017043948955 5998456426371025565923433)
          ·
            refine ⟨4498842319778269174442575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5998456426371025565923433 4498842319778269174442575)
            ·
              refine ⟨6748263479667403761663863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4498842319778269174442575 6748263479667403761663863)
              ·
                refine ⟨10122395219501105642495795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6748263479667403761663863 10122395219501105642495795)
                ·
                  refine ⟨15183592829251658463743693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10122395219501105642495795 15183592829251658463743693)
                  ·
                    refine ⟨5693847310969371923903885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15183592829251658463743693 5693847310969371923903885)
                    ·
                      refine ⟨2135192741613514471463957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5693847310969371923903885 2135192741613514471463957)
                      ·
                        rfl

theorem cell23_4158273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4158273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158273 prefixEnd_4158273 := by exact prefixLift 4158273
  have htrace : WordTrace (prefixWord ++ tailWord_4158273) baseStart_4158273 baseEnd_4158273 := by
    simpa [prefixWord, tailWord_4158273, baseEnd_4158273] using wordTrace_append hprefix tailTrace_4158273
  have hstable : (prefixWord ++ tailWord_4158273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158273).length < 2 ^ (prefixWord ++ tailWord_4158273).sum := by decide
  have hdescent : baseEnd_4158273 < baseStart_4158273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158372 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4158372 : Nat := 118140960795 + 4158372 * 2 ^ 59
def prefixEnd_4158372 : Nat := 4983230072969 + 3 ^ 40 * 4158372 * 2
def baseEnd_4158372 : Nat := 2135243576198309584126001

theorem tailTrace_4158372 : CollatzResearch.WordTrace tailWord_4158372 prefixEnd_4158372 2135243576198309584126001 := by
  unfold tailWord_4158372
  simp only [CollatzResearch.WordTrace]
  refine ⟨75834143445467956120662685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101112191260623941494216913 75834143445467956120662685)
  ·
    refine ⟨28437803792050483545248507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75834143445467956120662685 28437803792050483545248507)
    ·
      refine ⟨42656705688075725317872761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28437803792050483545248507 42656705688075725317872761)
      ·
        refine ⟨31992529266056793988404571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42656705688075725317872761 31992529266056793988404571)
        ·
          refine ⟨47988793899085190982606857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31992529266056793988404571 47988793899085190982606857)
          ·
            refine ⟨35991595424313893236955143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47988793899085190982606857 35991595424313893236955143)
            ·
              refine ⟨53987393136470839855432715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35991595424313893236955143 53987393136470839855432715)
              ·
                refine ⟨80981089704706259783149073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53987393136470839855432715 80981089704706259783149073)
                ·
                  refine ⟨60735817278529694837361805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80981089704706259783149073 60735817278529694837361805)
                  ·
                    refine ⟨22775931479448635564010677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60735817278529694837361805 22775931479448635564010677)
                    ·
                      refine ⟨2135243576198309584126001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22775931479448635564010677 2135243576198309584126001)
                      ·
                        rfl

theorem cell23_4158372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4158372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158372 prefixEnd_4158372 := by exact prefixLift 4158372
  have htrace : WordTrace (prefixWord ++ tailWord_4158372) baseStart_4158372 baseEnd_4158372 := by
    simpa [prefixWord, tailWord_4158372, baseEnd_4158372] using wordTrace_append hprefix tailTrace_4158372
  have hstable : (prefixWord ++ tailWord_4158372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158372).length < 2 ^ (prefixWord ++ tailWord_4158372).sum := by decide
  have hdescent : baseEnd_4158372 < baseStart_4158372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158389 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_4158389 : Nat := 118140960795 + 4158389 * 2 ^ 59
def prefixEnd_4158389 : Nat := 4983230072969 + 3 ^ 40 * 4158389 * 2
def baseEnd_4158389 : Nat := 2135252305369436017613423

theorem tailTrace_4158389 : CollatzResearch.WordTrace tailWord_4158389 prefixEnd_4158389 2135252305369436017613423 := by
  unfold tailWord_4158389
  simp only [CollatzResearch.WordTrace]
  refine ⟨151668906931874324144694221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101112604621249549429796147 151668906931874324144694221)
  ·
    refine ⟨56875840099452871554260333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151668906931874324144694221 56875840099452871554260333)
    ·
      refine ⟨21328440037294826832847625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56875840099452871554260333 21328440037294826832847625)
      ·
        refine ⟨15996330027971120124635719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21328440037294826832847625 15996330027971120124635719)
        ·
          refine ⟨23994495041956680186953579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15996330027971120124635719 23994495041956680186953579)
          ·
            refine ⟨35991742562935020280430369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23994495041956680186953579 35991742562935020280430369)
            ·
              refine ⟨26993806922201265210322777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35991742562935020280430369 26993806922201265210322777)
              ·
                refine ⟨20245355191650948907742083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26993806922201265210322777 20245355191650948907742083)
                ·
                  refine ⟨30368032787476423361613125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20245355191650948907742083 30368032787476423361613125)
                  ·
                    refine ⟨5694006147651829380302461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30368032787476423361613125 5694006147651829380302461)
                    ·
                      refine ⟨2135252305369436017613423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694006147651829380302461 2135252305369436017613423)
                      ·
                        rfl

theorem cell23_4158389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_4158389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158389 prefixEnd_4158389 := by exact prefixLift 4158389
  have htrace : WordTrace (prefixWord ++ tailWord_4158389) baseStart_4158389 baseEnd_4158389 := by
    simpa [prefixWord, tailWord_4158389, baseEnd_4158389] using wordTrace_append hprefix tailTrace_4158389
  have hstable : (prefixWord ++ tailWord_4158389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158389).length < 2 ^ (prefixWord ++ tailWord_4158389).sum := by decide
  have hdescent : baseEnd_4158389 < baseStart_4158389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158426 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_4158426 : Nat := 118140960795 + 4158426 * 2 ^ 59
def prefixEnd_4158426 : Nat := 4983230072969 + 3 ^ 40 * 4158426 * 2
def baseEnd_4158426 : Nat := 237252367128183596983417

theorem tailTrace_4158426 : CollatzResearch.WordTrace tailWord_4158426 prefixEnd_4158426 237252367128183596983417 := by
  unfold tailWord_4158426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37917564108185069865947783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101113504288493519642527421 37917564108185069865947783)
  ·
    refine ⟨56876346162277604798921675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37917564108185069865947783 56876346162277604798921675)
    ·
      refine ⟨85314519243416407198382513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56876346162277604798921675 85314519243416407198382513)
      ·
        refine ⟨63985889432562305398786885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85314519243416407198382513 63985889432562305398786885)
        ·
          refine ⟨11997354268605432262272541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63985889432562305398786885 11997354268605432262272541)
          ·
            refine ⟨4499007850727037098352203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11997354268605432262272541 4499007850727037098352203)
            ·
              refine ⟨6748511776090555647528305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499007850727037098352203 6748511776090555647528305)
              ·
                refine ⟨5061383832067916735646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6748511776090555647528305 5061383832067916735646229)
                ·
                  refine ⟨237252367128183596983417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5061383832067916735646229 237252367128183596983417)
                  ·
                    rfl

theorem cell23_4158426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_4158426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158426 prefixEnd_4158426 := by exact prefixLift 4158426
  have htrace : WordTrace (prefixWord ++ tailWord_4158426) baseStart_4158426 baseEnd_4158426 := by
    simpa [prefixWord, tailWord_4158426, baseEnd_4158426] using wordTrace_append hprefix tailTrace_4158426
  have hstable : (prefixWord ++ tailWord_4158426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158426).length < 2 ^ (prefixWord ++ tailWord_4158426).sum := by decide
  have hdescent : baseEnd_4158426 < baseStart_4158426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158429 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4158429 : Nat := 118140960795 + 4158429 * 2 ^ 59
def prefixEnd_4158429 : Nat := 4983230072969 + 3 ^ 40 * 4158429 * 2
def baseEnd_4158429 : Nat := 2135272844595615861113239

theorem tailTrace_4158429 : CollatzResearch.WordTrace tailWord_4158429 prefixEnd_4158429 2135272844595615861113239 := by
  unfold tailWord_4158429
  simp only [CollatzResearch.WordTrace]
  refine ⟨151670365851729410976150341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101113577234486273984100227 151670365851729410976150341)
  ·
    refine ⟨28438193597199264558028189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151670365851729410976150341 28438193597199264558028189)
    ·
      refine ⟨10664322598949724209260571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28438193597199264558028189 10664322598949724209260571)
      ·
        refine ⟨15996483898424586313890857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10664322598949724209260571 15996483898424586313890857)
        ·
          refine ⟨11997362923818439735418143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15996483898424586313890857 11997362923818439735418143)
          ·
            refine ⟨17996044385727659603127215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997362923818439735418143 17996044385727659603127215)
            ·
              refine ⟨26994066578591489404690823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996044385727659603127215 26994066578591489404690823)
              ·
                refine ⟨40491099867887234107036235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26994066578591489404690823 40491099867887234107036235)
                ·
                  refine ⟨60736649801830851160554353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40491099867887234107036235 60736649801830851160554353)
                  ·
                    refine ⟨45552487351373138370415765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60736649801830851160554353 45552487351373138370415765)
                    ·
                      refine ⟨2135272844595615861113239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45552487351373138370415765 2135272844595615861113239)
                      ·
                        rfl

theorem cell23_4158429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4158429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158429 prefixEnd_4158429 := by exact prefixLift 4158429
  have htrace : WordTrace (prefixWord ++ tailWord_4158429) baseStart_4158429 baseEnd_4158429 := by
    simpa [prefixWord, tailWord_4158429, baseEnd_4158429] using wordTrace_append hprefix tailTrace_4158429
  have hstable : (prefixWord ++ tailWord_4158429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158429).length < 2 ^ (prefixWord ++ tailWord_4158429).sum := by decide
  have hdescent : baseEnd_4158429 < baseStart_4158429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158459 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 8, 2]
def baseStart_4158459 : Nat := 118140960795 + 4158459 * 2 ^ 59
def prefixEnd_4158459 : Nat := 4983230072969 + 3 ^ 40 * 4158459 * 2
def baseEnd_4158459 : Nat := 2135288249015250743738101

theorem tailTrace_4158459 : CollatzResearch.WordTrace tailWord_4158459 prefixEnd_4158459 2135288249015250743738101 := by
  unfold tailWord_4158459
  simp only [CollatzResearch.WordTrace]
  refine ⟨151671460041620726099742431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101114306694413817399828287 151671460041620726099742431)
  ·
    refine ⟨227507190062431089149613647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151671460041620726099742431 227507190062431089149613647)
    ·
      refine ⟨341260785093646633724420471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227507190062431089149613647 341260785093646633724420471)
      ·
        refine ⟨511891177640469950586630707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341260785093646633724420471 511891177640469950586630707)
        ·
          refine ⟨767836766460704925879946061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511891177640469950586630707 767836766460704925879946061)
          ·
            refine ⟨287938787422764347204979773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767836766460704925879946061 287938787422764347204979773)
            ·
              refine ⟨107977045283536630201867415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287938787422764347204979773 107977045283536630201867415)
              ·
                refine ⟨161965567925304945302801123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107977045283536630201867415 161965567925304945302801123)
                ·
                  refine ⟨242948351887957417954201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161965567925304945302801123 242948351887957417954201685)
                  ·
                    refine ⟨2847050998687000991650801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 242948351887957417954201685 2847050998687000991650801)
                    ·
                      refine ⟨2135288249015250743738101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847050998687000991650801 2135288249015250743738101)
                      ·
                        rfl

theorem cell23_4158459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8, 2].length) (baseStart_4158459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158459 prefixEnd_4158459 := by exact prefixLift 4158459
  have htrace : WordTrace (prefixWord ++ tailWord_4158459) baseStart_4158459 baseEnd_4158459 := by
    simpa [prefixWord, tailWord_4158459, baseEnd_4158459] using wordTrace_append hprefix tailTrace_4158459
  have hstable : (prefixWord ++ tailWord_4158459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158459).length < 2 ^ (prefixWord ++ tailWord_4158459).sum := by decide
  have hdescent : baseEnd_4158459 < baseStart_4158459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158469 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_4158469 : Nat := 118140960795 + 4158469 * 2 ^ 59
def prefixEnd_4158469 : Nat := 4983230072969 + 3 ^ 40 * 4158469 * 2
def baseEnd_4158469 : Nat := 711764461273931901537685

theorem tailTrace_4158469 : CollatzResearch.WordTrace tailWord_4158469 prefixEnd_4158469 711764461273931901537685 := by
  unfold tailWord_4158469
  simp only [CollatzResearch.WordTrace]
  refine ⟨151671824771584497807606461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101114549847722998538404307 151671824771584497807606461)
  ·
    refine ⟨56876934289344186677852423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151671824771584497807606461 56876934289344186677852423)
    ·
      refine ⟨85315401434016280016778635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56876934289344186677852423 85315401434016280016778635)
      ·
        refine ⟨127973102151024420025167953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85315401434016280016778635 127973102151024420025167953)
        ·
          refine ⟨95979826613268315018875965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127973102151024420025167953 95979826613268315018875965)
          ·
            refine ⟨35992434979975618132078487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95979826613268315018875965 35992434979975618132078487)
            ·
              refine ⟨53988652469963427198117731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35992434979975618132078487 53988652469963427198117731)
              ·
                refine ⟨80982978704945140797176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53988652469963427198117731 80982978704945140797176597)
                ·
                  refine ⟨3796077126794303474867653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80982978704945140797176597 3796077126794303474867653)
                  ·
                    refine ⟨711764461273931901537685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796077126794303474867653 711764461273931901537685)
                    ·
                      rfl

theorem cell23_4158469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_4158469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158469 prefixEnd_4158469 := by exact prefixLift 4158469
  have htrace : WordTrace (prefixWord ++ tailWord_4158469) baseStart_4158469 baseEnd_4158469 := by
    simpa [prefixWord, tailWord_4158469, baseEnd_4158469] using wordTrace_append hprefix tailTrace_4158469
  have hstable : (prefixWord ++ tailWord_4158469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158469).length < 2 ^ (prefixWord ++ tailWord_4158469).sum := by decide
  have hdescent : baseEnd_4158469 < baseStart_4158469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158476 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4158476 : Nat := 118140960795 + 4158476 * 2 ^ 59
def prefixEnd_4158476 : Nat := 4983230072969 + 3 ^ 40 * 4158476 * 2
def baseEnd_4158476 : Nat := 2135296978186377177225523

theorem tailTrace_4158476 : CollatzResearch.WordTrace tailWord_4158476 prefixEnd_4158476 2135296978186377177225523 := by
  unfold tailWord_4158476
  simp only [CollatzResearch.WordTrace]
  refine ⟨75836040041279569001555641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101114720055039425335407521 75836040041279569001555641)
  ·
    refine ⟨56877030030959676751166731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75836040041279569001555641 56877030030959676751166731)
    ·
      refine ⟨85315545046439515126750097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56877030030959676751166731 85315545046439515126750097)
      ·
        refine ⟨63986658784829636345062573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85315545046439515126750097 63986658784829636345062573)
        ·
          refine ⟨23994997044311113629398465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63986658784829636345062573 23994997044311113629398465)
          ·
            refine ⟨17996247783233335222048849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23994997044311113629398465 17996247783233335222048849)
            ·
              refine ⟨13497185837425001416536637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17996247783233335222048849 13497185837425001416536637)
              ·
                refine ⟨5061444689034375531201239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13497185837425001416536637 5061444689034375531201239)
                ·
                  refine ⟨7592167033551563296801859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061444689034375531201239 7592167033551563296801859)
                  ·
                    refine ⟨11388250550327344945202789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7592167033551563296801859 11388250550327344945202789)
                    ·
                      refine ⟨2135296978186377177225523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11388250550327344945202789 2135296978186377177225523)
                      ·
                        rfl

theorem cell23_4158476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4158476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158476 prefixEnd_4158476 := by exact prefixLift 4158476
  have htrace : WordTrace (prefixWord ++ tailWord_4158476) baseStart_4158476 baseEnd_4158476 := by
    simpa [prefixWord, tailWord_4158476, baseEnd_4158476] using wordTrace_append hprefix tailTrace_4158476
  have hstable : (prefixWord ++ tailWord_4158476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158476).length < 2 ^ (prefixWord ++ tailWord_4158476).sum := by decide
  have hdescent : baseEnd_4158476 < baseStart_4158476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158487 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4158487 : Nat := 118140960795 + 4158487 * 2 ^ 59
def prefixEnd_4158487 : Nat := 4983230072969 + 3 ^ 40 * 4158487 * 2
def baseEnd_4158487 : Nat := 2135302626473576634187973

theorem tailTrace_4158487 : CollatzResearch.WordTrace tailWord_4158487 prefixEnd_4158487 2135302626473576634187973 := by
  unfold tailWord_4158487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151672481285519286881761715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101114987523679524587841143 151672481285519286881761715)
  ·
    refine ⟨227508721928278930322642573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151672481285519286881761715 227508721928278930322642573)
    ·
      refine ⟨85315770723104598870990965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227508721928278930322642573 85315770723104598870990965)
      ·
        refine ⟨7998353505291056144155403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85315770723104598870990965 7998353505291056144155403)
        ·
          refine ⟨11997530257936584216233105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998353505291056144155403 11997530257936584216233105)
          ·
            refine ⟨8998147693452438162174829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11997530257936584216233105 8998147693452438162174829)
            ·
              refine ⟨3374305385044664310815561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998147693452438162174829 3374305385044664310815561)
              ·
                refine ⟨2530729038783498233111671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374305385044664310815561 2530729038783498233111671)
                ·
                  refine ⟨3796093558175247349667507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530729038783498233111671 3796093558175247349667507)
                  ·
                    refine ⟨5694140337262871024501261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3796093558175247349667507 5694140337262871024501261)
                    ·
                      refine ⟨2135302626473576634187973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694140337262871024501261 2135302626473576634187973)
                      ·
                        rfl

theorem cell23_4158487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4158487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158487 prefixEnd_4158487 := by exact prefixLift 4158487
  have htrace : WordTrace (prefixWord ++ tailWord_4158487) baseStart_4158487 baseEnd_4158487 := by
    simpa [prefixWord, tailWord_4158487, baseEnd_4158487] using wordTrace_append hprefix tailTrace_4158487
  have hstable : (prefixWord ++ tailWord_4158487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158487).length < 2 ^ (prefixWord ++ tailWord_4158487).sum := by decide
  have hdescent : baseEnd_4158487 < baseStart_4158487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158499 : List Nat := [1, 1, 1, 4, 3, 3, 2, 8]
def baseStart_4158499 : Nat := 118140960795 + 4158499 * 2 ^ 59
def prefixEnd_4158499 : Nat := 4983230072969 + 3 ^ 40 * 4158499 * 2
def baseEnd_4158499 : Nat := 79085510675608540268071

theorem tailTrace_4158499 : CollatzResearch.WordTrace tailWord_4158499 prefixEnd_4158499 79085510675608540268071 := by
  unfold tailWord_4158499
  simp only [CollatzResearch.WordTrace]
  refine ⟨151672918961475812931198551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101115279307650541954132367 151672918961475812931198551)
  ·
    refine ⟨227509378442213719396797827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151672918961475812931198551 227509378442213719396797827)
    ·
      refine ⟨341264067663320579095196741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227509378442213719396797827 341264067663320579095196741)
      ·
        refine ⟨63987012686872608580349389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341264067663320579095196741 63987012686872608580349389)
        ·
          refine ⟨23995129757577228217631021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63987012686872608580349389 23995129757577228217631021)
          ·
            refine ⟨8998173659091460581611633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23995129757577228217631021 8998173659091460581611633)
            ·
              refine ⟨6748630244318595436208725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8998173659091460581611633 6748630244318595436208725)
              ·
                refine ⟨79085510675608540268071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6748630244318595436208725 79085510675608540268071)
                ·
                  rfl

theorem cell23_4158499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 8].length) (baseStart_4158499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158499 prefixEnd_4158499 := by exact prefixLift 4158499
  have htrace : WordTrace (prefixWord ++ tailWord_4158499) baseStart_4158499 baseEnd_4158499 := by
    simpa [prefixWord, tailWord_4158499, baseEnd_4158499] using wordTrace_append hprefix tailTrace_4158499
  have hstable : (prefixWord ++ tailWord_4158499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158499).length < 2 ^ (prefixWord ++ tailWord_4158499).sum := by decide
  have hdescent : baseEnd_4158499 < baseStart_4158499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158516 : List Nat := [2, 5, 1, 2, 1, 1, 2, 9]
def baseStart_4158516 : Nat := 118140960795 + 4158516 * 2 ^ 59
def prefixEnd_4158516 : Nat := 4983230072969 + 3 ^ 40 * 4158516 * 2
def baseEnd_4158516 : Nat := 79085833978242852619457

theorem tailTrace_4158516 : CollatzResearch.WordTrace tailWord_4158516 prefixEnd_4158516 79085833978242852619457 := by
  unfold tailWord_4158516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75836769501207112417283701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101115692668276149889711601 75836769501207112417283701)
  ·
    refine ⟨7109697140738166789120347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75836769501207112417283701 7109697140738166789120347)
    ·
      refine ⟨10664545711107250183680521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7109697140738166789120347 10664545711107250183680521)
      ·
        refine ⟨7998409283330437637760391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10664545711107250183680521 7998409283330437637760391)
        ·
          refine ⟨11997613924995656456640587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998409283330437637760391 11997613924995656456640587)
          ·
            refine ⟨17996420887493484684960881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997613924995656456640587 17996420887493484684960881)
            ·
              refine ⟨13497315665620113513720661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17996420887493484684960881 13497315665620113513720661)
              ·
                refine ⟨79085833978242852619457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13497315665620113513720661 79085833978242852619457)
                ·
                  rfl

theorem cell23_4158516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 9].length) (baseStart_4158516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158516 prefixEnd_4158516 := by exact prefixLift 4158516
  have htrace : WordTrace (prefixWord ++ tailWord_4158516) baseStart_4158516 baseEnd_4158516 := by
    simpa [prefixWord, tailWord_4158516, baseEnd_4158516] using wordTrace_append hprefix tailTrace_4158516
  have hstable : (prefixWord ++ tailWord_4158516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158516).length < 2 ^ (prefixWord ++ tailWord_4158516).sum := by decide
  have hdescent : baseEnd_4158516 < baseStart_4158516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158549 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4158549 : Nat := 118140960795 + 4158549 * 2 ^ 59
def prefixEnd_4158549 : Nat := 4983230072969 + 3 ^ 40 * 4158549 * 2
def baseEnd_4158549 : Nat := 2135334462274155391612687

theorem tailTrace_4158549 : CollatzResearch.WordTrace tailWord_4158549 prefixEnd_4158549 2135334462274155391612687 := by
  unfold tailWord_4158549
  simp only [CollatzResearch.WordTrace]
  refine ⟨151674742611294671470518701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101116495074196447647012467 151674742611294671470518701)
  ·
    refine ⟨56878028479235501801444513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151674742611294671470518701 56878028479235501801444513)
    ·
      refine ⟨42658521359426626351083385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56878028479235501801444513 42658521359426626351083385)
      ·
        refine ⟨31993891019569969763312539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42658521359426626351083385 31993891019569969763312539)
        ·
          refine ⟨47990836529354954644968809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31993891019569969763312539 47990836529354954644968809)
          ·
            refine ⟨35993127397016215983726607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47990836529354954644968809 35993127397016215983726607)
            ·
              refine ⟨53989691095524323975589911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35993127397016215983726607 53989691095524323975589911)
              ·
                refine ⟨80984536643286485963384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53989691095524323975589911 80984536643286485963384867)
                ·
                  refine ⟨121476804964929728945077301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80984536643286485963384867 121476804964929728945077301)
                  ·
                    refine ⟨11388450465462162088600997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121476804964929728945077301 11388450465462162088600997)
                    ·
                      refine ⟨2135334462274155391612687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11388450465462162088600997 2135334462274155391612687)
                      ·
                        rfl

theorem cell23_4158549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4158549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158549 prefixEnd_4158549 := by exact prefixLift 4158549
  have htrace : WordTrace (prefixWord ++ tailWord_4158549) baseStart_4158549 baseEnd_4158549 := by
    simpa [prefixWord, tailWord_4158549, baseEnd_4158549] using wordTrace_append hprefix tailTrace_4158549
  have hstable : (prefixWord ++ tailWord_4158549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158549).length < 2 ^ (prefixWord ++ tailWord_4158549).sum := by decide
  have hdescent : baseEnd_4158549 < baseStart_4158549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158550 : List Nat := [5, 2, 2, 1, 2, 2, 1, 8]
def baseStart_4158550 : Nat := 118140960795 + 4158550 * 2 ^ 59
def prefixEnd_4158550 : Nat := 4983230072969 + 3 ^ 40 * 4158550 * 2
def baseEnd_4158550 : Nat := 79086480583511477322229

theorem tailTrace_4158550 : CollatzResearch.WordTrace tailWord_4158550 prefixEnd_4158550 79086480583511477322229 := by
  unfold tailWord_4158550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479673692768190540081569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101116519389527365760870069 9479673692768190540081569)
  ·
    refine ⟨7109755269576142905061177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9479673692768190540081569 7109755269576142905061177)
    ·
      refine ⟨5332316452182107178795883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109755269576142905061177 5332316452182107178795883)
      ·
        refine ⟨7998474678273160768193825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332316452182107178795883 7998474678273160768193825)
        ·
          refine ⟨5998856008704870576145369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7998474678273160768193825 5998856008704870576145369)
          ·
            refine ⟨4499142006528652932109027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5998856008704870576145369 4499142006528652932109027)
            ·
              refine ⟨6748713009792979398163541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4499142006528652932109027 6748713009792979398163541)
              ·
                refine ⟨79086480583511477322229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6748713009792979398163541 79086480583511477322229)
                ·
                  rfl

theorem cell23_4158550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_4158550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158550 prefixEnd_4158550 := by exact prefixLift 4158550
  have htrace : WordTrace (prefixWord ++ tailWord_4158550) baseStart_4158550 baseEnd_4158550 := by
    simpa [prefixWord, tailWord_4158550, baseEnd_4158550] using wordTrace_append hprefix tailTrace_4158550
  have hstable : (prefixWord ++ tailWord_4158550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158550).length < 2 ^ (prefixWord ++ tailWord_4158550).sum := by decide
  have hdescent : baseEnd_4158550 < baseStart_4158550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158559 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 6]
def baseStart_4158559 : Nat := 118140960795 + 4158559 * 2 ^ 59
def prefixEnd_4158559 : Nat := 4983230072969 + 3 ^ 40 * 4158559 * 2
def baseEnd_4158559 : Nat := 711779865693566784162547

theorem tailTrace_4158559 : CollatzResearch.WordTrace tailWord_4158559 prefixEnd_4158559 711779865693566784162547 := by
  unfold tailWord_4158559
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675107341258443178382731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101116738227505628785588487 151675107341258443178382731)
  ·
    refine ⟨227512661011887664767574097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151675107341258443178382731 227512661011887664767574097)
    ·
      refine ⟨170634495758915748575680573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227512661011887664767574097 170634495758915748575680573)
      ·
        refine ⟨63987935909593405715880215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170634495758915748575680573 63987935909593405715880215)
        ·
          refine ⟨95981903864390108573820323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63987935909593405715880215 95981903864390108573820323)
          ·
            refine ⟨143972855796585162860730485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95981903864390108573820323 143972855796585162860730485)
            ·
              refine ⟨13497455230929859018193483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143972855796585162860730485 13497455230929859018193483)
              ·
                refine ⟨20246182846394788527290225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13497455230929859018193483 20246182846394788527290225)
                ·
                  refine ⟨15184637134796091395467669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20246182846394788527290225 15184637134796091395467669)
                  ·
                    refine ⟨711779865693566784162547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15184637134796091395467669 711779865693566784162547)
                    ·
                      rfl

theorem cell23_4158559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_4158559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158559 prefixEnd_4158559 := by exact prefixLift 4158559
  have htrace : WordTrace (prefixWord ++ tailWord_4158559) baseStart_4158559 baseEnd_4158559 := by
    simpa [prefixWord, tailWord_4158559, baseEnd_4158559] using wordTrace_append hprefix tailTrace_4158559
  have hstable : (prefixWord ++ tailWord_4158559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158559).length < 2 ^ (prefixWord ++ tailWord_4158559).sum := by decide
  have hdescent : baseEnd_4158559 < baseStart_4158559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158583 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_4158583 : Nat := 118140960795 + 4158583 * 2 ^ 59
def prefixEnd_4158583 : Nat := 4983230072969 + 3 ^ 40 * 4158583 * 2
def baseEnd_4158583 : Nat := 2135351920616408258587531

theorem tailTrace_4158583 : CollatzResearch.WordTrace tailWord_4158583 prefixEnd_4158583 2135351920616408258587531 := by
  unfold tailWord_4158583
  simp only [CollatzResearch.WordTrace]
  refine ⟨151675982693171495277256403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101117321795447663518170935 151675982693171495277256403)
  ·
    refine ⟨227513974039757242915884605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151675982693171495277256403 227513974039757242915884605)
    ·
      refine ⟨85317740264908966093456727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227513974039757242915884605 85317740264908966093456727)
      ·
        refine ⟨127976610397363449140185091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85317740264908966093456727 127976610397363449140185091)
        ·
          refine ⟨191964915596045173710277637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127976610397363449140185091 191964915596045173710277637)
          ·
            refine ⟨35993421674258470070677057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191964915596045173710277637 35993421674258470070677057)
            ·
              refine ⟨26995066255693852553007793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35993421674258470070677057 26995066255693852553007793)
              ·
                refine ⟨20246299691770389414755845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26995066255693852553007793 20246299691770389414755845)
                ·
                  refine ⟨3796181192206948015266721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20246299691770389414755845 3796181192206948015266721)
                  ·
                    refine ⟨2847135894155211011450041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796181192206948015266721 2847135894155211011450041)
                    ·
                      refine ⟨2135351920616408258587531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847135894155211011450041 2135351920616408258587531)
                      ·
                        rfl

theorem cell23_4158583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_4158583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158583 prefixEnd_4158583 := by exact prefixLift 4158583
  have htrace : WordTrace (prefixWord ++ tailWord_4158583) baseStart_4158583 baseEnd_4158583 := by
    simpa [prefixWord, tailWord_4158583, baseEnd_4158583] using wordTrace_append hprefix tailTrace_4158583
  have hstable : (prefixWord ++ tailWord_4158583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158583).length < 2 ^ (prefixWord ++ tailWord_4158583).sum := by decide
  have hdescent : baseEnd_4158583 < baseStart_4158583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158589 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 9]
def baseStart_4158589 : Nat := 118140960795 + 4158589 * 2 ^ 59
def prefixEnd_4158589 : Nat := 4983230072969 + 3 ^ 40 * 4158589 * 2
def baseEnd_4158589 : Nat := 237261666833370581679167

theorem tailTrace_4158589 : CollatzResearch.WordTrace tailWord_4158589 prefixEnd_4158589 237261666833370581679167 := by
  unfold tailWord_4158589
  simp only [CollatzResearch.WordTrace]
  refine ⟨151676201531149758301974821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101117467687433172201316547 151676201531149758301974821)
  ·
    refine ⟨28439287787090579681620279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151676201531149758301974821 28439287787090579681620279)
    ·
      refine ⟨42658931680635869522430419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28439287787090579681620279 42658931680635869522430419)
      ·
        refine ⟨63988397520953804283645629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42658931680635869522430419 63988397520953804283645629)
        ·
          refine ⟨23995649070357676606367111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63988397520953804283645629 23995649070357676606367111)
          ·
            refine ⟨35993473605536514909550667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23995649070357676606367111 35993473605536514909550667)
            ·
              refine ⟨53990210408304772364326001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35993473605536514909550667 53990210408304772364326001)
              ·
                refine ⟨40492657806228579273244501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53990210408304772364326001 40492657806228579273244501)
                ·
                  refine ⟨237261666833370581679167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40492657806228579273244501 237261666833370581679167)
                  ·
                    rfl

theorem cell23_4158589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_4158589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158589 prefixEnd_4158589 := by exact prefixLift 4158589
  have htrace : WordTrace (prefixWord ++ tailWord_4158589) baseStart_4158589 baseEnd_4158589 := by
    simpa [prefixWord, tailWord_4158589, baseEnd_4158589] using wordTrace_append hprefix tailTrace_4158589
  have hstable : (prefixWord ++ tailWord_4158589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158589).length < 2 ^ (prefixWord ++ tailWord_4158589).sum := by decide
  have hdescent : baseEnd_4158589 < baseStart_4158589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158596 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4158596 : Nat := 118140960795 + 4158596 * 2 ^ 59
def prefixEnd_4158596 : Nat := 4983230072969 + 3 ^ 40 * 4158596 * 2
def baseEnd_4158596 : Nat := 2135358595864916707724971

theorem tailTrace_4158596 : CollatzResearch.WordTrace tailWord_4158596 prefixEnd_4158596 2135358595864916707724971 := by
  unfold tailWord_4158596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75838228421062199248739821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101117637894749598998319761 75838228421062199248739821)
  ·
    refine ⟨28439335657898324718277433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75838228421062199248739821 28439335657898324718277433)
    ·
      refine ⟨21329501743423743538708075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28439335657898324718277433 21329501743423743538708075)
      ·
        refine ⟨31994252615135615308062113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21329501743423743538708075 31994252615135615308062113)
        ·
          refine ⟨23995689461351711481046585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31994252615135615308062113 23995689461351711481046585)
          ·
            refine ⟨17996767096013783610784939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23995689461351711481046585 17996767096013783610784939)
            ·
              refine ⟨26995150644020675416177409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996767096013783610784939 26995150644020675416177409)
              ·
                refine ⟨20246362983015506562133057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26995150644020675416177409 20246362983015506562133057)
                ·
                  refine ⟨15184772237261629921599793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20246362983015506562133057 15184772237261629921599793)
                  ·
                    refine ⟨11388579177946222441199845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15184772237261629921599793 11388579177946222441199845)
                    ·
                      refine ⟨2135358595864916707724971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11388579177946222441199845 2135358595864916707724971)
                      ·
                        rfl

theorem cell23_4158596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4158596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158596 prefixEnd_4158596 := by exact prefixLift 4158596
  have htrace : WordTrace (prefixWord ++ tailWord_4158596) baseStart_4158596 baseEnd_4158596 := by
    simpa [prefixWord, tailWord_4158596, baseEnd_4158596] using wordTrace_append hprefix tailTrace_4158596
  have hstable : (prefixWord ++ tailWord_4158596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158596).length < 2 ^ (prefixWord ++ tailWord_4158596).sum := by decide
  have hdescent : baseEnd_4158596 < baseStart_4158596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158606 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_4158606 : Nat := 118140960795 + 4158606 * 2 ^ 59
def prefixEnd_4158606 : Nat := 4983230072969 + 3 ^ 40 * 4158606 * 2
def baseEnd_4158606 : Nat := 237262636741273518733325

theorem tailTrace_4158606 : CollatzResearch.WordTrace tailWord_4158606 prefixEnd_4158606 237262636741273518733325 := by
  unfold tailWord_4158606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18959602696511021275667959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101117881048058780136895781 18959602696511021275667959)
  ·
    refine ⟨28439404044766531913501939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18959602696511021275667959 28439404044766531913501939)
    ·
      refine ⟨42659106067149797870252909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28439404044766531913501939 42659106067149797870252909)
      ·
        refine ⟨15997164775181174201344841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42659106067149797870252909 15997164775181174201344841)
        ·
          refine ⟨11997873581385880651008631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15997164775181174201344841 11997873581385880651008631)
          ·
            refine ⟨17996810372078820976512947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11997873581385880651008631 17996810372078820976512947)
            ·
              refine ⟨26995215558118231464769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17996810372078820976512947 26995215558118231464769421)
              ·
                refine ⟨10123205834294336799288533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26995215558118231464769421 10123205834294336799288533)
                ·
                  refine ⟨237262636741273518733325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10123205834294336799288533 237262636741273518733325)
                  ·
                    rfl

theorem cell23_4158606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_4158606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158606 prefixEnd_4158606 := by exact prefixLift 4158606
  have htrace : WordTrace (prefixWord ++ tailWord_4158606) baseStart_4158606 baseEnd_4158606 := by
    simpa [prefixWord, tailWord_4158606, baseEnd_4158606] using wordTrace_append hprefix tailTrace_4158606
  have hstable : (prefixWord ++ tailWord_4158606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158606).length < 2 ^ (prefixWord ++ tailWord_4158606).sum := by decide
  have hdescent : baseEnd_4158606 < baseStart_4158606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158657 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 5]
def baseStart_4158657 : Nat := 118140960795 + 4158657 * 2 ^ 59
def prefixEnd_4158657 : Nat := 4983230072969 + 3 ^ 40 * 4158657 * 2
def baseEnd_4158657 : Nat := 237265546464982329895799

theorem tailTrace_4158657 : CollatzResearch.WordTrace tailWord_4158657 prefixEnd_4158657 237265546464982329895799 := by
  unfold tailWord_4158657
  simp only [CollatzResearch.WordTrace]
  refine ⟨151678681694903405915450225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101119121129935603943633483 151678681694903405915450225)
  ·
    refine ⟨113759011271177554436587669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151678681694903405915450225 113759011271177554436587669)
    ·
      refine ⟨5332453653336447864215047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113759011271177554436587669 5332453653336447864215047)
      ·
        refine ⟨7998680480004671796322571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332453653336447864215047 7998680480004671796322571)
        ·
          refine ⟨11998020720007007694483857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998680480004671796322571 11998020720007007694483857)
          ·
            refine ⟨8998515540005255770862893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998020720007007694483857 8998515540005255770862893)
            ·
              refine ⟨3374443327501970914073585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8998515540005255770862893 3374443327501970914073585)
              ·
                refine ⟨2530832495626478185555189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374443327501970914073585 2530832495626478185555189)
                ·
                  refine ⟨237265546464982329895799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530832495626478185555189 237265546464982329895799)
                  ·
                    rfl

theorem cell23_4158657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 5].length) (baseStart_4158657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158657 prefixEnd_4158657 := by exact prefixLift 4158657
  have htrace : WordTrace (prefixWord ++ tailWord_4158657) baseStart_4158657 baseEnd_4158657 := by
    simpa [prefixWord, tailWord_4158657, baseEnd_4158657] using wordTrace_append hprefix tailTrace_4158657
  have hstable : (prefixWord ++ tailWord_4158657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158657).length < 2 ^ (prefixWord ++ tailWord_4158657).sum := by decide
  have hdescent : baseEnd_4158657 < baseStart_4158657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158659 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_4158659 : Nat := 118140960795 + 4158659 * 2 ^ 59
def prefixEnd_4158659 : Nat := 4983230072969 + 3 ^ 40 * 4158659 * 2
def baseEnd_4158659 : Nat := 2135390945146149961237181

theorem tailTrace_4158659 : CollatzResearch.WordTrace tailWord_4158659 prefixEnd_4158659 2135390945146149961237181 := by
  unfold tailWord_4158659
  simp only [CollatzResearch.WordTrace]
  refine ⟨151678754640896160257023031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101119169760597440171348687 151678754640896160257023031)
  ·
    refine ⟨227518131961344240385534547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151678754640896160257023031 227518131961344240385534547)
    ·
      refine ⟨341277197942016360578301821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227518131961344240385534547 341277197942016360578301821)
      ·
        refine ⟨127978949228256135216863183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341277197942016360578301821 127978949228256135216863183)
        ·
          refine ⟨191968423842384202825294775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127978949228256135216863183 191968423842384202825294775)
          ·
            refine ⟨287952635763576304237942163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191968423842384202825294775 287952635763576304237942163)
            ·
              refine ⟨431928953645364456356913245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287952635763576304237942163 431928953645364456356913245)
              ·
                refine ⟨161973357617011671133842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431928953645364456356913245 161973357617011671133842467)
                ·
                  refine ⟨242960036425517506700763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161973357617011671133842467 242960036425517506700763701)
                  ·
                    refine ⟨22777503414892266253196597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242960036425517506700763701 22777503414892266253196597)
                    ·
                      refine ⟨2135390945146149961237181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22777503414892266253196597 2135390945146149961237181)
                      ·
                        rfl

theorem cell23_4158659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_4158659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158659 prefixEnd_4158659 := by exact prefixLift 4158659
  have htrace : WordTrace (prefixWord ++ tailWord_4158659) baseStart_4158659 baseEnd_4158659 := by
    simpa [prefixWord, tailWord_4158659, baseEnd_4158659] using wordTrace_append hprefix tailTrace_4158659
  have hstable : (prefixWord ++ tailWord_4158659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158659).length < 2 ^ (prefixWord ++ tailWord_4158659).sum := by decide
  have hdescent : baseEnd_4158659 < baseStart_4158659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158708 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4158708 : Nat := 118140960795 + 4158708 * 2 ^ 59
def prefixEnd_4158708 : Nat := 4983230072969 + 3 ^ 40 * 4158708 * 2
def baseEnd_4158708 : Nat := 237268456188691141058273

theorem tailTrace_4158708 : CollatzResearch.WordTrace tailWord_4158708 prefixEnd_4158708 237268456188691141058273 := by
  unfold tailWord_4158708
  simp only [CollatzResearch.WordTrace]
  refine ⟨75840270908859320812778389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101120361211812427750371185 75840270908859320812778389)
  ·
    refine ⟨3555012698852780663098987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75840270908859320812778389 3555012698852780663098987)
    ·
      refine ⟨5332519048279170994648481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555012698852780663098987 5332519048279170994648481)
      ·
        refine ⟨3999389286209378245986361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5332519048279170994648481 3999389286209378245986361)
        ·
          refine ⟨2999541964657033684489771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999389286209378245986361 2999541964657033684489771)
          ·
            refine ⟨4499312946985550526734657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999541964657033684489771 4499312946985550526734657)
            ·
              refine ⟨3374484710239162895050993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499312946985550526734657 3374484710239162895050993)
              ·
                refine ⟨2530863532679372171288245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3374484710239162895050993 2530863532679372171288245)
                ·
                  refine ⟨237268456188691141058273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2530863532679372171288245 237268456188691141058273)
                  ·
                    rfl

theorem cell23_4158708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4158708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158708 prefixEnd_4158708 := by exact prefixLift 4158708
  have htrace : WordTrace (prefixWord ++ tailWord_4158708) baseStart_4158708 baseEnd_4158708 := by
    simpa [prefixWord, tailWord_4158708, baseEnd_4158708] using wordTrace_append hprefix tailTrace_4158708
  have hstable : (prefixWord ++ tailWord_4158708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158708).length < 2 ^ (prefixWord ++ tailWord_4158708).sum := by decide
  have hdescent : baseEnd_4158708 < baseStart_4158708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158743 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 1, 5]
def baseStart_4158743 : Nat := 118140960795 + 4158743 * 2 ^ 59
def prefixEnd_4158743 : Nat := 4983230072969 + 3 ^ 40 * 4158743 * 2
def baseEnd_4158743 : Nat := 711811359173709210862265

theorem tailTrace_4158743 : CollatzResearch.WordTrace tailWord_4158743 prefixEnd_4158743 711811359173709210862265 := by
  unfold tailWord_4158743
  simp only [CollatzResearch.WordTrace]
  refine ⟨151681818372591842603080883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101121212248394561735387255 151681818372591842603080883)
  ·
    refine ⟨227522727558887763904621325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151681818372591842603080883 227522727558887763904621325)
    ·
      refine ⟨85321022834582911464232997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227522727558887763904621325 85321022834582911464232997)
      ·
        refine ⟨15997691781484295899543687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85321022834582911464232997 15997691781484295899543687)
        ·
          refine ⟨23996537672226443849315531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15997691781484295899543687 23996537672226443849315531)
          ·
            refine ⟨35994806508339665773973297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23996537672226443849315531 35994806508339665773973297)
            ·
              refine ⟨26996104881254749330479973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35994806508339665773973297 26996104881254749330479973)
              ·
                refine ⟨5061769665235265499464995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26996104881254749330479973 5061769665235265499464995)
                ·
                  refine ⟨7592654497852898249197493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061769665235265499464995 7592654497852898249197493)
                  ·
                    refine ⟨711811359173709210862265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7592654497852898249197493 711811359173709210862265)
                    ·
                      rfl

theorem cell23_4158743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_4158743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158743 prefixEnd_4158743 := by exact prefixLift 4158743
  have htrace : WordTrace (prefixWord ++ tailWord_4158743) baseStart_4158743 baseEnd_4158743 := by
    simpa [prefixWord, tailWord_4158743, baseEnd_4158743] using wordTrace_append hprefix tailTrace_4158743
  have hstable : (prefixWord ++ tailWord_4158743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158743).length < 2 ^ (prefixWord ++ tailWord_4158743).sum := by decide
  have hdescent : baseEnd_4158743 < baseStart_4158743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158757 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_4158757 : Nat := 118140960795 + 4158757 * 2 ^ 59
def prefixEnd_4158757 : Nat := 4983230072969 + 3 ^ 40 * 4158757 * 2
def baseEnd_4158757 : Nat := 2135441266250290577811731

theorem tailTrace_4158757 : CollatzResearch.WordTrace tailWord_4158757 prefixEnd_4158757 2135441266250290577811731 := by
  unfold tailWord_4158757
  simp only [CollatzResearch.WordTrace]
  refine ⟨151682328994541122994090525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101121552663027415329393683 151682328994541122994090525)
  ·
    refine ⟨56880873372952921122783947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151682328994541122994090525 56880873372952921122783947)
    ·
      refine ⟨85321310059429381684175921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56880873372952921122783947 85321310059429381684175921)
      ·
        refine ⟨63990982544572036263131941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85321310059429381684175921 63990982544572036263131941)
        ·
          refine ⟨11998309227107256799337239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63990982544572036263131941 11998309227107256799337239)
          ·
            refine ⟨17997463840660885199005859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11998309227107256799337239 17997463840660885199005859)
            ·
              refine ⟨26996195760991327798508789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17997463840660885199005859 26996195760991327798508789)
              ·
                refine ⟨2530893352592936981110199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26996195760991327798508789 2530893352592936981110199)
                ·
                  refine ⟨3796340028889405471665299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2530893352592936981110199 3796340028889405471665299)
                  ·
                    refine ⟨5694510043334108207497949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3796340028889405471665299 5694510043334108207497949)
                    ·
                      refine ⟨2135441266250290577811731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694510043334108207497949 2135441266250290577811731)
                      ·
                        rfl

theorem cell23_4158757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_4158757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158757 prefixEnd_4158757 := by exact prefixLift 4158757
  have htrace : WordTrace (prefixWord ++ tailWord_4158757) baseStart_4158757 baseEnd_4158757 := by
    simpa [prefixWord, tailWord_4158757, baseEnd_4158757] using wordTrace_append hprefix tailTrace_4158757
  have hstable : (prefixWord ++ tailWord_4158757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158757).length < 2 ^ (prefixWord ++ tailWord_4158757).sum := by decide
  have hdescent : baseEnd_4158757 < baseStart_4158757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158760 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4158760 : Nat := 118140960795 + 4158760 * 2 ^ 59
def prefixEnd_4158760 : Nat := 4983230072969 + 3 ^ 40 * 4158760 * 2
def baseEnd_4158760 : Nat := 711814268897418022024739

theorem tailTrace_4158760 : CollatzResearch.WordTrace tailWord_4158760 prefixEnd_4158760 711814268897418022024739 := by
  unfold tailWord_4158760
  simp only [CollatzResearch.WordTrace]
  refine ⟨75841219206765127253224867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101121625609020169670966489 75841219206765127253224867)
  ·
    refine ⟨113761828810147690879837301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75841219206765127253224867 113761828810147690879837301)
    ·
      refine ⟨10665171450951346019984747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113761828810147690879837301 10665171450951346019984747)
      ·
        refine ⟨15997757176427019029977121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10665171450951346019984747 15997757176427019029977121)
        ·
          refine ⟨11998317882320264272482841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15997757176427019029977121 11998317882320264272482841)
          ·
            refine ⟨8998738411740198204362131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11998317882320264272482841 8998738411740198204362131)
            ·
              refine ⟨13498107617610297306543197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998738411740198204362131 13498107617610297306543197)
              ·
                refine ⟨5061790356603861489953699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13498107617610297306543197 5061790356603861489953699)
                ·
                  refine ⟨7592685534905792234930549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061790356603861489953699 7592685534905792234930549)
                  ·
                    refine ⟨711814268897418022024739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7592685534905792234930549 711814268897418022024739)
                    ·
                      rfl

theorem cell23_4158760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4158760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158760 prefixEnd_4158760 := by exact prefixLift 4158760
  have htrace : WordTrace (prefixWord ++ tailWord_4158760) baseStart_4158760 baseEnd_4158760 := by
    simpa [prefixWord, tailWord_4158760, baseEnd_4158760] using wordTrace_append hprefix tailTrace_4158760
  have hstable : (prefixWord ++ tailWord_4158760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158760).length < 2 ^ (prefixWord ++ tailWord_4158760).sum := by decide
  have hdescent : baseEnd_4158760 < baseStart_4158760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158776 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_4158776 : Nat := 118140960795 + 4158776 * 2 ^ 59
def prefixEnd_4158776 : Nat := 4983230072969 + 3 ^ 40 * 4158776 * 2
def baseEnd_4158776 : Nat := 2135451022382726003474143

theorem tailTrace_4158776 : CollatzResearch.WordTrace tailWord_4158776 prefixEnd_4158776 2135451022382726003474143 := by
  unfold tailWord_4158776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75841510990736144619516091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101122014654314859492688121 75841510990736144619516091)
  ·
    refine ⟨113762266486104216929274137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75841510990736144619516091 113762266486104216929274137)
    ·
      refine ⟨85321699864578162696955603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113762266486104216929274137 85321699864578162696955603)
      ·
        refine ⟨127982549796867244045433405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85321699864578162696955603 127982549796867244045433405)
        ·
          refine ⟨47993456173825216517037527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127982549796867244045433405 47993456173825216517037527)
          ·
            refine ⟨71990184260737824775556291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47993456173825216517037527 71990184260737824775556291)
            ·
              refine ⟨107985276391106737163334437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71990184260737824775556291 107985276391106737163334437)
              ·
                refine ⟨20247239323332513218125207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107985276391106737163334437 20247239323332513218125207)
                ·
                  refine ⟨30370858984998769827187811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20247239323332513218125207 30370858984998769827187811)
                  ·
                    refine ⟨45556288477498154740781717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30370858984998769827187811 45556288477498154740781717)
                    ·
                      refine ⟨2135451022382726003474143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45556288477498154740781717 2135451022382726003474143)
                      ·
                        rfl

theorem cell23_4158776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_4158776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158776 prefixEnd_4158776 := by exact prefixLift 4158776
  have htrace : WordTrace (prefixWord ++ tailWord_4158776) baseStart_4158776 baseEnd_4158776 := by
    simpa [prefixWord, tailWord_4158776, baseEnd_4158776] using wordTrace_append hprefix tailTrace_4158776
  have hstable : (prefixWord ++ tailWord_4158776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158776).length < 2 ^ (prefixWord ++ tailWord_4158776).sum := by decide
  have hdescent : baseEnd_4158776 < baseStart_4158776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158783 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_4158783 : Nat := 118140960795 + 4158783 * 2 ^ 59
def prefixEnd_4158783 : Nat := 4983230072969 + 3 ^ 40 * 4158783 * 2
def baseEnd_4158783 : Nat := 2135454616747307476086611

theorem tailTrace_4158783 : CollatzResearch.WordTrace tailWord_4158783 prefixEnd_4158783 2135454616747307476086611 := by
  unfold tailWord_4158783
  simp only [CollatzResearch.WordTrace]
  refine ⟨151683277292446929434537003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101122184861631286289691335 151683277292446929434537003)
  ·
    refine ⟨227524915938670394151805505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151683277292446929434537003 227524915938670394151805505)
    ·
      refine ⟨170643686954002795613854129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227524915938670394151805505 170643686954002795613854129)
      ·
        refine ⟨127982765215502096710390597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170643686954002795613854129 127982765215502096710390597)
        ·
          refine ⟨23996768477906643133198237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127982765215502096710390597 23996768477906643133198237)
          ·
            refine ⟨8998788179214991174949339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23996768477906643133198237 8998788179214991174949339)
            ·
              refine ⟨13498182268822486762424009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998788179214991174949339 13498182268822486762424009)
              ·
                refine ⟨10123636701616865071818007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13498182268822486762424009 10123636701616865071818007)
                ·
                  refine ⟨15185455052425297607727011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123636701616865071818007 15185455052425297607727011)
                  ·
                    refine ⟨22778182578637946411590517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15185455052425297607727011 22778182578637946411590517)
                    ·
                      refine ⟨2135454616747307476086611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22778182578637946411590517 2135454616747307476086611)
                      ·
                        rfl

theorem cell23_4158783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_4158783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158783 prefixEnd_4158783 := by exact prefixLift 4158783
  have htrace : WordTrace (prefixWord ++ tailWord_4158783) baseStart_4158783 baseEnd_4158783 := by
    simpa [prefixWord, tailWord_4158783, baseEnd_4158783] using wordTrace_append hprefix tailTrace_4158783
  have hstable : (prefixWord ++ tailWord_4158783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158783).length < 2 ^ (prefixWord ++ tailWord_4158783).sum := by decide
  have hdescent : baseEnd_4158783 < baseStart_4158783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158793 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_4158793 : Nat := 118140960795 + 4158793 * 2 ^ 59
def prefixEnd_4158793 : Nat := 4983230072969 + 3 ^ 40 * 4158793 * 2
def baseEnd_4158793 : Nat := 2135459751553852436961565

theorem tailTrace_4158793 : CollatzResearch.WordTrace tailWord_4158793 prefixEnd_4158793 2135459751553852436961565 := by
  unfold tailWord_4158793
  simp only [CollatzResearch.WordTrace]
  refine ⟨151683642022410701142401033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101122428014940467428267355 151683642022410701142401033)
  ·
    refine ⟨113762731516808025856800775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151683642022410701142401033 113762731516808025856800775)
    ·
      refine ⟨170644097275212038785201163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113762731516808025856800775 170644097275212038785201163)
      ·
        refine ⟨255966145912818058177801745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170644097275212038785201163 255966145912818058177801745)
        ·
          refine ⟨191974609434613543633351309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255966145912818058177801745 191974609434613543633351309)
          ·
            refine ⟨71990478537980078862506741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191974609434613543633351309 71990478537980078862506741)
            ·
              refine ⟨6749107362935632393360007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71990478537980078862506741 6749107362935632393360007)
              ·
                refine ⟨10123661044403448590040011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749107362935632393360007 10123661044403448590040011)
                ·
                  refine ⟨15185491566605172885060017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10123661044403448590040011 15185491566605172885060017)
                  ·
                    refine ⟨11389118674953879663795013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15185491566605172885060017 11389118674953879663795013)
                    ·
                      refine ⟨2135459751553852436961565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11389118674953879663795013 2135459751553852436961565)
                      ·
                        rfl

theorem cell23_4158793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_4158793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158793 prefixEnd_4158793 := by exact prefixLift 4158793
  have htrace : WordTrace (prefixWord ++ tailWord_4158793) baseStart_4158793 baseEnd_4158793 := by
    simpa [prefixWord, tailWord_4158793, baseEnd_4158793] using wordTrace_append hprefix tailTrace_4158793
  have hstable : (prefixWord ++ tailWord_4158793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158793).length < 2 ^ (prefixWord ++ tailWord_4158793).sum := by decide
  have hdescent : baseEnd_4158793 < baseStart_4158793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158800 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_4158800 : Nat := 118140960795 + 4158800 * 2 ^ 59
def prefixEnd_4158800 : Nat := 4983230072969 + 3 ^ 40 * 4158800 * 2
def baseEnd_4158800 : Nat := 2135463345918433909574033

theorem tailTrace_4158800 : CollatzResearch.WordTrace tailWord_4158800 prefixEnd_4158800 2135463345918433909574033 := by
  unfold tailWord_4158800
  simp only [CollatzResearch.WordTrace]
  refine ⟨75841948666692670668952927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101122598222256894225270569 75841948666692670668952927)
  ·
    refine ⟨113762923000039006003429391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75841948666692670668952927 113762923000039006003429391)
    ·
      refine ⟨170644384500058509005144087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113762923000039006003429391 170644384500058509005144087)
      ·
        refine ⟨255966576750087763507716131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170644384500058509005144087 255966576750087763507716131)
        ·
          refine ⟨383949865125131645261574197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255966576750087763507716131 383949865125131645261574197)
          ·
            refine ⟨35995299855481091743272581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383949865125131645261574197 35995299855481091743272581)
            ·
              refine ⟨6749118722902704701863609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35995299855481091743272581 6749118722902704701863609)
              ·
                refine ⟨5061839042177028526397707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749118722902704701863609 5061839042177028526397707)
                ·
                  refine ⟨7592758563265542789596561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061839042177028526397707 7592758563265542789596561)
                  ·
                    refine ⟨5694568922449157092197421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7592758563265542789596561 5694568922449157092197421)
                    ·
                      refine ⟨2135463345918433909574033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694568922449157092197421 2135463345918433909574033)
                      ·
                        rfl

theorem cell23_4158800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_4158800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158800 prefixEnd_4158800 := by exact prefixLift 4158800
  have htrace : WordTrace (prefixWord ++ tailWord_4158800) baseStart_4158800 baseEnd_4158800 := by
    simpa [prefixWord, tailWord_4158800, baseEnd_4158800] using wordTrace_append hprefix tailTrace_4158800
  have hstable : (prefixWord ++ tailWord_4158800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158800).length < 2 ^ (prefixWord ++ tailWord_4158800).sum := by decide
  have hdescent : baseEnd_4158800 < baseStart_4158800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158857 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 3, 3, 2]
def baseStart_4158857 : Nat := 118140960795 + 4158857 * 2 ^ 59
def prefixEnd_4158857 : Nat := 4983230072969 + 3 ^ 40 * 4158857 * 2
def baseEnd_4158857 : Nat := 2135492614315740186561271

theorem tailTrace_4158857 : CollatzResearch.WordTrace tailWord_4158857 prefixEnd_4158857 2135492614315740186561271 := by
  unfold tailWord_4158857
  simp only [CollatzResearch.WordTrace]
  refine ⟨151685976294178840072730825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101123984196119226715153883 151685976294178840072730825)
  ·
    refine ⟨113764482220634130054548119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151685976294178840072730825 113764482220634130054548119)
    ·
      refine ⟨170646723330951195081822179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113764482220634130054548119 170646723330951195081822179)
      ·
        refine ⟨255970084996426792622733269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170646723330951195081822179 255970084996426792622733269)
        ·
          refine ⟨5999298867103752952095311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 255970084996426792622733269 5999298867103752952095311)
          ·
            refine ⟨8998948300655629428142967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999298867103752952095311 8998948300655629428142967)
            ·
              refine ⟨13498422450983444142214451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8998948300655629428142967 13498422450983444142214451)
              ·
                refine ⟨20247633676475166213321677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498422450983444142214451 20247633676475166213321677)
                ·
                  refine ⟨7592862628678187329995629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20247633676475166213321677 7592862628678187329995629)
                  ·
                    refine ⟨2847323485754320248748361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7592862628678187329995629 2847323485754320248748361)
                    ·
                      refine ⟨2135492614315740186561271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847323485754320248748361 2135492614315740186561271)
                      ·
                        rfl

theorem cell23_4158857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3, 2].length) (baseStart_4158857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158857 prefixEnd_4158857 := by exact prefixLift 4158857
  have htrace : WordTrace (prefixWord ++ tailWord_4158857) baseStart_4158857 baseEnd_4158857 := by
    simpa [prefixWord, tailWord_4158857, baseEnd_4158857] using wordTrace_append hprefix tailTrace_4158857
  have hstable : (prefixWord ++ tailWord_4158857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158857).length < 2 ^ (prefixWord ++ tailWord_4158857).sum := by decide
  have hdescent : baseEnd_4158857 < baseStart_4158857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158873 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_4158873 : Nat := 118140960795 + 4158873 * 2 ^ 59
def prefixEnd_4158873 : Nat := 4983230072969 + 3 ^ 40 * 4158873 * 2
def baseEnd_4158873 : Nat := 2135500830006212123961197

theorem tailTrace_4158873 : CollatzResearch.WordTrace tailWord_4158873 prefixEnd_4158873 2135500830006212123961197 := by
  unfold tailWord_4158873
  simp only [CollatzResearch.WordTrace]
  refine ⟨151686559862120874805313273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101124373241413916536875515 151686559862120874805313273)
  ·
    refine ⟨113764919896590656103984955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151686559862120874805313273 113764919896590656103984955)
    ·
      refine ⟨170647379844885984155977433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113764919896590656103984955 170647379844885984155977433)
      ·
        refine ⟨127985534883664488116983075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170647379844885984155977433 127985534883664488116983075)
        ·
          refine ⟨191978302325496732175474613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127985534883664488116983075 191978302325496732175474613)
          ·
            refine ⟨17997965843015318641450745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191978302325496732175474613 17997965843015318641450745)
            ·
              refine ⟨13498474382261488981088059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17997965843015318641450745 13498474382261488981088059)
              ·
                refine ⟨20247711573392233471632089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13498474382261488981088059 20247711573392233471632089)
                ·
                  refine ⟨15185783680044175103724067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20247711573392233471632089 15185783680044175103724067)
                  ·
                    refine ⟨22778675520066262655586101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15185783680044175103724067 22778675520066262655586101)
                    ·
                      refine ⟨2135500830006212123961197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22778675520066262655586101 2135500830006212123961197)
                      ·
                        rfl

theorem cell23_4158873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_4158873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158873 prefixEnd_4158873 := by exact prefixLift 4158873
  have htrace : WordTrace (prefixWord ++ tailWord_4158873) baseStart_4158873 baseEnd_4158873 := by
    simpa [prefixWord, tailWord_4158873, baseEnd_4158873] using wordTrace_append hprefix tailTrace_4158873
  have hstable : (prefixWord ++ tailWord_4158873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158873).length < 2 ^ (prefixWord ++ tailWord_4158873).sum := by decide
  have hdescent : baseEnd_4158873 < baseStart_4158873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158874 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4158874 : Nat := 118140960795 + 4158874 * 2 ^ 59
def prefixEnd_4158874 : Nat := 4983230072969 + 3 ^ 40 * 4158874 * 2
def baseEnd_4158874 : Nat := 2135501343486866620048693

theorem tailTrace_4158874 : CollatzResearch.WordTrace tailWord_4158874 prefixEnd_4158874 2135501343486866620048693 := by
  unfold tailWord_4158874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37921649083779312994024919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101124397556744834650733117 37921649083779312994024919)
  ·
    refine ⟨56882473625668969491037379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37921649083779312994024919 56882473625668969491037379)
    ·
      refine ⟨85323710438503454236556069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56882473625668969491037379 85323710438503454236556069)
      ·
        refine ⟨15998195707219397669354263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85323710438503454236556069 15998195707219397669354263)
        ·
          refine ⟨23997293560829096504031395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15998195707219397669354263 23997293560829096504031395)
          ·
            refine ⟨35995940341243644756047093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23997293560829096504031395 35995940341243644756047093)
            ·
              refine ⟨3374619406991591695879415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35995940341243644756047093 3374619406991591695879415)
              ·
                refine ⟨5061929110487387543819123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374619406991591695879415 5061929110487387543819123)
                ·
                  refine ⟨7592893665731081315728685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5061929110487387543819123 7592893665731081315728685)
                  ·
                    refine ⟨2847335124649155493398257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7592893665731081315728685 2847335124649155493398257)
                    ·
                      refine ⟨2135501343486866620048693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847335124649155493398257 2135501343486866620048693)
                      ·
                        rfl

theorem cell23_4158874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4158874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158874 prefixEnd_4158874 := by exact prefixLift 4158874
  have htrace : WordTrace (prefixWord ++ tailWord_4158874) baseStart_4158874 baseEnd_4158874 := by
    simpa [prefixWord, tailWord_4158874, baseEnd_4158874] using wordTrace_append hprefix tailTrace_4158874
  have hstable : (prefixWord ++ tailWord_4158874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158874).length < 2 ^ (prefixWord ++ tailWord_4158874).sum := by decide
  have hdescent : baseEnd_4158874 < baseStart_4158874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158883 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4158883 : Nat := 118140960795 + 4158883 * 2 ^ 59
def prefixEnd_4158883 : Nat := 4983230072969 + 3 ^ 40 * 4158883 * 2
def baseEnd_4158883 : Nat := 2135505964812757084836151

theorem tailTrace_4158883 : CollatzResearch.WordTrace tailWord_4158883 prefixEnd_4158883 2135505964812757084836151 := by
  unfold tailWord_4158883
  simp only [CollatzResearch.WordTrace]
  refine ⟨151686924592084646513177303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101124616394723097675451535 151686924592084646513177303)
  ·
    refine ⟨227530386888126969769765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151686924592084646513177303 227530386888126969769765955)
    ·
      refine ⟨341295580332190454654648933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227530386888126969769765955 341295580332190454654648933)
      ·
        refine ⟨63992921312285710247746675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341295580332190454654648933 63992921312285710247746675)
        ·
          refine ⟨95989381968428565371620013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63992921312285710247746675 95989381968428565371620013)
          ·
            refine ⟨35996018238160712014357505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95989381968428565371620013 35996018238160712014357505)
            ·
              refine ⟨26997013678620534010768129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35996018238160712014357505 26997013678620534010768129)
              ·
                refine ⟨20247760258965400508076097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26997013678620534010768129 20247760258965400508076097)
                ·
                  refine ⟨15185820194224050381057073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20247760258965400508076097 15185820194224050381057073)
                  ·
                    refine ⟨11389365145668037785792805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15185820194224050381057073 11389365145668037785792805)
                    ·
                      refine ⟨2135505964812757084836151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11389365145668037785792805 2135505964812757084836151)
                      ·
                        rfl

theorem cell23_4158883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4158883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158883 prefixEnd_4158883 := by exact prefixLift 4158883
  have htrace : WordTrace (prefixWord ++ tailWord_4158883) baseStart_4158883 baseEnd_4158883 := by
    simpa [prefixWord, tailWord_4158883, baseEnd_4158883] using wordTrace_append hprefix tailTrace_4158883
  have hstable : (prefixWord ++ tailWord_4158883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158883).length < 2 ^ (prefixWord ++ tailWord_4158883).sum := by decide
  have hdescent : baseEnd_4158883 < baseStart_4158883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158970 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_4158970 : Nat := 118140960795 + 4158970 * 2 ^ 59
def prefixEnd_4158970 : Nat := 4983230072969 + 3 ^ 40 * 4158970 * 2
def baseEnd_4158970 : Nat := 711850212543232748149417

theorem tailTrace_4158970 : CollatzResearch.WordTrace tailWord_4158970 prefixEnd_4158970 711850212543232748149417 := by
  unfold tailWord_4158970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37922524435692365092898591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101126731828512973581062909 37922524435692365092898591)
  ·
    refine ⟨56883786653538547639347887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37922524435692365092898591 56883786653538547639347887)
    ·
      refine ⟨85325679980307821459021831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56883786653538547639347887 85325679980307821459021831)
      ·
        refine ⟨127988519970461732188532747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85325679980307821459021831 127988519970461732188532747)
        ·
          refine ⟨191982779955692598282799121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127988519970461732188532747 191982779955692598282799121)
          ·
            refine ⟨143987084966769448712099341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191982779955692598282799121 143987084966769448712099341)
            ·
              refine ⟨53995156862538543267037253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143987084966769448712099341 53995156862538543267037253)
              ·
                refine ⟨10124091911725976862569485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53995156862538543267037253 10124091911725976862569485)
                ·
                  refine ⟨3796534466897241323463557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10124091911725976862569485 3796534466897241323463557)
                  ·
                    refine ⟨711850212543232748149417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3796534466897241323463557 711850212543232748149417)
                    ·
                      rfl

theorem cell23_4158970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_4158970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158970 prefixEnd_4158970 := by exact prefixLift 4158970
  have htrace : WordTrace (prefixWord ++ tailWord_4158970) baseStart_4158970 baseEnd_4158970 := by
    simpa [prefixWord, tailWord_4158970, baseEnd_4158970] using wordTrace_append hprefix tailTrace_4158970
  have hstable : (prefixWord ++ tailWord_4158970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158970).length < 2 ^ (prefixWord ++ tailWord_4158970).sum := by decide
  have hdescent : baseEnd_4158970 < baseStart_4158970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4158997 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_4158997 : Nat := 118140960795 + 4158997 * 2 ^ 59
def prefixEnd_4158997 : Nat := 4983230072969 + 3 ^ 40 * 4158997 * 2
def baseEnd_4158997 : Nat := 2135564501607369638810627

theorem tailTrace_4158997 : CollatzResearch.WordTrace tailWord_4158997 prefixEnd_4158997 2135564501607369638810627 := by
  unfold tailWord_4158997
  simp only [CollatzResearch.WordTrace]
  refine ⟨151691082513671643982827245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101127388342447762655218163 151691082513671643982827245)
  ·
    refine ⟨56884155942626866493560217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151691082513671643982827245 56884155942626866493560217)
    ·
      refine ⟨42663116956970149870170163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56884155942626866493560217 42663116956970149870170163)
      ·
        refine ⟨63994675435455224805255245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42663116956970149870170163 63994675435455224805255245)
        ·
          refine ⟨23998003288295709301970717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63994675435455224805255245 23998003288295709301970717)
          ·
            refine ⟨8999251233110890988239019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23998003288295709301970717 8999251233110890988239019)
            ·
              refine ⟨13498876849666336482358529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8999251233110890988239019 13498876849666336482358529)
              ·
                refine ⟨10124157637249752361768897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13498876849666336482358529 10124157637249752361768897)
                ·
                  refine ⟨7593118227937314271326673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10124157637249752361768897 7593118227937314271326673)
                  ·
                    refine ⟨5694838670952985703495005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593118227937314271326673 5694838670952985703495005)
                    ·
                      refine ⟨2135564501607369638810627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694838670952985703495005 2135564501607369638810627)
                      ·
                        rfl

theorem cell23_4158997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_4158997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4158997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4158997 prefixEnd_4158997 := by exact prefixLift 4158997
  have htrace : WordTrace (prefixWord ++ tailWord_4158997) baseStart_4158997 baseEnd_4158997 := by
    simpa [prefixWord, tailWord_4158997, baseEnd_4158997] using wordTrace_append hprefix tailTrace_4158997
  have hstable : (prefixWord ++ tailWord_4158997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4158997).length < 2 ^ (prefixWord ++ tailWord_4158997).sum := by decide
  have hdescent : baseEnd_4158997 < baseStart_4158997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4158997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159013 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_4159013 : Nat := 118140960795 + 4159013 * 2 ^ 59
def prefixEnd_4159013 : Nat := 4983230072969 + 3 ^ 40 * 4159013 * 2
def baseEnd_4159013 : Nat := 711857572432613858736851

theorem tailTrace_4159013 : CollatzResearch.WordTrace tailWord_4159013 prefixEnd_4159013 711857572432613858736851 := by
  unfold tailWord_4159013
  simp only [CollatzResearch.WordTrace]
  refine ⟨151691666081613678715409693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101127777387742452476939795 151691666081613678715409693)
  ·
    refine ⟨56884374780605129518278635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151691666081613678715409693 56884374780605129518278635)
    ·
      refine ⟨85326562170907694277417953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56884374780605129518278635 85326562170907694277417953)
      ·
        refine ⟨63994921628180770708063465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85326562170907694277417953 63994921628180770708063465)
        ·
          refine ⟨47996191221135578031047599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63994921628180770708063465 47996191221135578031047599)
          ·
            refine ⟨71994286831703367046571399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47996191221135578031047599 71994286831703367046571399)
            ·
              refine ⟨107991430247555050569857099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71994286831703367046571399 107991430247555050569857099)
              ·
                refine ⟨161987145371332575854785649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107991430247555050569857099 161987145371332575854785649)
                ·
                  refine ⟨121490359028499431891089237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161987145371332575854785649 121490359028499431891089237)
                  ·
                    refine ⟨711857572432613858736851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121490359028499431891089237 711857572432613858736851)
                    ·
                      rfl

theorem cell23_4159013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_4159013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159013 prefixEnd_4159013 := by exact prefixLift 4159013
  have htrace : WordTrace (prefixWord ++ tailWord_4159013) baseStart_4159013 baseEnd_4159013 := by
    simpa [prefixWord, tailWord_4159013, baseEnd_4159013] using wordTrace_append hprefix tailTrace_4159013
  have hstable : (prefixWord ++ tailWord_4159013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159013).length < 2 ^ (prefixWord ++ tailWord_4159013).sum := by decide
  have hdescent : baseEnd_4159013 < baseStart_4159013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159060 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_4159060 : Nat := 118140960795 + 4159060 * 2 ^ 59
def prefixEnd_4159060 : Nat := 4983230072969 + 3 ^ 40 * 4159060 * 2
def baseEnd_4159060 : Nat := 711865616962867630774279

theorem tailTrace_4159060 : CollatzResearch.WordTrace tailWord_4159060 prefixEnd_4159060 711865616962867630774279 := by
  unfold tailWord_4159060
  simp only [CollatzResearch.WordTrace]
  refine ⟨75846690156221702871185317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101128920208295603828247089 75846690156221702871185317)
  ·
    refine ⟨14221254404291569288347247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75846690156221702871185317 14221254404291569288347247)
    ·
      refine ⟨21331881606437353932520871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221254404291569288347247 21331881606437353932520871)
      ·
        refine ⟨31997822409656030898781307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21331881606437353932520871 31997822409656030898781307)
        ·
          refine ⟨47996733614484046348171961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31997822409656030898781307 47996733614484046348171961)
          ·
            refine ⟨35997550210863034761128971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47996733614484046348171961 35997550210863034761128971)
            ·
              refine ⟨53996325316294552141693457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35997550210863034761128971 53996325316294552141693457)
              ·
                refine ⟨40497243987220914106270093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53996325316294552141693457 40497243987220914106270093)
                ·
                  refine ⟨15186466495207842789851285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40497243987220914106270093 15186466495207842789851285)
                  ·
                    refine ⟨711865616962867630774279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15186466495207842789851285 711865616962867630774279)
                    ·
                      rfl

theorem cell23_4159060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_4159060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159060 prefixEnd_4159060 := by exact prefixLift 4159060
  have htrace : WordTrace (prefixWord ++ tailWord_4159060) baseStart_4159060 baseEnd_4159060 := by
    simpa [prefixWord, tailWord_4159060, baseEnd_4159060] using wordTrace_append hprefix tailTrace_4159060
  have hstable : (prefixWord ++ tailWord_4159060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159060).length < 2 ^ (prefixWord ++ tailWord_4159060).sum := by decide
  have hdescent : baseEnd_4159060 < baseStart_4159060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159077 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_4159077 : Nat := 118140960795 + 4159077 * 2 ^ 59
def prefixEnd_4159077 : Nat := 4983230072969 + 3 ^ 40 * 4159077 * 2
def baseEnd_4159077 : Nat := 711868526686576441936753

theorem tailTrace_4159077 : CollatzResearch.WordTrace tailWord_4159077 prefixEnd_4159077 711868526686576441936753 := by
  unfold tailWord_4159077
  simp only [CollatzResearch.WordTrace]
  refine ⟨151694000353381817645739485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101129333568921211763826323 151694000353381817645739485)
  ·
    refine ⟨56885250132518181617152307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151694000353381817645739485 56885250132518181617152307)
    ·
      refine ⟨85327875198777272425728461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56885250132518181617152307 85327875198777272425728461)
      ·
        refine ⟨31997953199541477159648173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85327875198777272425728461 31997953199541477159648173)
        ·
          refine ⟨11999232449828053934868065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31997953199541477159648173 11999232449828053934868065)
          ·
            refine ⟨8999424337371040451151049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11999232449828053934868065 8999424337371040451151049)
            ·
              refine ⟨6749568253028280338363287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8999424337371040451151049 6749568253028280338363287)
              ·
                refine ⟨10124352379542420507544931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6749568253028280338363287 10124352379542420507544931)
                ·
                  refine ⟨15186528569313630761317397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10124352379542420507544931 15186528569313630761317397)
                  ·
                    refine ⟨711868526686576441936753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15186528569313630761317397 711868526686576441936753)
                    ·
                      rfl

theorem cell23_4159077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_4159077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159077 prefixEnd_4159077 := by exact prefixLift 4159077
  have htrace : WordTrace (prefixWord ++ tailWord_4159077) baseStart_4159077 baseEnd_4159077 := by
    simpa [prefixWord, tailWord_4159077, baseEnd_4159077] using wordTrace_append hprefix tailTrace_4159077
  have hstable : (prefixWord ++ tailWord_4159077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159077).length < 2 ^ (prefixWord ++ tailWord_4159077).sum := by decide
  have hdescent : baseEnd_4159077 < baseStart_4159077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159087 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_4159087 : Nat := 118140960795 + 4159087 * 2 ^ 59
def prefixEnd_4159087 : Nat := 4983230072969 + 3 ^ 40 * 4159087 * 2
def baseEnd_4159087 : Nat := 2135610714866274286685213

theorem tailTrace_4159087 : CollatzResearch.WordTrace tailWord_4159087 prefixEnd_4159087 2135610714866274286685213 := by
  unfold tailWord_4159087
  simp only [CollatzResearch.WordTrace]
  refine ⟨151694365083345589353603515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101129576722230392902402343 151694365083345589353603515)
  ·
    refine ⟨227541547625018384030405273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151694365083345589353603515 227541547625018384030405273)
    ·
      refine ⟨170656160718763788022803955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227541547625018384030405273 170656160718763788022803955)
      ·
        refine ⟨255984241078145682034205933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170656160718763788022803955 255984241078145682034205933)
        ·
          refine ⟨95994090404304630762827225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255984241078145682034205933 95994090404304630762827225)
          ·
            refine ⟨71995567803228473072120419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95994090404304630762827225 71995567803228473072120419)
            ·
              refine ⟨107993351704842709608180629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71995567803228473072120419 107993351704842709608180629)
              ·
                refine ⟨5062188361164502012883467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107993351704842709608180629 5062188361164502012883467)
                ·
                  refine ⟨7593282541746753019325201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062188361164502012883467 7593282541746753019325201)
                  ·
                    refine ⟨5694961906310064764493901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593282541746753019325201 5694961906310064764493901)
                    ·
                      refine ⟨2135610714866274286685213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5694961906310064764493901 2135610714866274286685213)
                      ·
                        rfl

theorem cell23_4159087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_4159087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159087 prefixEnd_4159087 := by exact prefixLift 4159087
  have htrace : WordTrace (prefixWord ++ tailWord_4159087) baseStart_4159087 baseEnd_4159087 := by
    simpa [prefixWord, tailWord_4159087, baseEnd_4159087] using wordTrace_append hprefix tailTrace_4159087
  have hstable : (prefixWord ++ tailWord_4159087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159087).length < 2 ^ (prefixWord ++ tailWord_4159087).sum := by decide
  have hdescent : baseEnd_4159087 < baseStart_4159087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159101 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_4159101 : Nat := 118140960795 + 4159101 * 2 ^ 59
def prefixEnd_4159101 : Nat := 4983230072969 + 3 ^ 40 * 4159101 * 2
def baseEnd_4159101 : Nat := 2135617903595437231910149

theorem tailTrace_4159101 : CollatzResearch.WordTrace tailWord_4159101 prefixEnd_4159101 2135617903595437231910149 := by
  unfold tailWord_4159101
  simp only [CollatzResearch.WordTrace]
  refine ⟨151694875705294869744613157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101129917136863246496408771 151694875705294869744613157)
  ·
    refine ⟨28442789194742788077114967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151694875705294869744613157 28442789194742788077114967)
    ·
      refine ⟨42664183792114182115672451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28442789194742788077114967 42664183792114182115672451)
      ·
        refine ⟨63996275688171273173508677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42664183792114182115672451 63996275688171273173508677)
        ·
          refine ⟨11999301691532113720032877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63996275688171273173508677 11999301691532113720032877)
          ·
            refine ⟨4499738134324542645012329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11999301691532113720032877 4499738134324542645012329)
            ·
              refine ⟨3374803600743406983759247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499738134324542645012329 3374803600743406983759247)
              ·
                refine ⟨5062205401115110475638871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374803600743406983759247 5062205401115110475638871)
                ·
                  refine ⟨7593308101672665713458307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062205401115110475638871 7593308101672665713458307)
                  ·
                    refine ⟨11389962152508998570187461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7593308101672665713458307 11389962152508998570187461)
                    ·
                      refine ⟨2135617903595437231910149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11389962152508998570187461 2135617903595437231910149)
                      ·
                        rfl

theorem cell23_4159101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_4159101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159101 prefixEnd_4159101 := by exact prefixLift 4159101
  have htrace : WordTrace (prefixWord ++ tailWord_4159101) baseStart_4159101 baseEnd_4159101 := by
    simpa [prefixWord, tailWord_4159101, baseEnd_4159101] using wordTrace_append hprefix tailTrace_4159101
  have hstable : (prefixWord ++ tailWord_4159101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159101).length < 2 ^ (prefixWord ++ tailWord_4159101).sum := by decide
  have hdescent : baseEnd_4159101 < baseStart_4159101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159118 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4159118 : Nat := 118140960795 + 4159118 * 2 ^ 59
def prefixEnd_4159118 : Nat := 4983230072969 + 3 ^ 40 * 4159118 * 2
def baseEnd_4159118 : Nat := 2135626632766563665397571

theorem tailTrace_4159118 : CollatzResearch.WordTrace tailWord_4159118 prefixEnd_4159118 2135626632766563665397571 := by
  unfold tailWord_4159118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961936968279160205997751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101130330497488854431988005 18961936968279160205997751)
  ·
    refine ⟨28442905452418740308996627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18961936968279160205997751 28442905452418740308996627)
    ·
      refine ⟨42664358178628110463494941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28442905452418740308996627 42664358178628110463494941)
      ·
        refine ⟨15999134316985541423810603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42664358178628110463494941 15999134316985541423810603)
        ·
          refine ⟨23998701475478312135715905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999134316985541423810603 23998701475478312135715905)
          ·
            refine ⟨17999026106608734101786929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23998701475478312135715905 17999026106608734101786929)
            ·
              refine ⟨13499269579956550576340197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17999026106608734101786929 13499269579956550576340197)
              ·
                refine ⟨2531113046241853233063787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13499269579956550576340197 2531113046241853233063787)
                ·
                  refine ⟨3796669569362779849595681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531113046241853233063787 3796669569362779849595681)
                  ·
                    refine ⟨2847502177022084887196761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796669569362779849595681 2847502177022084887196761)
                    ·
                      refine ⟨2135626632766563665397571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847502177022084887196761 2135626632766563665397571)
                      ·
                        rfl

theorem cell23_4159118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4159118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159118 prefixEnd_4159118 := by exact prefixLift 4159118
  have htrace : WordTrace (prefixWord ++ tailWord_4159118) baseStart_4159118 baseEnd_4159118 := by
    simpa [prefixWord, tailWord_4159118, baseEnd_4159118] using wordTrace_append hprefix tailTrace_4159118
  have hstable : (prefixWord ++ tailWord_4159118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159118).length < 2 ^ (prefixWord ++ tailWord_4159118).sum := by decide
  have hdescent : baseEnd_4159118 < baseStart_4159118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159138 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4159138 : Nat := 118140960795 + 4159138 * 2 ^ 59
def prefixEnd_4159138 : Nat := 4983230072969 + 3 ^ 40 * 4159138 * 2
def baseEnd_4159138 : Nat := 2135636902379653587147479

theorem tailTrace_4159138 : CollatzResearch.WordTrace tailWord_4159138 prefixEnd_4159138 2135636902379653587147479 := by
  unfold tailWord_4159138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37924056301540206265927517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101130816804107216709140045 37924056301540206265927517)
  ·
    refine ⟨14221521113077577349722819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37924056301540206265927517 14221521113077577349722819)
    ·
      refine ⟨21332281669616366024584229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14221521113077577349722819 21332281669616366024584229)
      ·
        refine ⟨3999802813053068629609543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21332281669616366024584229 3999802813053068629609543)
        ·
          refine ⟨5999704219579602944414315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3999802813053068629609543 5999704219579602944414315)
          ·
            refine ⟨8999556329369404416621473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5999704219579602944414315 8999556329369404416621473)
            ·
              refine ⟨6749667247027053312466105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8999556329369404416621473 6749667247027053312466105)
              ·
                refine ⟨5062250435270289984349579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6749667247027053312466105 5062250435270289984349579)
                ·
                  refine ⟨7593375652905434976524369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062250435270289984349579 7593375652905434976524369)
                  ·
                    refine ⟨5695031739679076232393277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593375652905434976524369 5695031739679076232393277)
                    ·
                      refine ⟨2135636902379653587147479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5695031739679076232393277 2135636902379653587147479)
                      ·
                        rfl

theorem cell23_4159138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4159138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159138 prefixEnd_4159138 := by exact prefixLift 4159138
  have htrace : WordTrace (prefixWord ++ tailWord_4159138) baseStart_4159138 baseEnd_4159138 := by
    simpa [prefixWord, tailWord_4159138, baseEnd_4159138] using wordTrace_append hprefix tailTrace_4159138
  have hstable : (prefixWord ++ tailWord_4159138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159138).length < 2 ^ (prefixWord ++ tailWord_4159138).sum := by decide
  have hdescent : baseEnd_4159138 < baseStart_4159138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159191 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_4159191 : Nat := 118140960795 + 4159191 * 2 ^ 59
def prefixEnd_4159191 : Nat := 4983230072969 + 3 ^ 40 * 4159191 * 2
def baseEnd_4159191 : Nat := 2135664116854341879784735

theorem tailTrace_4159191 : CollatzResearch.WordTrace tailWord_4159191 prefixEnd_4159191 2135664116854341879784735 := by
  unfold tailWord_4159191
  simp only [CollatzResearch.WordTrace]
  refine ⟨151698158274968815115389427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101132105516645876743592951 151698158274968815115389427)
  ·
    refine ⟨227547237412453222673084141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151698158274968815115389427 227547237412453222673084141)
    ·
      refine ⟨85330214029669958502406553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227547237412453222673084141 85330214029669958502406553)
      ·
        refine ⟨63997660522252468876804915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85330214029669958502406553 63997660522252468876804915)
        ·
          refine ⟨95996490783378703315207373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63997660522252468876804915 95996490783378703315207373)
          ·
            refine ⟨35998684043767013743202765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95996490783378703315207373 35998684043767013743202765)
            ·
              refine ⟨13499506516412630153701037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35998684043767013743202765 13499506516412630153701037)
              ·
                refine ⟨5062314943654736307637889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13499506516412630153701037 5062314943654736307637889)
                ·
                  refine ⟨3796736207741052230728417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062314943654736307637889 3796736207741052230728417)
                  ·
                    refine ⟨2847552155805789173046313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796736207741052230728417 2847552155805789173046313)
                    ·
                      refine ⟨2135664116854341879784735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847552155805789173046313 2135664116854341879784735)
                      ·
                        rfl

theorem cell23_4159191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_4159191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159191 prefixEnd_4159191 := by exact prefixLift 4159191
  have htrace : WordTrace (prefixWord ++ tailWord_4159191) baseStart_4159191 baseEnd_4159191 := by
    simpa [prefixWord, tailWord_4159191, baseEnd_4159191] using wordTrace_append hprefix tailTrace_4159191
  have hstable : (prefixWord ++ tailWord_4159191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159191).length < 2 ^ (prefixWord ++ tailWord_4159191).sum := by decide
  have hdescent : baseEnd_4159191 < baseStart_4159191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159214 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_4159214 : Nat := 118140960795 + 4159214 * 2 ^ 59
def prefixEnd_4159214 : Nat := 4983230072969 + 3 ^ 40 * 4159214 * 2
def baseEnd_4159214 : Nat := 237297325212155032199681

theorem tailTrace_4159214 : CollatzResearch.WordTrace tailWord_4159214 prefixEnd_4159214 237297325212155032199681 := by
  unfold tailWord_4159214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18962374644235686255434587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101132664769256993362317797 18962374644235686255434587)
  ·
    refine ⟨28443561966353529383151881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18962374644235686255434587 28443561966353529383151881)
    ·
      refine ⟨21332671474765147037363911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28443561966353529383151881 21332671474765147037363911)
      ·
        refine ⟨31999007212147720556045867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21332671474765147037363911 31999007212147720556045867)
        ·
          refine ⟨47998510818221580834068801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31999007212147720556045867 47998510818221580834068801)
          ·
            refine ⟨35998883113666185625551601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47998510818221580834068801 35998883113666185625551601)
            ·
              refine ⟨26999162335249639219163701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35998883113666185625551601 26999162335249639219163701)
              ·
                refine ⟨2531171468929653676796597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26999162335249639219163701 2531171468929653676796597)
                ·
                  refine ⟨237297325212155032199681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531171468929653676796597 237297325212155032199681)
                  ·
                    rfl

theorem cell23_4159214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_4159214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159214 prefixEnd_4159214 := by exact prefixLift 4159214
  have htrace : WordTrace (prefixWord ++ tailWord_4159214) baseStart_4159214 baseEnd_4159214 := by
    simpa [prefixWord, tailWord_4159214, baseEnd_4159214] using wordTrace_append hprefix tailTrace_4159214
  have hstable : (prefixWord ++ tailWord_4159214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159214).length < 2 ^ (prefixWord ++ tailWord_4159214).sum := by decide
  have hdescent : baseEnd_4159214 < baseStart_4159214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159264 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4159264 : Nat := 118140960795 + 4159264 * 2 ^ 59
def prefixEnd_4159264 : Nat := 4983230072969 + 3 ^ 40 * 4159264 * 2
def baseEnd_4159264 : Nat := 2135701600942120094171899

theorem tailTrace_4159264 : CollatzResearch.WordTrace tailWord_4159264 prefixEnd_4159264 2135701600942120094171899 := by
  unfold tailWord_4159264
  simp only [CollatzResearch.WordTrace]
  refine ⟨75850410401852174291398423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101133880535802899055197897 75850410401852174291398423)
  ·
    refine ⟨113775615602778261437097635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75850410401852174291398423 113775615602778261437097635)
    ·
      refine ⟨170663423404167392155646453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113775615602778261437097635 170663423404167392155646453)
      ·
        refine ⟨15999695944140693014591855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170663423404167392155646453 15999695944140693014591855)
        ·
          refine ⟨23999543916211039521887783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15999695944140693014591855 23999543916211039521887783)
          ·
            refine ⟨35999315874316559282831675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23999543916211039521887783 35999315874316559282831675)
            ·
              refine ⟨53998973811474838924247513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35999315874316559282831675 53998973811474838924247513)
              ·
                refine ⟨40499230358606129193185635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53998973811474838924247513 40499230358606129193185635)
                ·
                  refine ⟨60748845537909193789778453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40499230358606129193185635 60748845537909193789778453)
                  ·
                    refine ⟨2847602134589493458895865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60748845537909193789778453 2847602134589493458895865)
                    ·
                      refine ⟨2135701600942120094171899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847602134589493458895865 2135701600942120094171899)
                      ·
                        rfl

theorem cell23_4159264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4159264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159264 prefixEnd_4159264 := by exact prefixLift 4159264
  have htrace : WordTrace (prefixWord ++ tailWord_4159264) baseStart_4159264 baseEnd_4159264 := by
    simpa [prefixWord, tailWord_4159264, baseEnd_4159264] using wordTrace_append hprefix tailTrace_4159264
  have hstable : (prefixWord ++ tailWord_4159264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159264).length < 2 ^ (prefixWord ++ tailWord_4159264).sum := by decide
  have hdescent : baseEnd_4159264 < baseStart_4159264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159287 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 6]
def baseStart_4159287 : Nat := 118140960795 + 4159287 * 2 ^ 59
def prefixEnd_4159287 : Nat := 4983230072969 + 3 ^ 40 * 4159287 * 2
def baseEnd_4159287 : Nat := 237301490110797056020477

theorem tailTrace_4159287 : CollatzResearch.WordTrace tailWord_4159287 prefixEnd_4159287 237301490110797056020477 := by
  unfold tailWord_4159287
  simp only [CollatzResearch.WordTrace]
  refine ⟨151701659682621023510884115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101134439788414015673922743 151701659682621023510884115)
  ·
    refine ⟨227552489523931535266326173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151701659682621023510884115 227552489523931535266326173)
    ·
      refine ⟨85332183571474325724872315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227552489523931535266326173 85332183571474325724872315)
      ·
        refine ⟨127998275357211488587308473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85332183571474325724872315 127998275357211488587308473)
        ·
          refine ⟨95998706517908616440481355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127998275357211488587308473 95998706517908616440481355)
          ·
            refine ⟨143998059776862924660722033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95998706517908616440481355 143998059776862924660722033)
            ·
              refine ⟨107998544832647193495541525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143998059776862924660722033 107998544832647193495541525)
              ·
                refine ⟨5062431789030337195103509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107998544832647193495541525 5062431789030337195103509)
                ·
                  refine ⟨237301490110797056020477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5062431789030337195103509 237301490110797056020477)
                  ·
                    rfl

theorem cell23_4159287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 6].length) (baseStart_4159287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159287 prefixEnd_4159287 := by exact prefixLift 4159287
  have htrace : WordTrace (prefixWord ++ tailWord_4159287) baseStart_4159287 baseEnd_4159287 := by
    simpa [prefixWord, tailWord_4159287, baseEnd_4159287] using wordTrace_append hprefix tailTrace_4159287
  have hstable : (prefixWord ++ tailWord_4159287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159287).length < 2 ^ (prefixWord ++ tailWord_4159287).sum := by decide
  have hdescent : baseEnd_4159287 < baseStart_4159287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159341 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4159341 : Nat := 118140960795 + 4159341 * 2 ^ 59
def prefixEnd_4159341 : Nat := 4983230072969 + 3 ^ 40 * 4159341 * 2
def baseEnd_4159341 : Nat := 2135741138952516292909045

theorem tailTrace_4159341 : CollatzResearch.WordTrace tailWord_4159341 prefixEnd_4159341 2135741138952516292909045 := by
  unfold tailWord_4159341
  simp only [CollatzResearch.WordTrace]
  refine ⟨151703629224425390733349877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101135752816283593822233251 151703629224425390733349877)
  ·
    refine ⟨14222215239789880381251551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151703629224425390733349877 14222215239789880381251551)
    ·
      refine ⟨21333322859684820571877327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14222215239789880381251551 21333322859684820571877327)
      ·
        refine ⟨31999984289527230857815991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21333322859684820571877327 31999984289527230857815991)
        ·
          refine ⟨47999976434290846286723987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31999984289527230857815991 47999976434290846286723987)
          ·
            refine ⟨71999964651436269430085981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47999976434290846286723987 71999964651436269430085981)
            ·
              refine ⟨26999986744288601036282243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71999964651436269430085981 26999986744288601036282243)
              ·
                refine ⟨40499980116432901554423365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26999986744288601036282243 40499980116432901554423365)
                ·
                  refine ⟨7593746271831169041454381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40499980116432901554423365 7593746271831169041454381)
                  ·
                    refine ⟨2847654851936688390545393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7593746271831169041454381 2847654851936688390545393)
                    ·
                      refine ⟨2135741138952516292909045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847654851936688390545393 2135741138952516292909045)
                      ·
                        rfl

theorem cell23_4159341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4159341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159341 prefixEnd_4159341 := by exact prefixLift 4159341
  have htrace : WordTrace (prefixWord ++ tailWord_4159341) baseStart_4159341 baseEnd_4159341 := by
    simpa [prefixWord, tailWord_4159341, baseEnd_4159341] using wordTrace_append hprefix tailTrace_4159341
  have hstable : (prefixWord ++ tailWord_4159341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159341).length < 2 ^ (prefixWord ++ tailWord_4159341).sum := by decide
  have hdescent : baseEnd_4159341 < baseStart_4159341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159368 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_4159368 : Nat := 118140960795 + 4159368 * 2 ^ 59
def prefixEnd_4159368 : Nat := 4983230072969 + 3 ^ 40 * 4159368 * 2
def baseEnd_4159368 : Nat := 711918334310062562423807

theorem tailTrace_4159368 : CollatzResearch.WordTrace tailWord_4159368 prefixEnd_4159368 711918334310062562423807 := by
  unfold tailWord_4159368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75852306997663787172291379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101136409330218382896388505 75852306997663787172291379)
  ·
    refine ⟨113778460496495680758437069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75852306997663787172291379 113778460496495680758437069)
    ·
      refine ⟨42666922686185880284413901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113778460496495680758437069 42666922686185880284413901)
      ·
        refine ⟨16000096007319705106655213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42666922686185880284413901 16000096007319705106655213)
        ·
          refine ⟨6000036002744889414995705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16000096007319705106655213 6000036002744889414995705)
          ·
            refine ⟨4500027002058667061246779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000036002744889414995705 4500027002058667061246779)
            ·
              refine ⟨6750040503088000591870169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500027002058667061246779 6750040503088000591870169)
              ·
                refine ⟨5062530377316000443902627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750040503088000591870169 5062530377316000443902627)
                ·
                  refine ⟨7593795565974000665853941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062530377316000443902627 7593795565974000665853941)
                  ·
                    refine ⟨711918334310062562423807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7593795565974000665853941 711918334310062562423807)
                    ·
                      rfl

theorem cell23_4159368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_4159368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159368 prefixEnd_4159368 := by exact prefixLift 4159368
  have htrace : WordTrace (prefixWord ++ tailWord_4159368) baseStart_4159368 baseEnd_4159368 := by
    simpa [prefixWord, tailWord_4159368, baseEnd_4159368] using wordTrace_append hprefix tailTrace_4159368
  have hstable : (prefixWord ++ tailWord_4159368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159368).length < 2 ^ (prefixWord ++ tailWord_4159368).sum := by decide
  have hdescent : baseEnd_4159368 < baseStart_4159368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159371 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 5, 2, 2]
def baseStart_4159371 : Nat := 118140960795 + 4159371 * 2 ^ 59
def prefixEnd_4159371 : Nat := 4983230072969 + 3 ^ 40 * 4159371 * 2
def baseEnd_4159371 : Nat := 2135756543372151175533907

theorem tailTrace_4159371 : CollatzResearch.WordTrace tailWord_4159371 prefixEnd_4159371 2135756543372151175533907 := by
  unfold tailWord_4159371
  simp only [CollatzResearch.WordTrace]
  refine ⟨151704723414316705856941967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101136482276211137237961311 151704723414316705856941967)
  ·
    refine ⟨227557085121475058785412951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151704723414316705856941967 227557085121475058785412951)
    ·
      refine ⟨341335627682212588178119427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227557085121475058785412951 341335627682212588178119427)
      ·
        refine ⟨512003441523318882267179141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341335627682212588178119427 512003441523318882267179141)
        ·
          refine ⟨96000645285622290425096089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512003441523318882267179141 96000645285622290425096089)
          ·
            refine ⟨72000483964216717818822067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96000645285622290425096089 72000483964216717818822067)
            ·
              refine ⟨108000725946325076728233101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72000483964216717818822067 108000725946325076728233101)
              ·
                refine ⟨40500272229871903773087413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108000725946325076728233101 40500272229871903773087413)
                ·
                  refine ⟨3796900521550490978726945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40500272229871903773087413 3796900521550490978726945)
                  ·
                    refine ⟨2847675391162868234045209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3796900521550490978726945 2847675391162868234045209)
                    ·
                      refine ⟨2135756543372151175533907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847675391162868234045209 2135756543372151175533907)
                      ·
                        rfl

theorem cell23_4159371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2, 2].length) (baseStart_4159371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159371 prefixEnd_4159371 := by exact prefixLift 4159371
  have htrace : WordTrace (prefixWord ++ tailWord_4159371) baseStart_4159371 baseEnd_4159371 := by
    simpa [prefixWord, tailWord_4159371, baseEnd_4159371] using wordTrace_append hprefix tailTrace_4159371
  have hstable : (prefixWord ++ tailWord_4159371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159371).length < 2 ^ (prefixWord ++ tailWord_4159371).sum := by decide
  have hdescent : baseEnd_4159371 < baseStart_4159371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159377 : List Nat := [1, 2, 2, 1, 1, 1, 6, 9]
def baseStart_4159377 : Nat := 118140960795 + 4159377 * 2 ^ 59
def prefixEnd_4159377 : Nat := 4983230072969 + 3 ^ 40 * 4159377 * 2
def baseEnd_4159377 : Nat := 79102208305780672298477

theorem tailTrace_4159377 : CollatzResearch.WordTrace tailWord_4159377 prefixEnd_4159377 79102208305780672298477 := by
  unfold tailWord_4159377
  simp only [CollatzResearch.WordTrace]
  refine ⟨151704942252294968881660385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101136628168196645921106923 151704942252294968881660385)
  ·
    refine ⟨113778706689221226661245289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151704942252294968881660385 113778706689221226661245289)
    ·
      refine ⟨85334030016915919995933967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113778706689221226661245289 85334030016915919995933967)
      ·
        refine ⟨128001045025373879993900951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85334030016915919995933967 128001045025373879993900951)
        ·
          refine ⟨192001567538060819990851427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128001045025373879993900951 192001567538060819990851427)
          ·
            refine ⟨288002351307091229986277141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192001567538060819990851427 288002351307091229986277141)
            ·
              refine ⟨13500110217519901405606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288002351307091229986277141 13500110217519901405606741)
              ·
                refine ⟨79102208305780672298477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13500110217519901405606741 79102208305780672298477)
                ·
                  rfl

theorem cell23_4159377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 9].length) (baseStart_4159377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159377 prefixEnd_4159377 := by exact prefixLift 4159377
  have htrace : WordTrace (prefixWord ++ tailWord_4159377) baseStart_4159377 baseEnd_4159377 := by
    simpa [prefixWord, tailWord_4159377, baseEnd_4159377] using wordTrace_append hprefix tailTrace_4159377
  have hstable : (prefixWord ++ tailWord_4159377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159377).length < 2 ^ (prefixWord ++ tailWord_4159377).sum := by decide
  have hdescent : baseEnd_4159377 < baseStart_4159377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159394 : List Nat := [3, 3, 1, 2, 3, 11]
def baseStart_4159394 : Nat := 118140960795 + 4159394 * 2 ^ 59
def prefixEnd_4159394 : Nat := 4983230072969 + 3 ^ 40 * 4159394 * 2
def baseEnd_4159394 : Nat := 8789170178712776072207

theorem tailTrace_4159394 : CollatzResearch.WordTrace tailWord_4159394 prefixEnd_4159394 8789170178712776072207 := by
  unfold tailWord_4159394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926390573308345196257309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101137041528822253856686157 37926390573308345196257309)
  ·
    refine ⟨14222396464990629448596491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37926390573308345196257309 14222396464990629448596491)
    ·
      refine ⟨21333594697485944172894737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14222396464990629448596491 21333594697485944172894737)
      ·
        refine ⟨16000196023114458129671053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21333594697485944172894737 16000196023114458129671053)
        ·
          refine ⟨6000073508667921798626645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16000196023114458129671053 6000073508667921798626645)
          ·
            refine ⟨8789170178712776072207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6000073508667921798626645 8789170178712776072207)
            ·
              rfl

theorem cell23_4159394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 11].length) (baseStart_4159394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159394 prefixEnd_4159394 := by exact prefixLift 4159394
  have htrace : WordTrace (prefixWord ++ tailWord_4159394) baseStart_4159394 baseEnd_4159394 := by
    simpa [prefixWord, tailWord_4159394, baseEnd_4159394] using wordTrace_append hprefix tailTrace_4159394
  have hstable : (prefixWord ++ tailWord_4159394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159394).length < 2 ^ (prefixWord ++ tailWord_4159394).sum := by decide
  have hdescent : baseEnd_4159394 < baseStart_4159394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159407 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 9]
def baseStart_4159407 : Nat := 118140960795 + 4159407 * 2 ^ 59
def prefixEnd_4159407 : Nat := 4983230072969 + 3 ^ 40 * 4159407 * 2
def baseEnd_4159407 : Nat := 711925009558571011561247

theorem tailTrace_4159407 : CollatzResearch.WordTrace tailWord_4159407 prefixEnd_4159407 711925009558571011561247 := by
  unfold tailWord_4159407
  simp only [CollatzResearch.WordTrace]
  refine ⟨151706036442186284005252475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101137357628124189336834983 151706036442186284005252475)
  ·
    refine ⟨227559054663279426007878713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151706036442186284005252475 227559054663279426007878713)
    ·
      refine ⟨170669290997459569505909035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227559054663279426007878713 170669290997459569505909035)
      ·
        refine ⟨256003936496189354258863553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170669290997459569505909035 256003936496189354258863553)
        ·
          refine ⟨192002952372142015694147665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256003936496189354258863553 192002952372142015694147665)
          ·
            refine ⟨144002214279106511770610749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192002952372142015694147665 144002214279106511770610749)
            ·
              refine ⟨54000830354664941913979031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144002214279106511770610749 54000830354664941913979031)
              ·
                refine ⟨81001245531997412870968547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54000830354664941913979031 81001245531997412870968547)
                ·
                  refine ⟨121501868297996119306452821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81001245531997412870968547 121501868297996119306452821)
                  ·
                    refine ⟨711925009558571011561247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121501868297996119306452821 711925009558571011561247)
                    ·
                      rfl

theorem cell23_4159407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_4159407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159407 prefixEnd_4159407 := by exact prefixLift 4159407
  have htrace : WordTrace (prefixWord ++ tailWord_4159407) baseStart_4159407 baseEnd_4159407 := by
    simpa [prefixWord, tailWord_4159407, baseEnd_4159407] using wordTrace_append hprefix tailTrace_4159407
  have hstable : (prefixWord ++ tailWord_4159407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159407).length < 2 ^ (prefixWord ++ tailWord_4159407).sum := by decide
  have hdescent : baseEnd_4159407 < baseStart_4159407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159421 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_4159421 : Nat := 118140960795 + 4159421 * 2 ^ 59
def prefixEnd_4159421 : Nat := 4983230072969 + 3 ^ 40 * 4159421 * 2
def baseEnd_4159421 : Nat := 2135782217404875979908677

theorem tailTrace_4159421 : CollatzResearch.WordTrace tailWord_4159421 prefixEnd_4159421 2135782217404875979908677 := by
  unfold tailWord_4159421
  simp only [CollatzResearch.WordTrace]
  refine ⟨151706547064135564396262117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101137698042757042930841411 151706547064135564396262117)
  ·
    refine ⟨28444977574525418324299147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151706547064135564396262117 28444977574525418324299147)
    ·
      refine ⟨42667466361788127486448721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28444977574525418324299147 42667466361788127486448721)
      ·
        refine ⟨32000599771341095614836541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42667466361788127486448721 32000599771341095614836541)
        ·
          refine ⟨12000224914252910855563703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32000599771341095614836541 12000224914252910855563703)
          ·
            refine ⟨18000337371379366283345555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000224914252910855563703 18000337371379366283345555)
            ·
              refine ⟨27000506057069049425018333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18000337371379366283345555 27000506057069049425018333)
              ·
                refine ⟨10125189771400893534381875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27000506057069049425018333 10125189771400893534381875)
                ·
                  refine ⟨15187784657101340301572813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10125189771400893534381875 15187784657101340301572813)
                  ·
                    refine ⟨5695419246413002613089805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15187784657101340301572813 5695419246413002613089805)
                    ·
                      refine ⟨2135782217404875979908677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5695419246413002613089805 2135782217404875979908677)
                      ·
                        rfl

theorem cell23_4159421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_4159421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159421 prefixEnd_4159421 := by exact prefixLift 4159421
  have htrace : WordTrace (prefixWord ++ tailWord_4159421) baseStart_4159421 baseEnd_4159421 := by
    simpa [prefixWord, tailWord_4159421, baseEnd_4159421] using wordTrace_append hprefix tailTrace_4159421
  have hstable : (prefixWord ++ tailWord_4159421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159421).length < 2 ^ (prefixWord ++ tailWord_4159421).sum := by decide
  have hdescent : baseEnd_4159421 < baseStart_4159421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_4159427 : Nat := 118140960795 + 4159427 * 2 ^ 59
def prefixEnd_4159427 : Nat := 4983230072969 + 3 ^ 40 * 4159427 * 2
def baseEnd_4159427 : Nat := 2135785298288802956433649

theorem tailTrace_4159427 : CollatzResearch.WordTrace tailWord_4159427 prefixEnd_4159427 2135785298288802956433649 := by
  unfold tailWord_4159427
  simp only [CollatzResearch.WordTrace]
  refine ⟨151706765902113827420980535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101137843934742551613987023 151706765902113827420980535)
  ·
    refine ⟨227560148853170741131470803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151706765902113827420980535 227560148853170741131470803)
    ·
      refine ⟨341340223279756111697206205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227560148853170741131470803 341340223279756111697206205)
      ·
        refine ⟨128002583729908541886452327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341340223279756111697206205 128002583729908541886452327)
        ·
          refine ⟨192003875594862812829678491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128002583729908541886452327 192003875594862812829678491)
          ·
            refine ⟨288005813392294219244517737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192003875594862812829678491 288005813392294219244517737)
            ·
              refine ⟨216004360044220664433388303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288005813392294219244517737 216004360044220664433388303)
              ·
                refine ⟨324006540066330996650082455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216004360044220664433388303 324006540066330996650082455)
                ·
                  refine ⟨486009810099496494975123683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324006540066330996650082455 486009810099496494975123683)
                  ·
                    refine ⟨729014715149244742462685525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486009810099496494975123683 729014715149244742462685525)
                    ·
                      refine ⟨2135785298288802956433649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 729014715149244742462685525 2135785298288802956433649)
                      ·
                        rfl

theorem cell23_4159427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_4159427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159427 prefixEnd_4159427 := by exact prefixLift 4159427
  have htrace : WordTrace (prefixWord ++ tailWord_4159427) baseStart_4159427 baseEnd_4159427 := by
    simpa [prefixWord, tailWord_4159427, baseEnd_4159427] using wordTrace_append hprefix tailTrace_4159427
  have hstable : (prefixWord ++ tailWord_4159427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159427).length < 2 ^ (prefixWord ++ tailWord_4159427).sum := by decide
  have hdescent : baseEnd_4159427 < baseStart_4159427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159442 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4159442 : Nat := 118140960795 + 4159442 * 2 ^ 59
def prefixEnd_4159442 : Nat := 4983230072969 + 3 ^ 40 * 4159442 * 2
def baseEnd_4159442 : Nat := 2135793000498620397746081

theorem tailTrace_4159442 : CollatzResearch.WordTrace tailWord_4159442 prefixEnd_4159442 2135793000498620397746081 := by
  unfold tailWord_4159442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37926828249264871245694145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101138208664706323321851053 37926828249264871245694145)
  ·
    refine ⟨28445121186948653434270609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37926828249264871245694145 28445121186948653434270609)
    ·
      refine ⟨21333840890211490075702957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28445121186948653434270609 21333840890211490075702957)
      ·
        refine ⟨8000190333829308778388609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21333840890211490075702957 8000190333829308778388609)
        ·
          refine ⟨6000142750371981583791457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000190333829308778388609 6000142750371981583791457)
          ·
            refine ⟨4500107062778986187843593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000142750371981583791457 4500107062778986187843593)
            ·
              refine ⟨3375080297084239640882695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500107062778986187843593 3375080297084239640882695)
              ·
                refine ⟨5062620445626359461324043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375080297084239640882695 5062620445626359461324043)
                ·
                  refine ⟨7593930668439539191986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062620445626359461324043 7593930668439539191986065)
                  ·
                    refine ⟨5695448001329654393989549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7593930668439539191986065 5695448001329654393989549)
                    ·
                      refine ⟨2135793000498620397746081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5695448001329654393989549 2135793000498620397746081)
                      ·
                        rfl

theorem cell23_4159442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4159442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159442 prefixEnd_4159442 := by exact prefixLift 4159442
  have htrace : WordTrace (prefixWord ++ tailWord_4159442) baseStart_4159442 baseEnd_4159442 := by
    simpa [prefixWord, tailWord_4159442, baseEnd_4159442] using wordTrace_append hprefix tailTrace_4159442
  have hstable : (prefixWord ++ tailWord_4159442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159442).length < 2 ^ (prefixWord ++ tailWord_4159442).sum := by decide
  have hdescent : baseEnd_4159442 < baseStart_4159442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159448 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4159448 : Nat := 118140960795 + 4159448 * 2 ^ 59
def prefixEnd_4159448 : Nat := 4983230072969 + 3 ^ 40 * 4159448 * 2
def baseEnd_4159448 : Nat := 2135796081382547374271053

theorem tailTrace_4159448 : CollatzResearch.WordTrace tailWord_4159448 prefixEnd_4159448 2135796081382547374271053 := by
  unfold tailWord_4159448
  simp only [CollatzResearch.WordTrace]
  refine ⟨75853765917518874003747499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101138354556691832004996665 75853765917518874003747499)
  ·
    refine ⟨113780648876278311005621249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75853765917518874003747499 113780648876278311005621249)
    ·
      refine ⟨85335486657208733254215937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113780648876278311005621249 85335486657208733254215937)
      ·
        refine ⟨64001614992906549940661953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85335486657208733254215937 64001614992906549940661953)
        ·
          refine ⟨48001211244679912455496465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64001614992906549940661953 48001211244679912455496465)
          ·
            refine ⟨36000908433509934341622349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48001211244679912455496465 36000908433509934341622349)
            ·
              refine ⟨13500340662566225378108381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36000908433509934341622349 13500340662566225378108381)
              ·
                refine ⟨5062627748462334516790643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13500340662566225378108381 5062627748462334516790643)
                ·
                  refine ⟨7593941622693501775185965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5062627748462334516790643 7593941622693501775185965)
                  ·
                    refine ⟨2847728108510063165694737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7593941622693501775185965 2847728108510063165694737)
                    ·
                      refine ⟨2135796081382547374271053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847728108510063165694737 2135796081382547374271053)
                      ·
                        rfl

theorem cell23_4159448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4159448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159448 prefixEnd_4159448 := by exact prefixLift 4159448
  have htrace : WordTrace (prefixWord ++ tailWord_4159448) baseStart_4159448 baseEnd_4159448 := by
    simpa [prefixWord, tailWord_4159448, baseEnd_4159448] using wordTrace_append hprefix tailTrace_4159448
  have hstable : (prefixWord ++ tailWord_4159448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159448).length < 2 ^ (prefixWord ++ tailWord_4159448).sum := by decide
  have hdescent : baseEnd_4159448 < baseStart_4159448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159455 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_4159455 : Nat := 118140960795 + 4159455 * 2 ^ 59
def prefixEnd_4159455 : Nat := 4983230072969 + 3 ^ 40 * 4159455 * 2
def baseEnd_4159455 : Nat := 2135799675747128846883521

theorem tailTrace_4159455 : CollatzResearch.WordTrace tailWord_4159455 prefixEnd_4159455 2135799675747128846883521 := by
  unfold tailWord_4159455
  simp only [CollatzResearch.WordTrace]
  refine ⟨151707787146012388202999819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101138524764008258801999879 151707787146012388202999819)
  ·
    refine ⟨227561680719018582304499729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151707787146012388202999819 227561680719018582304499729)
    ·
      refine ⟨170671260539263936728374797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227561680719018582304499729 170671260539263936728374797)
      ·
        refine ⟨64001722702223976273140549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170671260539263936728374797 64001722702223976273140549)
        ·
          refine ⟨12000323006666995551213853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64001722702223976273140549 12000323006666995551213853)
          ·
            refine ⟨4500121127500123331705195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12000323006666995551213853 4500121127500123331705195)
            ·
              refine ⟨6750181691250184997557793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500121127500123331705195 6750181691250184997557793)
              ·
                refine ⟨5062636268437638748168345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6750181691250184997557793 5062636268437638748168345)
                ·
                  refine ⟨3796977201328229061126259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5062636268437638748168345 3796977201328229061126259)
                  ·
                    refine ⟨5695465801992343591689389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3796977201328229061126259 5695465801992343591689389)
                    ·
                      refine ⟨2135799675747128846883521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5695465801992343591689389 2135799675747128846883521)
                      ·
                        rfl

theorem cell23_4159455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_4159455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159455 prefixEnd_4159455 := by exact prefixLift 4159455
  have htrace : WordTrace (prefixWord ++ tailWord_4159455) baseStart_4159455 baseEnd_4159455 := by
    simpa [prefixWord, tailWord_4159455, baseEnd_4159455] using wordTrace_append hprefix tailTrace_4159455
  have hstable : (prefixWord ++ tailWord_4159455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159455).length < 2 ^ (prefixWord ++ tailWord_4159455).sum := by decide
  have hdescent : baseEnd_4159455 < baseStart_4159455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4159464 : Nat := 118140960795 + 4159464 * 2 ^ 59
def prefixEnd_4159464 : Nat := 4983230072969 + 3 ^ 40 * 4159464 * 2
def baseEnd_4159464 : Nat := 2135804297073019311670979

theorem tailTrace_4159464 : CollatzResearch.WordTrace tailWord_4159464 prefixEnd_4159464 2135804297073019311670979 := by
  unfold tailWord_4159464
  simp only [CollatzResearch.WordTrace]
  refine ⟨75854057701489891370038723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101138743601986521826718297 75854057701489891370038723)
  ·
    refine ⟨113781086552234837055058085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75854057701489891370038723 113781086552234837055058085)
    ·
      refine ⟨21333953728544031947823391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113781086552234837055058085 21333953728544031947823391)
      ·
        refine ⟨32000930592816047921735087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21333953728544031947823391 32000930592816047921735087)
        ·
          refine ⟨48001395889224071882602631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32000930592816047921735087 48001395889224071882602631)
          ·
            refine ⟨72002093833836107823903947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48001395889224071882602631 72002093833836107823903947)
            ·
              refine ⟨108003140750754161735855921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72002093833836107823903947 108003140750754161735855921)
              ·
                refine ⟨81002355563065621301891941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108003140750754161735855921 81002355563065621301891941)
                ·
                  refine ⟨15187941668074803994104739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81002355563065621301891941 15187941668074803994104739)
                  ·
                    refine ⟨22781912502112205991157109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15187941668074803994104739 22781912502112205991157109)
                    ·
                      refine ⟨2135804297073019311670979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22781912502112205991157109 2135804297073019311670979)
                      ·
                        rfl

theorem cell23_4159464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4159464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159464 prefixEnd_4159464 := by exact prefixLift 4159464
  have htrace : WordTrace (prefixWord ++ tailWord_4159464) baseStart_4159464 baseEnd_4159464 := by
    simpa [prefixWord, tailWord_4159464, baseEnd_4159464] using wordTrace_append hprefix tailTrace_4159464
  have hstable : (prefixWord ++ tailWord_4159464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159464).length < 2 ^ (prefixWord ++ tailWord_4159464).sum := by decide
  have hdescent : baseEnd_4159464 < baseStart_4159464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159484 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 7]
def baseStart_4159484 : Nat := 118140960795 + 4159484 * 2 ^ 59
def prefixEnd_4159484 : Nat := 4983230072969 + 3 ^ 40 * 4159484 * 2
def baseEnd_4159484 : Nat := 237312729631789914824543

theorem tailTrace_4159484 : CollatzResearch.WordTrace tailWord_4159484 prefixEnd_4159484 237312729631789914824543 := by
  unfold tailWord_4159484
  simp only [CollatzResearch.WordTrace]
  refine ⟨75854422431453663077902753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101139229908604884103870337 75854422431453663077902753)
  ·
    refine ⟨56890816823590247308427065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75854422431453663077902753 56890816823590247308427065)
    ·
      refine ⟨42668112617692685481320299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56890816823590247308427065 42668112617692685481320299)
      ·
        refine ⟨64002168926539028221980449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42668112617692685481320299 64002168926539028221980449)
        ·
          refine ⟨48001626694904271166485337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64002168926539028221980449 48001626694904271166485337)
          ·
            refine ⟨36001220021178203374864003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48001626694904271166485337 36001220021178203374864003)
            ·
              refine ⟨54001830031767305062296005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36001220021178203374864003 54001830031767305062296005)
              ·
                refine ⟨10125343130956369699180501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54001830031767305062296005 10125343130956369699180501)
                ·
                  refine ⟨237312729631789914824543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10125343130956369699180501 237312729631789914824543)
                  ·
                    rfl

theorem cell23_4159484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_4159484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159484 prefixEnd_4159484 := by exact prefixLift 4159484
  have htrace : WordTrace (prefixWord ++ tailWord_4159484) baseStart_4159484 baseEnd_4159484 := by
    simpa [prefixWord, tailWord_4159484, baseEnd_4159484] using wordTrace_append hprefix tailTrace_4159484
  have hstable : (prefixWord ++ tailWord_4159484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159484).length < 2 ^ (prefixWord ++ tailWord_4159484).sum := by decide
  have hdescent : baseEnd_4159484 < baseStart_4159484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159551 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_4159551 : Nat := 118140960795 + 4159551 * 2 ^ 59
def prefixEnd_4159551 : Nat := 4983230072969 + 3 ^ 40 * 4159551 * 2
def baseEnd_4159551 : Nat := 2135848969889960471283079

theorem tailTrace_4159551 : CollatzResearch.WordTrace tailWord_4159551 prefixEnd_4159551 2135848969889960471283079 := by
  unfold tailWord_4159551
  simp only [CollatzResearch.WordTrace]
  refine ⟨151711288553664596598494507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101140859035776397732329671 151711288553664596598494507)
  ·
    refine ⟨227566932830496894897741761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151711288553664596598494507 227566932830496894897741761)
    ·
      refine ⟨170675199622872671173306321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227566932830496894897741761 170675199622872671173306321)
      ·
        refine ⟨128006399717154503379979741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170675199622872671173306321 128006399717154503379979741)
        ·
          refine ⟨48002399893932938767492403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128006399717154503379979741 48002399893932938767492403)
          ·
            refine ⟨72003599840899408151238605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48002399893932938767492403 72003599840899408151238605)
            ·
              refine ⟨27001349940337278056714477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72003599840899408151238605 27001349940337278056714477)
              ·
                refine ⟨10125506227626479271267929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27001349940337278056714477 10125506227626479271267929)
                ·
                  refine ⟨7594129670719859453450947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10125506227626479271267929 7594129670719859453450947)
                  ·
                    refine ⟨11391194506079789180176421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594129670719859453450947 11391194506079789180176421)
                    ·
                      refine ⟨2135848969889960471283079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11391194506079789180176421 2135848969889960471283079)
                      ·
                        rfl

theorem cell23_4159551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_4159551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159551 prefixEnd_4159551 := by exact prefixLift 4159551
  have htrace : WordTrace (prefixWord ++ tailWord_4159551) baseStart_4159551 baseEnd_4159551 := by
    simpa [prefixWord, tailWord_4159551, baseEnd_4159551] using wordTrace_append hprefix tailTrace_4159551
  have hstable : (prefixWord ++ tailWord_4159551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159551).length < 2 ^ (prefixWord ++ tailWord_4159551).sum := by decide
  have hdescent : baseEnd_4159551 < baseStart_4159551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159558 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4159558 : Nat := 118140960795 + 4159558 * 2 ^ 59
def prefixEnd_4159558 : Nat := 4983230072969 + 3 ^ 40 * 4159558 * 2
def baseEnd_4159558 : Nat := 2135852564254541943895547

theorem tailTrace_4159558 : CollatzResearch.WordTrace tailWord_4159558 prefixEnd_4159558 2135852564254541943895547 := by
  unfold tailWord_4159558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740985745769976149812479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101141029243092824529332885 4740985745769976149812479)
  ·
    refine ⟨7111478618654964224718719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4740985745769976149812479 7111478618654964224718719)
    ·
      refine ⟨10667217927982446337078079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7111478618654964224718719 10667217927982446337078079)
      ·
        refine ⟨16000826891973669505617119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10667217927982446337078079 16000826891973669505617119)
        ·
          refine ⟨24001240337960504258425679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16000826891973669505617119 24001240337960504258425679)
          ·
            refine ⟨36001860506940756387638519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24001240337960504258425679 36001860506940756387638519)
            ·
              refine ⟨54002790760411134581457779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36001860506940756387638519 54002790760411134581457779)
              ·
                refine ⟨81004186140616701872186669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54002790760411134581457779 81004186140616701872186669)
                ·
                  refine ⟨30376569802731263202070001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81004186140616701872186669 30376569802731263202070001)
                  ·
                    refine ⟨22782427352048447401552501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30376569802731263202070001 22782427352048447401552501)
                    ·
                      refine ⟨2135852564254541943895547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22782427352048447401552501 2135852564254541943895547)
                      ·
                        rfl

theorem cell23_4159558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4159558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159558 prefixEnd_4159558 := by exact prefixLift 4159558
  have htrace : WordTrace (prefixWord ++ tailWord_4159558) baseStart_4159558 baseEnd_4159558 := by
    simpa [prefixWord, tailWord_4159558, baseEnd_4159558] using wordTrace_append hprefix tailTrace_4159558
  have hstable : (prefixWord ++ tailWord_4159558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159558).length < 2 ^ (prefixWord ++ tailWord_4159558).sum := by decide
  have hdescent : baseEnd_4159558 < baseStart_4159558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159591 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 6]
def baseStart_4159591 : Nat := 118140960795 + 4159591 * 2 ^ 59
def prefixEnd_4159591 : Nat := 4983230072969 + 3 ^ 40 * 4159591 * 2
def baseEnd_4159591 : Nat := 237318834346237812753655

theorem tailTrace_4159591 : CollatzResearch.WordTrace tailWord_4159591 prefixEnd_4159591 237318834346237812753655 := by
  unfold tailWord_4159591
  simp only [CollatzResearch.WordTrace]
  refine ⟨151712747473519683429950627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101141831649013122286633751 151712747473519683429950627)
  ·
    refine ⟨227569121210279525144925941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151712747473519683429950627 227569121210279525144925941)
    ·
      refine ⟨21334605113463705482336807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227569121210279525144925941 21334605113463705482336807)
      ·
        refine ⟨32001907670195558223505211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21334605113463705482336807 32001907670195558223505211)
        ·
          refine ⟨48002861505293337335257817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32001907670195558223505211 48002861505293337335257817)
          ·
            refine ⟨36002146128970003001443363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48002861505293337335257817 36002146128970003001443363)
            ·
              refine ⟨54003219193455004502165045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36002146128970003001443363 54003219193455004502165045)
              ·
                refine ⟨5062801799386406672077973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54003219193455004502165045 5062801799386406672077973)
                ·
                  refine ⟨237318834346237812753655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5062801799386406672077973 237318834346237812753655)
                  ·
                    rfl

theorem cell23_4159591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 6].length) (baseStart_4159591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159591 prefixEnd_4159591 := by exact prefixLift 4159591
  have htrace : WordTrace (prefixWord ++ tailWord_4159591) baseStart_4159591 baseEnd_4159591 := by
    simpa [prefixWord, tailWord_4159591, baseEnd_4159591] using wordTrace_append hprefix tailTrace_4159591
  have hstable : (prefixWord ++ tailWord_4159591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159591).length < 2 ^ (prefixWord ++ tailWord_4159591).sum := by decide
  have hdescent : baseEnd_4159591 < baseStart_4159591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159641 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_4159641 : Nat := 118140960795 + 4159641 * 2 ^ 59
def prefixEnd_4159641 : Nat := 4983230072969 + 3 ^ 40 * 4159641 * 2
def baseEnd_4159641 : Nat := 2135895183148865119157665

theorem tailTrace_4159641 : CollatzResearch.WordTrace tailWord_4159641 prefixEnd_4159641 2135895183148865119157665 := by
  unfold tailWord_4159641
  simp only [CollatzResearch.WordTrace]
  refine ⟨151714571123338541969270777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101143047415559027979513851 151714571123338541969270777)
  ·
    refine ⟨113785928342503906476953083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151714571123338541969270777 113785928342503906476953083)
    ·
      refine ⟨170678892513755859715429625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113785928342503906476953083 170678892513755859715429625)
      ·
        refine ⟨128009169385316894786572219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170678892513755859715429625 128009169385316894786572219)
        ·
          refine ⟨192013754077975342179858329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128009169385316894786572219 192013754077975342179858329)
          ·
            refine ⟨144010315558481506634893747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192013754077975342179858329 144010315558481506634893747)
            ·
              refine ⟨216015473337722259952340621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144010315558481506634893747 216015473337722259952340621)
              ·
                refine ⟨81005802501645847482127733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216015473337722259952340621 81005802501645847482127733)
                ·
                  refine ⟨7594293984529298201449475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81005802501645847482127733 7594293984529298201449475)
                  ·
                    refine ⟨11391440976793947302174213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594293984529298201449475 11391440976793947302174213)
                    ·
                      refine ⟨2135895183148865119157665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11391440976793947302174213 2135895183148865119157665)
                      ·
                        rfl

theorem cell23_4159641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_4159641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159641 prefixEnd_4159641 := by exact prefixLift 4159641
  have htrace : WordTrace (prefixWord ++ tailWord_4159641) baseStart_4159641 baseEnd_4159641 := by
    simpa [prefixWord, tailWord_4159641, baseEnd_4159641] using wordTrace_append hprefix tailTrace_4159641
  have hstable : (prefixWord ++ tailWord_4159641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159641).length < 2 ^ (prefixWord ++ tailWord_4159641).sum := by decide
  have hdescent : baseEnd_4159641 < baseStart_4159641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159698 : List Nat := [3, 2, 2, 2, 1, 3, 2, 8]
def baseStart_4159698 : Nat := 118140960795 + 4159698 * 2 ^ 59
def prefixEnd_4159698 : Nat := 4983230072969 + 3 ^ 40 * 4159698 * 2
def baseEnd_4159698 : Nat := 79108313020228570227589

theorem tailTrace_4159698 : CollatzResearch.WordTrace tailWord_4159698 prefixEnd_4159698 79108313020228570227589 := by
  unfold tailWord_4159698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37929162521033010176023937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101144433389421360469397165 37929162521033010176023937)
  ·
    refine ⟨28446871890774757632017953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37929162521033010176023937 28446871890774757632017953)
    ·
      refine ⟨21335153918081068224013465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28446871890774757632017953 21335153918081068224013465)
      ·
        refine ⟨16001365438560801168010099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21335153918081068224013465 16001365438560801168010099)
        ·
          refine ⟨24002048157841201752015149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16001365438560801168010099 24002048157841201752015149)
          ·
            refine ⟨9000768059190450657005681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24002048157841201752015149 9000768059190450657005681)
            ·
              refine ⟨6750576044392837992754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9000768059190450657005681 6750576044392837992754261)
              ·
                refine ⟨79108313020228570227589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6750576044392837992754261 79108313020228570227589)
                ·
                  rfl

theorem cell23_4159698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_4159698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159698 prefixEnd_4159698 := by exact prefixLift 4159698
  have htrace : WordTrace (prefixWord ++ tailWord_4159698) baseStart_4159698 baseEnd_4159698 := by
    simpa [prefixWord, tailWord_4159698, baseEnd_4159698] using wordTrace_append hprefix tailTrace_4159698
  have hstable : (prefixWord ++ tailWord_4159698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159698).length < 2 ^ (prefixWord ++ tailWord_4159698).sum := by decide
  have hdescent : baseEnd_4159698 < baseStart_4159698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159741 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_4159741 : Nat := 118140960795 + 4159741 * 2 ^ 59
def prefixEnd_4159741 : Nat := 4983230072969 + 3 ^ 40 * 4159741 * 2
def baseEnd_4159741 : Nat := 711982177071438242635735

theorem tailTrace_4159741 : CollatzResearch.WordTrace tailWord_4159741 prefixEnd_4159741 711982177071438242635735 := by
  unfold tailWord_4159741
  simp only [CollatzResearch.WordTrace]
  refine ⟨151718218422976259047911077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101145478948650839365274051 151718218422976259047911077)
  ·
    refine ⟨28447165954308048571483327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151718218422976259047911077 28447165954308048571483327)
    ·
      refine ⟨42670748931462072857224991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28447165954308048571483327 42670748931462072857224991)
      ·
        refine ⟨64006123397193109285837487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42670748931462072857224991 64006123397193109285837487)
        ·
          refine ⟨96009185095789663928756231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64006123397193109285837487 96009185095789663928756231)
          ·
            refine ⟨144013777643684495893134347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96009185095789663928756231 144013777643684495893134347)
            ·
              refine ⟨216020666465526743839701521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144013777643684495893134347 216020666465526743839701521)
              ·
                refine ⟨162015499849145057879776141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216020666465526743839701521 162015499849145057879776141)
                ·
                  refine ⟨60755812443429396704916053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162015499849145057879776141 60755812443429396704916053)
                  ·
                    refine ⟨711982177071438242635735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60755812443429396704916053 711982177071438242635735)
                    ·
                      rfl

theorem cell23_4159741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_4159741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159741 prefixEnd_4159741 := by exact prefixLift 4159741
  have htrace : WordTrace (prefixWord ++ tailWord_4159741) baseStart_4159741 baseEnd_4159741 := by
    simpa [prefixWord, tailWord_4159741, baseEnd_4159741] using wordTrace_append hprefix tailTrace_4159741
  have hstable : (prefixWord ++ tailWord_4159741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159741).length < 2 ^ (prefixWord ++ tailWord_4159741).sum := by decide
  have hdescent : baseEnd_4159741 < baseStart_4159741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159758 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4159758 : Nat := 118140960795 + 4159758 * 2 ^ 59
def prefixEnd_4159758 : Nat := 4983230072969 + 3 ^ 40 * 4159758 * 2
def baseEnd_4159758 : Nat := 711985086795147053798209

theorem tailTrace_4159758 : CollatzResearch.WordTrace tailWord_4159758 prefixEnd_4159758 711985086795147053798209 := by
  unfold tailWord_4159758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18964854807989333868909991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101145892309276447300853285 18964854807989333868909991)
  ·
    refine ⟨28447282211984000803364987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18964854807989333868909991 28447282211984000803364987)
    ·
      refine ⟨42670923317976001205047481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28447282211984000803364987 42670923317976001205047481)
      ·
        refine ⟨32003192488482000903785611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42670923317976001205047481 32003192488482000903785611)
        ·
          refine ⟨48004788732723001355678417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32003192488482000903785611 48004788732723001355678417)
          ·
            refine ⟨36003591549542251016758813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48004788732723001355678417 36003591549542251016758813)
            ·
              refine ⟨13501346831078344131284555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36003591549542251016758813 13501346831078344131284555)
              ·
                refine ⟨20252020246617516196926833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13501346831078344131284555 20252020246617516196926833)
                ·
                  refine ⟨15189015184963137147695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20252020246617516196926833 15189015184963137147695125)
                  ·
                    refine ⟨711985086795147053798209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15189015184963137147695125 711985086795147053798209)
                    ·
                      rfl

theorem cell23_4159758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4159758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159758 prefixEnd_4159758 := by exact prefixLift 4159758
  have htrace : WordTrace (prefixWord ++ tailWord_4159758) baseStart_4159758 baseEnd_4159758 := by
    simpa [prefixWord, tailWord_4159758, baseEnd_4159758] using wordTrace_append hprefix tailTrace_4159758
  have hstable : (prefixWord ++ tailWord_4159758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159758).length < 2 ^ (prefixWord ++ tailWord_4159758).sum := by decide
  have hdescent : baseEnd_4159758 < baseStart_4159758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159765 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_4159765 : Nat := 118140960795 + 4159765 * 2 ^ 59
def prefixEnd_4159765 : Nat := 4983230072969 + 3 ^ 40 * 4159765 * 2
def baseEnd_4159765 : Nat := 2135958854750022634007095

theorem tailTrace_4159765 : CollatzResearch.WordTrace tailWord_4159765 prefixEnd_4159765 2135958854750022634007095 := by
  unfold tailWord_4159765
  simp only [CollatzResearch.WordTrace]
  refine ⟨151719093774889311146784749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101146062516592874097856499 151719093774889311146784749)
  ·
    refine ⟨56894660165583491680044281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151719093774889311146784749 56894660165583491680044281)
    ·
      refine ⟨42670995124187618760033211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56894660165583491680044281 42670995124187618760033211)
      ·
        refine ⟨64006492686281428140049817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42670995124187618760033211 64006492686281428140049817)
        ·
          refine ⟨48004869514711071105037363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64006492686281428140049817 48004869514711071105037363)
          ·
            refine ⟨72007304272066606657556045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48004869514711071105037363 72007304272066606657556045)
            ·
              refine ⟨27002739102024977496583517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72007304272066606657556045 27002739102024977496583517)
              ·
                refine ⟨10126027163259366561218819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27002739102024977496583517 10126027163259366561218819)
                ·
                  refine ⟨15189040744889049841828229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126027163259366561218819 15189040744889049841828229)
                  ·
                    refine ⟨2847945139666696845342793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15189040744889049841828229 2847945139666696845342793)
                    ·
                      refine ⟨2135958854750022634007095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2847945139666696845342793 2135958854750022634007095)
                      ·
                        rfl

theorem cell23_4159765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_4159765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159765 prefixEnd_4159765 := by exact prefixLift 4159765
  have htrace : WordTrace (prefixWord ++ tailWord_4159765) baseStart_4159765 baseEnd_4159765 := by
    simpa [prefixWord, tailWord_4159765, baseEnd_4159765] using wordTrace_append hprefix tailTrace_4159765
  have hstable : (prefixWord ++ tailWord_4159765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159765).length < 2 ^ (prefixWord ++ tailWord_4159765).sum := by decide
  have hdescent : baseEnd_4159765 < baseStart_4159765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159768 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4159768 : Nat := 118140960795 + 4159768 * 2 ^ 59
def prefixEnd_4159768 : Nat := 4983230072969 + 3 ^ 40 * 4159768 * 2
def baseEnd_4159768 : Nat := 2135960395191986122269581

theorem tailTrace_4159768 : CollatzResearch.WordTrace tailWord_4159768 prefixEnd_4159768 2135960395191986122269581 := by
  unfold tailWord_4159768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75859601596939221329571979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101146135462585628439429305 75859601596939221329571979)
  ·
    refine ⟨113789402395408831994357969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75859601596939221329571979 113789402395408831994357969)
    ·
      refine ⟨85342051796556623995768477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113789402395408831994357969 85342051796556623995768477)
      ·
        refine ⟨32003269423708733998413179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85342051796556623995768477 32003269423708733998413179)
        ·
          refine ⟨48004904135563100997619769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32003269423708733998413179 48004904135563100997619769)
          ·
            refine ⟨36003678101672325748214827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48004904135563100997619769 36003678101672325748214827)
            ·
              refine ⟨54005517152508488622322241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36003678101672325748214827 54005517152508488622322241)
              ·
                refine ⟨40504137864381366466741681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54005517152508488622322241 40504137864381366466741681)
                ·
                  refine ⟨30378103398286024850056261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40504137864381366466741681 30378103398286024850056261)
                  ·
                    refine ⟨5695894387178629659385549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30378103398286024850056261 5695894387178629659385549)
                    ·
                      refine ⟨2135960395191986122269581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5695894387178629659385549 2135960395191986122269581)
                      ·
                        rfl

theorem cell23_4159768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4159768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159768 prefixEnd_4159768 := by exact prefixLift 4159768
  have htrace : WordTrace (prefixWord ++ tailWord_4159768) baseStart_4159768 baseEnd_4159768 := by
    simpa [prefixWord, tailWord_4159768, baseEnd_4159768] using wordTrace_append hprefix tailTrace_4159768
  have hstable : (prefixWord ++ tailWord_4159768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159768).length < 2 ^ (prefixWord ++ tailWord_4159768).sum := by decide
  have hdescent : baseEnd_4159768 < baseStart_4159768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159771 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 9]
def baseStart_4159771 : Nat := 118140960795 + 4159771 * 2 ^ 59
def prefixEnd_4159771 : Nat := 4983230072969 + 3 ^ 40 * 4159771 * 2
def baseEnd_4159771 : Nat := 237329103959327734503563

theorem tailTrace_4159771 : CollatzResearch.WordTrace tailWord_4159771 prefixEnd_4159771 237329103959327734503563 := by
  unfold tailWord_4159771
  simp only [CollatzResearch.WordTrace]
  refine ⟨151719312612867574171503167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101146208408578382781002111 151719312612867574171503167)
  ·
    refine ⟨227578968919301361257254751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151719312612867574171503167 227578968919301361257254751)
    ·
      refine ⟨341368453378952041885882127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227578968919301361257254751 341368453378952041885882127)
      ·
        refine ⟨512052680068428062828823191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341368453378952041885882127 512052680068428062828823191)
        ·
          refine ⟨768079020102642094243234787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512052680068428062828823191 768079020102642094243234787)
          ·
            refine ⟨1152118530153963141364852181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768079020102642094243234787 1152118530153963141364852181)
            ·
              refine ⟨27002778050483511125738723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1152118530153963141364852181 27002778050483511125738723)
              ·
                refine ⟨40504167075725266688608085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27002778050483511125738723 40504167075725266688608085)
                ·
                  refine ⟨237329103959327734503563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40504167075725266688608085 237329103959327734503563)
                  ·
                    rfl

theorem cell23_4159771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_4159771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159771 prefixEnd_4159771 := by exact prefixLift 4159771
  have htrace : WordTrace (prefixWord ++ tailWord_4159771) baseStart_4159771 baseEnd_4159771 := by
    simpa [prefixWord, tailWord_4159771, baseEnd_4159771] using wordTrace_append hprefix tailTrace_4159771
  have hstable : (prefixWord ++ tailWord_4159771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159771).length < 2 ^ (prefixWord ++ tailWord_4159771).sum := by decide
  have hdescent : baseEnd_4159771 < baseStart_4159771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159855 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 4, 2]
def baseStart_4159855 : Nat := 118140960795 + 4159855 * 2 ^ 59
def prefixEnd_4159855 : Nat := 4983230072969 + 3 ^ 40 * 4159855 * 2
def baseEnd_4159855 : Nat := 2136005068008927281881681

theorem tailTrace_4159855 : CollatzResearch.WordTrace tailWord_4159855 prefixEnd_4159855 2136005068008927281881681 := by
  unfold tailWord_4159855
  simp only [CollatzResearch.WordTrace]
  refine ⟨151722376344563256517561019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101148250896375504345040679 151722376344563256517561019)
  ·
    refine ⟨227583564516844884776341529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151722376344563256517561019 227583564516844884776341529)
    ·
      refine ⟨170687673387633663582256147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227583564516844884776341529 170687673387633663582256147)
      ·
        refine ⟨256031510081450495373384221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170687673387633663582256147 256031510081450495373384221)
        ·
          refine ⟨96011816280543935765019083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256031510081450495373384221 96011816280543935765019083)
          ·
            refine ⟨144017724420815903647528625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96011816280543935765019083 144017724420815903647528625)
            ·
              refine ⟨108013293315611927735646469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144017724420815903647528625 108013293315611927735646469)
              ·
                refine ⟨20252492496677236450433713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108013293315611927735646469 20252492496677236450433713)
                ·
                  refine ⟨15189369372507927337825285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20252492496677236450433713 15189369372507927337825285)
                  ·
                    refine ⟨2848006757345236375842241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15189369372507927337825285 2848006757345236375842241)
                    ·
                      refine ⟨2136005068008927281881681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848006757345236375842241 2136005068008927281881681)
                      ·
                        rfl

theorem cell23_4159855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4, 2].length) (baseStart_4159855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159855 prefixEnd_4159855 := by exact prefixLift 4159855
  have htrace : WordTrace (prefixWord ++ tailWord_4159855) baseStart_4159855 baseEnd_4159855 := by
    simpa [prefixWord, tailWord_4159855, baseEnd_4159855] using wordTrace_append hprefix tailTrace_4159855
  have hstable : (prefixWord ++ tailWord_4159855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159855).length < 2 ^ (prefixWord ++ tailWord_4159855).sum := by decide
  have hdescent : baseEnd_4159855 < baseStart_4159855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159868 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_4159868 : Nat := 118140960795 + 4159868 * 2 ^ 59
def prefixEnd_4159868 : Nat := 4983230072969 + 3 ^ 40 * 4159868 * 2
def baseEnd_4159868 : Nat := 2136011743257435731019121

theorem tailTrace_4159868 : CollatzResearch.WordTrace tailWord_4159868 prefixEnd_4159868 2136011743257435731019121 := by
  unfold tailWord_4159868
  simp only [CollatzResearch.WordTrace]
  refine ⟨75861425246758079868892129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101148566995677439825189505 75861425246758079868892129)
  ·
    refine ⟨56896068935068559901669097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75861425246758079868892129 56896068935068559901669097)
    ·
      refine ⟨42672051701301419926251823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56896068935068559901669097 42672051701301419926251823)
      ·
        refine ⟨64008077551952129889377735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42672051701301419926251823 64008077551952129889377735)
        ·
          refine ⟨96012116327928194834066603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64008077551952129889377735 96012116327928194834066603)
          ·
            refine ⟨144018174491892292251099905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96012116327928194834066603 144018174491892292251099905)
            ·
              refine ⟨108013630868919219188324929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144018174491892292251099905 108013630868919219188324929)
              ·
                refine ⟨81010223151689414391243697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108013630868919219188324929 81010223151689414391243697)
                ·
                  refine ⟨60757667363767060793432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81010223151689414391243697 60757667363767060793432773)
                  ·
                    refine ⟨11392062630706323898768645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60757667363767060793432773 11392062630706323898768645)
                    ·
                      refine ⟨2136011743257435731019121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11392062630706323898768645 2136011743257435731019121)
                      ·
                        rfl

theorem cell23_4159868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_4159868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159868 prefixEnd_4159868 := by exact prefixLift 4159868
  have htrace : WordTrace (prefixWord ++ tailWord_4159868) baseStart_4159868 baseEnd_4159868 := by
    simpa [prefixWord, tailWord_4159868, baseEnd_4159868] using wordTrace_append hprefix tailTrace_4159868
  have hstable : (prefixWord ++ tailWord_4159868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159868).length < 2 ^ (prefixWord ++ tailWord_4159868).sum := by decide
  have hdescent : baseEnd_4159868 < baseStart_4159868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159912 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 6]
def baseStart_4159912 : Nat := 118140960795 + 4159912 * 2 ^ 59
def prefixEnd_4159912 : Nat := 4983230072969 + 3 ^ 40 * 4159912 * 2
def baseEnd_4159912 : Nat := 237337148489581506540991

theorem tailTrace_4159912 : CollatzResearch.WordTrace tailWord_4159912 prefixEnd_4159912 237337148489581506540991 := by
  unfold tailWord_4159912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75862227652678377626192995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101149636870237836834923993 75862227652678377626192995)
  ·
    refine ⟨113793341479017566439289493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75862227652678377626192995 113793341479017566439289493)
    ·
      refine ⟨5334062881828948426841695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113793341479017566439289493 5334062881828948426841695)
      ·
        refine ⟨8001094322743422640262543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5334062881828948426841695 8001094322743422640262543)
        ·
          refine ⟨12001641484115133960393815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001094322743422640262543 12001641484115133960393815)
          ·
            refine ⟨18002462226172700940590723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001641484115133960393815 18002462226172700940590723)
            ·
              refine ⟨27003693339259051410886085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002462226172700940590723 27003693339259051410886085)
              ·
                refine ⟨5063192501111072139541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27003693339259051410886085 5063192501111072139541141)
                ·
                  refine ⟨237337148489581506540991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5063192501111072139541141 237337148489581506540991)
                  ·
                    rfl

theorem cell23_4159912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_4159912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159912 prefixEnd_4159912 := by exact prefixLift 4159912
  have htrace : WordTrace (prefixWord ++ tailWord_4159912) baseStart_4159912 baseEnd_4159912 := by
    simpa [prefixWord, tailWord_4159912, baseEnd_4159912] using wordTrace_append hprefix tailTrace_4159912
  have hstable : (prefixWord ++ tailWord_4159912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159912).length < 2 ^ (prefixWord ++ tailWord_4159912).sum := by decide
  have hdescent : baseEnd_4159912 < baseStart_4159912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159922 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_4159922 : Nat := 118140960795 + 4159922 * 2 ^ 59
def prefixEnd_4159922 : Nat := 4983230072969 + 3 ^ 40 * 4159922 * 2
def baseEnd_4159922 : Nat := 2136039471212778519743873

theorem tailTrace_4159922 : CollatzResearch.WordTrace tailWord_4159922 prefixEnd_4159922 2136039471212778519743873 := by
  unfold tailWord_4159922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931205008830131740062505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101149880023547017973500013 37931205008830131740062505)
  ·
    refine ⟨28448403756622598805046879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37931205008830131740062505 28448403756622598805046879)
    ·
      refine ⟨42672605634933898207570319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28448403756622598805046879 42672605634933898207570319)
      ·
        refine ⟨64008908452400847311355479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42672605634933898207570319 64008908452400847311355479)
        ·
          refine ⟨96013362678601270967033219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64008908452400847311355479 96013362678601270967033219)
          ·
            refine ⟨144020044017901906450549829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96013362678601270967033219 144020044017901906450549829)
            ·
              refine ⟨27003758253356607459478093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144020044017901906450549829 27003758253356607459478093)
              ·
                refine ⟨10126409345008727797304285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27003758253356607459478093 10126409345008727797304285)
                ·
                  refine ⟨3797403504378272923989107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126409345008727797304285 3797403504378272923989107)
                  ·
                    refine ⟨5696105256567409385983661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797403504378272923989107 5696105256567409385983661)
                    ·
                      refine ⟨2136039471212778519743873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5696105256567409385983661 2136039471212778519743873)
                      ·
                        rfl

theorem cell23_4159922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_4159922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159922 prefixEnd_4159922 := by exact prefixLift 4159922
  have htrace : WordTrace (prefixWord ++ tailWord_4159922) baseStart_4159922 baseEnd_4159922 := by
    simpa [prefixWord, tailWord_4159922, baseEnd_4159922] using wordTrace_append hprefix tailTrace_4159922
  have hstable : (prefixWord ++ tailWord_4159922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159922).length < 2 ^ (prefixWord ++ tailWord_4159922).sum := by decide
  have hdescent : baseEnd_4159922 < baseStart_4159922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159945 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_4159945 : Nat := 118140960795 + 4159945 * 2 ^ 59
def prefixEnd_4159945 : Nat := 4983230072969 + 3 ^ 40 * 4159945 * 2
def baseEnd_4159945 : Nat := 2136051281267831929756267

theorem tailTrace_4159945 : CollatzResearch.WordTrace tailWord_4159945 prefixEnd_4159945 2136051281267831929756267 := by
  unfold tailWord_4159945
  simp only [CollatzResearch.WordTrace]
  refine ⟨151725658914237201888337289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101150439276158134592224859 151725658914237201888337289)
  ·
    refine ⟨113794244185677901416252967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151725658914237201888337289 113794244185677901416252967)
    ·
      refine ⟨170691366278516852124379451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113794244185677901416252967 170691366278516852124379451)
      ·
        refine ⟨256037049417775278186569177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170691366278516852124379451 256037049417775278186569177)
        ·
          refine ⟨192027787063331458639926883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256037049417775278186569177 192027787063331458639926883)
          ·
            refine ⟨288041680594997187959890325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192027787063331458639926883 288041680594997187959890325)
            ·
              refine ⟨13501953777890493185619859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288041680594997187959890325 13501953777890493185619859)
              ·
                refine ⟨20252930666835739778429789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13501953777890493185619859 20252930666835739778429789)
                ·
                  refine ⟨7594849000063402416911171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20252930666835739778429789 7594849000063402416911171)
                  ·
                    refine ⟨11392273500095103625366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594849000063402416911171 11392273500095103625366757)
                    ·
                      refine ⟨2136051281267831929756267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11392273500095103625366757 2136051281267831929756267)
                      ·
                        rfl

theorem cell23_4159945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_4159945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159945 prefixEnd_4159945 := by exact prefixLift 4159945
  have htrace : WordTrace (prefixWord ++ tailWord_4159945) baseStart_4159945 baseEnd_4159945 := by
    simpa [prefixWord, tailWord_4159945, baseEnd_4159945] using wordTrace_append hprefix tailTrace_4159945
  have hstable : (prefixWord ++ tailWord_4159945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159945).length < 2 ^ (prefixWord ++ tailWord_4159945).sum := by decide
  have hdescent : baseEnd_4159945 < baseStart_4159945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159956 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4159956 : Nat := 118140960795 + 4159956 * 2 ^ 59
def prefixEnd_4159956 : Nat := 4983230072969 + 3 ^ 40 * 4159956 * 2
def baseEnd_4159956 : Nat := 2136056929555031386718717

theorem tailTrace_4159956 : CollatzResearch.WordTrace tailWord_4159956 prefixEnd_4159956 2136056929555031386718717 := by
  unfold tailWord_4159956
  simp only [CollatzResearch.WordTrace]
  refine ⟨75863030058598675383493861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101150706744798233844658481 75863030058598675383493861)
  ·
    refine ⟨14224318135987251634405099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75863030058598675383493861 14224318135987251634405099)
    ·
      refine ⟨21336477203980877451607649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14224318135987251634405099 21336477203980877451607649)
      ·
        refine ⟨16002357902985658088705737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21336477203980877451607649 16002357902985658088705737)
        ·
          refine ⟨12001768427239243566529303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16002357902985658088705737 12001768427239243566529303)
          ·
            refine ⟨18002652640858865349793955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12001768427239243566529303 18002652640858865349793955)
            ·
              refine ⟨27003978961288298024690933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18002652640858865349793955 27003978961288298024690933)
              ·
                refine ⟨2531623027620777939814775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27003978961288298024690933 2531623027620777939814775)
                ·
                  refine ⟨3797434541431166909722163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531623027620777939814775 3797434541431166909722163)
                  ·
                    refine ⟨5696151812146750364583245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797434541431166909722163 5696151812146750364583245)
                    ·
                      refine ⟨2136056929555031386718717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5696151812146750364583245 2136056929555031386718717)
                      ·
                        rfl

theorem cell23_4159956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4159956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159956 prefixEnd_4159956 := by exact prefixLift 4159956
  have htrace : WordTrace (prefixWord ++ tailWord_4159956) baseStart_4159956 baseEnd_4159956 := by
    simpa [prefixWord, tailWord_4159956, baseEnd_4159956] using wordTrace_append hprefix tailTrace_4159956
  have hstable : (prefixWord ++ tailWord_4159956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159956).length < 2 ^ (prefixWord ++ tailWord_4159956).sum := by decide
  have hdescent : baseEnd_4159956 < baseStart_4159956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159962 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_4159962 : Nat := 118140960795 + 4159962 * 2 ^ 59
def prefixEnd_4159962 : Nat := 4983230072969 + 3 ^ 40 * 4159962 * 2
def baseEnd_4159962 : Nat := 2136060010438958363243689

theorem tailTrace_4159962 : CollatzResearch.WordTrace tailWord_4159962 prefixEnd_4159962 2136060010438958363243689 := by
  unfold tailWord_4159962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37931569738793903447926535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101150852636783742527804093 37931569738793903447926535)
  ·
    refine ⟨56897354608190855171889803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37931569738793903447926535 56897354608190855171889803)
    ·
      refine ⟨85346031912286282757834705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56897354608190855171889803 85346031912286282757834705)
      ·
        refine ⟨64009523934214712068376029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85346031912286282757834705 64009523934214712068376029)
        ·
          refine ⟨24003571475330517025641011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64009523934214712068376029 24003571475330517025641011)
          ·
            refine ⟨36005357212995775538461517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003571475330517025641011 36005357212995775538461517)
            ·
              refine ⟨13502008954873415826923069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36005357212995775538461517 13502008954873415826923069)
              ·
                refine ⟨5063253358077530935096151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13502008954873415826923069 5063253358077530935096151)
                ·
                  refine ⟨7594880037116296402644227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063253358077530935096151 7594880037116296402644227)
                  ·
                    refine ⟨11392320055674444603966341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7594880037116296402644227 11392320055674444603966341)
                    ·
                      refine ⟨2136060010438958363243689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11392320055674444603966341 2136060010438958363243689)
                      ·
                        rfl

theorem cell23_4159962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_4159962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159962 prefixEnd_4159962 := by exact prefixLift 4159962
  have htrace : WordTrace (prefixWord ++ tailWord_4159962) baseStart_4159962 baseEnd_4159962 := by
    simpa [prefixWord, tailWord_4159962, baseEnd_4159962] using wordTrace_append hprefix tailTrace_4159962
  have hstable : (prefixWord ++ tailWord_4159962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159962).length < 2 ^ (prefixWord ++ tailWord_4159962).sum := by decide
  have hdescent : baseEnd_4159962 < baseStart_4159962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159968 : List Nat := [2, 1, 1, 3, 1, 1, 14]
def baseStart_4159968 : Nat := 118140960795 + 4159968 * 2 ^ 59
def prefixEnd_4159968 : Nat := 4983230072969 + 3 ^ 40 * 4159968 * 2
def baseEnd_4159968 : Nat := 26371149275591177034181

theorem tailTrace_4159968 : CollatzResearch.WordTrace tailWord_4159968 prefixEnd_4159968 26371149275591177034181 := by
  unfold tailWord_4159968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75863248896576938408212279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101150998528769251210949705 75863248896576938408212279)
  ·
    refine ⟨113794873344865407612318419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75863248896576938408212279 113794873344865407612318419)
    ·
      refine ⟨170692310017298111418477629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113794873344865407612318419 170692310017298111418477629)
      ·
        refine ⟨64009616256486791781929111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170692310017298111418477629 64009616256486791781929111)
        ·
          refine ⟨96014424384730187672893667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64009616256486791781929111 96014424384730187672893667)
          ·
            refine ⟨144021636577095281509340501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96014424384730187672893667 144021636577095281509340501)
            ·
              refine ⟨26371149275591177034181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 144021636577095281509340501 26371149275591177034181)
              ·
                rfl

theorem cell23_4159968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 14].length) (baseStart_4159968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159968 prefixEnd_4159968 := by exact prefixLift 4159968
  have htrace : WordTrace (prefixWord ++ tailWord_4159968) baseStart_4159968 baseEnd_4159968 := by
    simpa [prefixWord, tailWord_4159968, baseEnd_4159968] using wordTrace_append hprefix tailTrace_4159968
  have hstable : (prefixWord ++ tailWord_4159968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159968).length < 2 ^ (prefixWord ++ tailWord_4159968).sum := by decide
  have hdescent : baseEnd_4159968 < baseStart_4159968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159975 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4159975 : Nat := 118140960795 + 4159975 * 2 ^ 59
def prefixEnd_4159975 : Nat := 4983230072969 + 3 ^ 40 * 4159975 * 2
def baseEnd_4159975 : Nat := 2136066685687466812381129

theorem tailTrace_4159975 : CollatzResearch.WordTrace tailWord_4159975 prefixEnd_4159975 2136066685687466812381129 := by
  unfold tailWord_4159975
  simp only [CollatzResearch.WordTrace]
  refine ⟨151726753104128517011929379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101151168736085678007952919 151726753104128517011929379)
  ·
    refine ⟨227590129656192775517894069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151726753104128517011929379 227590129656192775517894069)
    ·
      refine ⟨21336574655268072704802569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227590129656192775517894069 21336574655268072704802569)
      ·
        refine ⟨16002430991451054528601927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21336574655268072704802569 16002430991451054528601927)
        ·
          refine ⟨24003646487176581792902891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002430991451054528601927 24003646487176581792902891)
          ·
            refine ⟨36005469730764872689354337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24003646487176581792902891 36005469730764872689354337)
            ·
              refine ⟨27004102298073654517015753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36005469730764872689354337 27004102298073654517015753)
              ·
                refine ⟨20253076723555240887761815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27004102298073654517015753 20253076723555240887761815)
                ·
                  refine ⟨30379615085332861331642723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20253076723555240887761815 30379615085332861331642723)
                  ·
                    refine ⟨45569422627999291997464085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30379615085332861331642723 45569422627999291997464085)
                    ·
                      refine ⟨2136066685687466812381129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45569422627999291997464085 2136066685687466812381129)
                      ·
                        rfl

theorem cell23_4159975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4159975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159975 prefixEnd_4159975 := by exact prefixLift 4159975
  have htrace : WordTrace (prefixWord ++ tailWord_4159975) baseStart_4159975 baseEnd_4159975 := by
    simpa [prefixWord, tailWord_4159975, baseEnd_4159975] using wordTrace_append hprefix tailTrace_4159975
  have hstable : (prefixWord ++ tailWord_4159975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159975).length < 2 ^ (prefixWord ++ tailWord_4159975).sum := by decide
  have hdescent : baseEnd_4159975 < baseStart_4159975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159979 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 3, 2, 2]
def baseStart_4159979 : Nat := 118140960795 + 4159979 * 2 ^ 59
def prefixEnd_4159979 : Nat := 4983230072969 + 3 ^ 40 * 4159979 * 2
def baseEnd_4159979 : Nat := 2136068739610084796731111

theorem tailTrace_4159979 : CollatzResearch.WordTrace tailWord_4159979 prefixEnd_4159979 2136068739610084796731111 := by
  unfold tailWord_4159979
  simp only [CollatzResearch.WordTrace]
  refine ⟨151726898996114025695074991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101151265997409350463383327 151726898996114025695074991)
  ·
    refine ⟨227590348494171038542612487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151726898996114025695074991 227590348494171038542612487)
    ·
      refine ⟨341385522741256557813918731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227590348494171038542612487 341385522741256557813918731)
      ·
        refine ⟨512078284111884836720878097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341385522741256557813918731 512078284111884836720878097)
        ·
          refine ⟨384058713083913627540658573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512078284111884836720878097 384058713083913627540658573)
          ·
            refine ⟨144022017406467610327746965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384058713083913627540658573 144022017406467610327746965)
            ·
              refine ⟨6751032065928169234113139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144022017406467610327746965 6751032065928169234113139)
              ·
                refine ⟨10126548098892253851169709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751032065928169234113139 10126548098892253851169709)
                ·
                  refine ⟨3797455537084595194188641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10126548098892253851169709 3797455537084595194188641)
                  ·
                    refine ⟨2848091652813446395641481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797455537084595194188641 2848091652813446395641481)
                    ·
                      refine ⟨2136068739610084796731111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848091652813446395641481 2136068739610084796731111)
                      ·
                        rfl

theorem cell23_4159979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2, 2].length) (baseStart_4159979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159979 prefixEnd_4159979 := by exact prefixLift 4159979
  have htrace : WordTrace (prefixWord ++ tailWord_4159979) baseStart_4159979 baseEnd_4159979 := by
    simpa [prefixWord, tailWord_4159979, baseEnd_4159979] using wordTrace_append hprefix tailTrace_4159979
  have hstable : (prefixWord ++ tailWord_4159979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159979).length < 2 ^ (prefixWord ++ tailWord_4159979).sum := by decide
  have hdescent : baseEnd_4159979 < baseStart_4159979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4159982 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4159982 : Nat := 118140960795 + 4159982 * 2 ^ 59
def prefixEnd_4159982 : Nat := 4983230072969 + 3 ^ 40 * 4159982 * 2
def baseEnd_4159982 : Nat := 2136070280052048284993597

theorem tailTrace_4159982 : CollatzResearch.WordTrace tailWord_4159982 prefixEnd_4159982 2136070280052048284993597 := by
  unfold tailWord_4159982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965876051887894650929275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101151338943402104804956133 18965876051887894650929275)
  ·
    refine ⟨28448814077831841976393913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18965876051887894650929275 28448814077831841976393913)
    ·
      refine ⟨21336610558373881482295435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28448814077831841976393913 21336610558373881482295435)
      ·
        refine ⟨32004915837560822223443153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21336610558373881482295435 32004915837560822223443153)
        ·
          refine ⟨24003686878170616667582365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32004915837560822223443153 24003686878170616667582365)
          ·
            refine ⟨9001382579313981250343387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24003686878170616667582365 9001382579313981250343387)
            ·
              refine ⟨13502073868970971875515081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001382579313981250343387 13502073868970971875515081)
              ·
                refine ⟨10126555401728228906636311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502073868970971875515081 10126555401728228906636311)
                ·
                  refine ⟨15189833102592343359954467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126555401728228906636311 15189833102592343359954467)
                  ·
                    refine ⟨22784749653888515039931701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15189833102592343359954467 22784749653888515039931701)
                    ·
                      refine ⟨2136070280052048284993597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22784749653888515039931701 2136070280052048284993597)
                      ·
                        rfl

theorem cell23_4159982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4159982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4159982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4159982 prefixEnd_4159982 := by exact prefixLift 4159982
  have htrace : WordTrace (prefixWord ++ tailWord_4159982) baseStart_4159982 baseEnd_4159982 := by
    simpa [prefixWord, tailWord_4159982, baseEnd_4159982] using wordTrace_append hprefix tailTrace_4159982
  have hstable : (prefixWord ++ tailWord_4159982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4159982).length < 2 ^ (prefixWord ++ tailWord_4159982).sum := by decide
  have hdescent : baseEnd_4159982 < baseStart_4159982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4159982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160029 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4160029 : Nat := 118140960795 + 4160029 * 2 ^ 59
def prefixEnd_4160029 : Nat := 4983230072969 + 3 ^ 40 * 4160029 * 2
def baseEnd_4160029 : Nat := 2136094413642809601105881

theorem tailTrace_4160029 : CollatzResearch.WordTrace tailWord_4160029 prefixEnd_4160029 2136094413642809601105881 := by
  unfold tailWord_4160029
  simp only [CollatzResearch.WordTrace]
  refine ⟨151728722645932884234395141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101152481763955256156263427 151728722645932884234395141)
  ·
    refine ⟨28449135496112415793949089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151728722645932884234395141 28449135496112415793949089)
    ·
      refine ⟨21336851622084311845461817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28449135496112415793949089 21336851622084311845461817)
      ·
        refine ⟨16002638716563233884096363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21336851622084311845461817 16002638716563233884096363)
        ·
          refine ⟨24003958074844850826144545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16002638716563233884096363 24003958074844850826144545)
          ·
            refine ⟨18002968556133638119608409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24003958074844850826144545 18002968556133638119608409)
            ·
              refine ⟨13502226417100228589706307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18002968556133638119608409 13502226417100228589706307)
              ·
                refine ⟨20253339625650342884559461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502226417100228589706307 20253339625650342884559461)
                ·
                  refine ⟨3797501179809439290854899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20253339625650342884559461 3797501179809439290854899)
                  ·
                    refine ⟨5696251769714158936282349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3797501179809439290854899 5696251769714158936282349)
                    ·
                      refine ⟨2136094413642809601105881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5696251769714158936282349 2136094413642809601105881)
                      ·
                        rfl

theorem cell23_4160029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4160029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160029 prefixEnd_4160029 := by exact prefixLift 4160029
  have htrace : WordTrace (prefixWord ++ tailWord_4160029) baseStart_4160029 baseEnd_4160029 := by
    simpa [prefixWord, tailWord_4160029, baseEnd_4160029] using wordTrace_append hprefix tailTrace_4160029
  have hstable : (prefixWord ++ tailWord_4160029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160029).length < 2 ^ (prefixWord ++ tailWord_4160029).sum := by decide
  have hdescent : baseEnd_4160029 < baseStart_4160029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160055 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_4160055 : Nat := 118140960795 + 4160055 * 2 ^ 59
def prefixEnd_4160055 : Nat := 4983230072969 + 3 ^ 40 * 4160055 * 2
def baseEnd_4160055 : Nat := 2136107764139826499380761

theorem tailTrace_4160055 : CollatzResearch.WordTrace tailWord_4160055 prefixEnd_4160055 2136107764139826499380761 := by
  unfold tailWord_4160055
  simp only [CollatzResearch.WordTrace]
  refine ⟨151729670943838690674841619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101153113962559127116561079 151729670943838690674841619)
  ·
    refine ⟨227594506415758036012262429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151729670943838690674841619 227594506415758036012262429)
    ·
      refine ⟨85347939905909263504598411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227594506415758036012262429 85347939905909263504598411)
      ·
        refine ⟨128021909858863895256897617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85347939905909263504598411 128021909858863895256897617)
        ·
          refine ⟨96016432394147921442673213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128021909858863895256897617 96016432394147921442673213)
          ·
            refine ⟨36006162147805470541002455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96016432394147921442673213 36006162147805470541002455)
            ·
              refine ⟨54009243221708205811503683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36006162147805470541002455 54009243221708205811503683)
              ·
                refine ⟨81013864832562308717255525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54009243221708205811503683 81013864832562308717255525)
                ·
                  refine ⟨15190099656105432884485411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81013864832562308717255525 15190099656105432884485411)
                  ·
                    refine ⟨22785149484158149326728117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15190099656105432884485411 22785149484158149326728117)
                    ·
                      refine ⟨2136107764139826499380761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22785149484158149326728117 2136107764139826499380761)
                      ·
                        rfl

theorem cell23_4160055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_4160055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160055 prefixEnd_4160055 := by exact prefixLift 4160055
  have htrace : WordTrace (prefixWord ++ tailWord_4160055) baseStart_4160055 baseEnd_4160055 := by
    simpa [prefixWord, tailWord_4160055, baseEnd_4160055] using wordTrace_append hprefix tailTrace_4160055
  have hstable : (prefixWord ++ tailWord_4160055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160055).length < 2 ^ (prefixWord ++ tailWord_4160055).sum := by decide
  have hdescent : baseEnd_4160055 < baseStart_4160055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160069 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_4160069 : Nat := 118140960795 + 4160069 * 2 ^ 59
def prefixEnd_4160069 : Nat := 4983230072969 + 3 ^ 40 * 4160069 * 2
def baseEnd_4160069 : Nat := 2136114952868989444605697

theorem tailTrace_4160069 : CollatzResearch.WordTrace tailWord_4160069 prefixEnd_4160069 2136114952868989444605697 := by
  unfold tailWord_4160069
  simp only [CollatzResearch.WordTrace]
  refine ⟨151730181565787971065851261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101153454377191980710567507 151730181565787971065851261)
  ·
    refine ⟨56898818087170489149694223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151730181565787971065851261 56898818087170489149694223)
    ·
      refine ⟨85348227130755733724541335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56898818087170489149694223 85348227130755733724541335)
      ·
        refine ⟨128022340696133600586812003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85348227130755733724541335 128022340696133600586812003)
        ·
          refine ⟨192033511044200400880218005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128022340696133600586812003 192033511044200400880218005)
          ·
            refine ⟨9001570830196893791260219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192033511044200400880218005 9001570830196893791260219)
            ·
              refine ⟨13502356245295340686890329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001570830196893791260219 13502356245295340686890329)
              ·
                refine ⟨10126767183971505515167747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502356245295340686890329 10126767183971505515167747)
                ·
                  refine ⟨15190150775957258272751621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10126767183971505515167747 15190150775957258272751621)
                  ·
                    refine ⟨2848153270491985926140929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15190150775957258272751621 2848153270491985926140929)
                    ·
                      refine ⟨2136114952868989444605697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848153270491985926140929 2136114952868989444605697)
                      ·
                        rfl

theorem cell23_4160069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_4160069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160069 prefixEnd_4160069 := by exact prefixLift 4160069
  have htrace : WordTrace (prefixWord ++ tailWord_4160069) baseStart_4160069 baseEnd_4160069 := by
    simpa [prefixWord, tailWord_4160069, baseEnd_4160069] using wordTrace_append hprefix tailTrace_4160069
  have hstable : (prefixWord ++ tailWord_4160069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160069).length < 2 ^ (prefixWord ++ tailWord_4160069).sum := by decide
  have hdescent : baseEnd_4160069 < baseStart_4160069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160082 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4160082 : Nat := 118140960795 + 4160082 * 2 ^ 59
def prefixEnd_4160082 : Nat := 4983230072969 + 3 ^ 40 * 4160082 * 2
def baseEnd_4160082 : Nat := 2136121628117497893743137

theorem tailTrace_4160082 : CollatzResearch.WordTrace tailWord_4160082 prefixEnd_4160082 2136121628117497893743137 := by
  unfold tailWord_4160082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37932663928685218571518625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101153770476493916190716333 37932663928685218571518625)
  ·
    refine ⟨28449497946513913928638969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37932663928685218571518625 28449497946513913928638969)
    ·
      refine ⟨21337123459885435446479227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28449497946513913928638969 21337123459885435446479227)
      ·
        refine ⟨32005685189828153169718841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21337123459885435446479227 32005685189828153169718841)
        ·
          refine ⟨24004263892371114877289131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32005685189828153169718841 24004263892371114877289131)
          ·
            refine ⟨36006395838556672315933697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24004263892371114877289131 36006395838556672315933697)
            ·
              refine ⟨27004796878917504236950273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36006395838556672315933697 27004796878917504236950273)
              ·
                refine ⟨20253597659188128177712705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27004796878917504236950273 20253597659188128177712705)
                ·
                  refine ⟨15190198244391096133284529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20253597659188128177712705 15190198244391096133284529)
                  ·
                    refine ⟨11392648683293322099963397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15190198244391096133284529 11392648683293322099963397)
                    ·
                      refine ⟨2136121628117497893743137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11392648683293322099963397 2136121628117497893743137)
                      ·
                        rfl

theorem cell23_4160082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4160082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160082 prefixEnd_4160082 := by exact prefixLift 4160082
  have htrace : WordTrace (prefixWord ++ tailWord_4160082) baseStart_4160082 baseEnd_4160082 := by
    simpa [prefixWord, tailWord_4160082, baseEnd_4160082] using wordTrace_append hprefix tailTrace_4160082
  have hstable : (prefixWord ++ tailWord_4160082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160082).length < 2 ^ (prefixWord ++ tailWord_4160082).sum := by decide
  have hdescent : baseEnd_4160082 < baseStart_4160082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160085 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4160085 : Nat := 118140960795 + 4160085 * 2 ^ 59
def prefixEnd_4160085 : Nat := 4983230072969 + 3 ^ 40 * 4160085 * 2
def baseEnd_4160085 : Nat := 2136123168559461382005623

theorem tailTrace_4160085 : CollatzResearch.WordTrace tailWord_4160085 prefixEnd_4160085 2136123168559461382005623 := by
  unfold tailWord_4160085
  simp only [CollatzResearch.WordTrace]
  refine ⟨151730765133730005798433709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101153843422486670532289139 151730765133730005798433709)
  ·
    refine ⟨56899036925148752174412641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151730765133730005798433709 56899036925148752174412641)
    ·
      refine ⟨42674277693861564130809481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56899036925148752174412641 42674277693861564130809481)
      ·
        refine ⟨32005708270396173098107111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42674277693861564130809481 32005708270396173098107111)
        ·
          refine ⟨48008562405594259647160667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32005708270396173098107111 48008562405594259647160667)
          ·
            refine ⟨72012843608391389470741001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48008562405594259647160667 72012843608391389470741001)
            ·
              refine ⟨54009632706293542103055751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72012843608391389470741001 54009632706293542103055751)
              ·
                refine ⟨81014449059440313154583627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54009632706293542103055751 81014449059440313154583627)
                ·
                  refine ⟨121521673589160469731875441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81014449059440313154583627 121521673589160469731875441)
                  ·
                    refine ⟨91141255191870352298906581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121521673589160469731875441 91141255191870352298906581)
                    ·
                      refine ⟨2136123168559461382005623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91141255191870352298906581 2136123168559461382005623)
                      ·
                        rfl

theorem cell23_4160085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4160085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160085 prefixEnd_4160085 := by exact prefixLift 4160085
  have htrace : WordTrace (prefixWord ++ tailWord_4160085) baseStart_4160085 baseEnd_4160085 := by
    simpa [prefixWord, tailWord_4160085, baseEnd_4160085] using wordTrace_append hprefix tailTrace_4160085
  have hstable : (prefixWord ++ tailWord_4160085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160085).length < 2 ^ (prefixWord ++ tailWord_4160085).sum := by decide
  have hdescent : baseEnd_4160085 < baseStart_4160085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160105 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_4160105 : Nat := 118140960795 + 4160105 * 2 ^ 59
def prefixEnd_4160105 : Nat := 4983230072969 + 3 ^ 40 * 4160105 * 2
def baseEnd_4160105 : Nat := 712044479390850434585177

theorem tailTrace_4160105 : CollatzResearch.WordTrace tailWord_4160105 prefixEnd_4160105 712044479390850434585177 := by
  unfold tailWord_4160105
  simp only [CollatzResearch.WordTrace]
  refine ⟨151731494593657549214161769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101154329729105032809441179 151731494593657549214161769)
  ·
    refine ⟨113798620945243161910621327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151731494593657549214161769 113798620945243161910621327)
    ·
      refine ⟨170697931417864742865931991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113798620945243161910621327 170697931417864742865931991)
      ·
        refine ⟨256046897126797114298897987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170697931417864742865931991 256046897126797114298897987)
        ·
          refine ⟨384070345690195671448346981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256046897126797114298897987 384070345690195671448346981)
          ·
            refine ⟨72013189816911688396565059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384070345690195671448346981 72013189816911688396565059)
            ·
              refine ⟨108019784725367532594847589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72013189816911688396565059 108019784725367532594847589)
              ·
                refine ⟨20253709636006412361533923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108019784725367532594847589 20253709636006412361533923)
                ·
                  refine ⟨30380564454009618542300885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20253709636006412361533923 30380564454009618542300885)
                  ·
                    refine ⟨712044479390850434585177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30380564454009618542300885 712044479390850434585177)
                    ·
                      rfl

theorem cell23_4160105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_4160105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160105 prefixEnd_4160105 := by exact prefixLift 4160105
  have htrace : WordTrace (prefixWord ++ tailWord_4160105) baseStart_4160105 baseEnd_4160105 := by
    simpa [prefixWord, tailWord_4160105, baseEnd_4160105] using wordTrace_append hprefix tailTrace_4160105
  have hstable : (prefixWord ++ tailWord_4160105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160105).length < 2 ^ (prefixWord ++ tailWord_4160105).sum := by decide
  have hdescent : baseEnd_4160105 < baseStart_4160105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160115 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_4160115 : Nat := 118140960795 + 4160115 * 2 ^ 59
def prefixEnd_4160115 : Nat := 4983230072969 + 3 ^ 40 * 4160115 * 2
def baseEnd_4160115 : Nat := 2136138572979096264630485

theorem tailTrace_4160115 : CollatzResearch.WordTrace tailWord_4160115 prefixEnd_4160115 2136138572979096264630485 := by
  unfold tailWord_4160115
  simp only [CollatzResearch.WordTrace]
  refine ⟨151731859323621320922025799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101154572882414213948017199 151731859323621320922025799)
  ·
    refine ⟨227597788985431981383038699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151731859323621320922025799 227597788985431981383038699)
    ·
      refine ⟨341396683478147972074558049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227597788985431981383038699 341396683478147972074558049)
      ·
        refine ⟨256047512608610979055918537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341396683478147972074558049 256047512608610979055918537)
        ·
          refine ⟨192035634456458234291938903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256047512608610979055918537 192035634456458234291938903)
          ·
            refine ⟨288053451684687351437908355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192035634456458234291938903 288053451684687351437908355)
            ·
              refine ⟨432080177527031027156862533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288053451684687351437908355 432080177527031027156862533)
              ·
                refine ⟨81015033286318317591911725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432080177527031027156862533 81015033286318317591911725)
                ·
                  refine ⟨30380637482369369096966897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81015033286318317591911725 30380637482369369096966897)
                  ·
                    refine ⟨22785478111777026822725173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30380637482369369096966897 22785478111777026822725173)
                    ·
                      refine ⟨2136138572979096264630485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22785478111777026822725173 2136138572979096264630485)
                      ·
                        rfl

theorem cell23_4160115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_4160115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160115 prefixEnd_4160115 := by exact prefixLift 4160115
  have htrace : WordTrace (prefixWord ++ tailWord_4160115) baseStart_4160115 baseEnd_4160115 := by
    simpa [prefixWord, tailWord_4160115, baseEnd_4160115] using wordTrace_append hprefix tailTrace_4160115
  have hstable : (prefixWord ++ tailWord_4160115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160115).length < 2 ^ (prefixWord ++ tailWord_4160115).sum := by decide
  have hdescent : baseEnd_4160115 < baseStart_4160115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160193 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4160193 : Nat := 118140960795 + 4160193 * 2 ^ 59
def prefixEnd_4160193 : Nat := 4983230072969 + 3 ^ 40 * 4160193 * 2
def baseEnd_4160193 : Nat := 2136178624470146959455127

theorem tailTrace_4160193 : CollatzResearch.WordTrace tailWord_4160193 prefixEnd_4160193 2136178624470146959455127 := by
  unfold tailWord_4160193
  simp only [CollatzResearch.WordTrace]
  refine ⟨151734704217338740243365233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101156469478225826828910155 151734704217338740243365233)
  ·
    refine ⟨113801028163004055182523925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151734704217338740243365233 113801028163004055182523925)
    ·
      refine ⟨5334423195140815086680809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113801028163004055182523925 5334423195140815086680809)
      ·
        refine ⟨4000817396355611315010607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334423195140815086680809 4000817396355611315010607)
        ·
          refine ⟨6001226094533416972515911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4000817396355611315010607 6001226094533416972515911)
          ·
            refine ⟨9001839141800125458773867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001226094533416972515911 9001839141800125458773867)
            ·
              refine ⟨13502758712700188188160801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001839141800125458773867 13502758712700188188160801)
              ·
                refine ⟨10127069034525141141120601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502758712700188188160801 10127069034525141141120601)
                ·
                  refine ⟨7595301775893855855840451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127069034525141141120601 7595301775893855855840451)
                  ·
                    refine ⟨11392952663840783783760677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595301775893855855840451 11392952663840783783760677)
                    ·
                      refine ⟨2136178624470146959455127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11392952663840783783760677 2136178624470146959455127)
                      ·
                        rfl

theorem cell23_4160193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4160193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160193 prefixEnd_4160193 := by exact prefixLift 4160193
  have htrace : WordTrace (prefixWord ++ tailWord_4160193) baseStart_4160193 baseEnd_4160193 := by
    simpa [prefixWord, tailWord_4160193, baseEnd_4160193] using wordTrace_append hprefix tailTrace_4160193
  have hstable : (prefixWord ++ tailWord_4160193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160193).length < 2 ^ (prefixWord ++ tailWord_4160193).sum := by decide
  have hdescent : baseEnd_4160193 < baseStart_4160193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160196 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4160196 : Nat := 118140960795 + 4160196 * 2 ^ 59
def prefixEnd_4160196 : Nat := 4983230072969 + 3 ^ 40 * 4160196 * 2
def baseEnd_4160196 : Nat := 2136180164912110447717613

theorem tailTrace_4160196 : CollatzResearch.WordTrace tailWord_4160196 prefixEnd_4160196 2136180164912110447717613 := by
  unfold tailWord_4160196
  simp only [CollatzResearch.WordTrace]
  refine ⟨75867406818163935877862221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101156542424218581170482961 75867406818163935877862221)
  ·
    refine ⟨28450277556811475954198333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75867406818163935877862221 28450277556811475954198333)
    ·
      refine ⟨10668854083804303482824375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28450277556811475954198333 10668854083804303482824375)
      ·
        refine ⟨16003281125706455224236563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668854083804303482824375 16003281125706455224236563)
        ·
          refine ⟨24004921688559682836354845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003281125706455224236563 24004921688559682836354845)
          ·
            refine ⟨9001845633209881063633067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24004921688559682836354845 9001845633209881063633067)
            ·
              refine ⟨13502768449814821595449601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001845633209881063633067 13502768449814821595449601)
              ·
                refine ⟨10127076337361116196587201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13502768449814821595449601 10127076337361116196587201)
                ·
                  refine ⟨7595307253020837147440401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127076337361116196587201 7595307253020837147440401)
                  ·
                    refine ⟨5696480439765627860580301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7595307253020837147440401 5696480439765627860580301)
                    ·
                      refine ⟨2136180164912110447717613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5696480439765627860580301 2136180164912110447717613)
                      ·
                        rfl

theorem cell23_4160196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4160196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160196 prefixEnd_4160196 := by exact prefixLift 4160196
  have htrace : WordTrace (prefixWord ++ tailWord_4160196) baseStart_4160196 baseEnd_4160196 := by
    simpa [prefixWord, tailWord_4160196, baseEnd_4160196] using wordTrace_append hprefix tailTrace_4160196
  have hstable : (prefixWord ++ tailWord_4160196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160196).length < 2 ^ (prefixWord ++ tailWord_4160196).sum := by decide
  have hdescent : baseEnd_4160196 < baseStart_4160196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160216 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 6]
def baseStart_4160216 : Nat := 118140960795 + 4160216 * 2 ^ 59
def prefixEnd_4160216 : Nat := 4983230072969 + 3 ^ 40 * 4160216 * 2
def baseEnd_4160216 : Nat := 237354492725022263274169

theorem tailTrace_4160216 : CollatzResearch.WordTrace tailWord_4160216 prefixEnd_4160216 237354492725022263274169 := by
  unfold tailWord_4160216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75867771548127707585726251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101157028730836943447635001 75867771548127707585726251)
  ·
    refine ⟨113801657322191561378589377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75867771548127707585726251 113801657322191561378589377)
    ·
      refine ⟨85351242991643671033942033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113801657322191561378589377 85351242991643671033942033)
      ·
        refine ⟨64013432243732753275456525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85351242991643671033942033 64013432243732753275456525)
        ·
          refine ⟨24005037091399782478296197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64013432243732753275456525 24005037091399782478296197)
          ·
            refine ⟨4500944454637459214680537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24005037091399782478296197 4500944454637459214680537)
            ·
              refine ⟨3375708340978094411010403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4500944454637459214680537 3375708340978094411010403)
              ·
                refine ⟨5063562511467141616515605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375708340978094411010403 5063562511467141616515605)
                ·
                  refine ⟨237354492725022263274169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5063562511467141616515605 237354492725022263274169)
                  ·
                    rfl

theorem cell23_4160216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_4160216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160216 prefixEnd_4160216 := by exact prefixLift 4160216
  have htrace : WordTrace (prefixWord ++ tailWord_4160216) baseStart_4160216 baseEnd_4160216 := by
    simpa [prefixWord, tailWord_4160216, baseEnd_4160216] using wordTrace_append hprefix tailTrace_4160216
  have hstable : (prefixWord ++ tailWord_4160216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160216).length < 2 ^ (prefixWord ++ tailWord_4160216).sum := by decide
  have hdescent : baseEnd_4160216 < baseStart_4160216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160229 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_4160229 : Nat := 118140960795 + 4160229 * 2 ^ 59
def prefixEnd_4160229 : Nat := 4983230072969 + 3 ^ 40 * 4160229 * 2
def baseEnd_4160229 : Nat := 712065703257902939534987

theorem tailTrace_4160229 : CollatzResearch.WordTrace tailWord_4160229 prefixEnd_4160229 712065703257902939534987 := by
  unfold tailWord_4160229
  simp only [CollatzResearch.WordTrace]
  refine ⟨151736017245208318391675741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101157344830138878927783827 151736017245208318391675741)
  ·
    refine ⟨56901006466953119396878403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151736017245208318391675741 56901006466953119396878403)
    ·
      refine ⟨85351509700429679095317605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56901006466953119396878403 85351509700429679095317605)
      ·
        refine ⟨16003408068830564830372051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85351509700429679095317605 16003408068830564830372051)
        ·
          refine ⟨24005112103245847245558077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16003408068830564830372051 24005112103245847245558077)
          ·
            refine ⟨9001917038717192717084279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24005112103245847245558077 9001917038717192717084279)
            ·
              refine ⟨13502875558075789075626419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9001917038717192717084279 13502875558075789075626419)
              ·
                refine ⟨20254313337113683613439629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13502875558075789075626419 20254313337113683613439629)
                ·
                  refine ⟨7595367501417631355039861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20254313337113683613439629 7595367501417631355039861)
                  ·
                    refine ⟨712065703257902939534987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7595367501417631355039861 712065703257902939534987)
                    ·
                      rfl

theorem cell23_4160229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_4160229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160229 prefixEnd_4160229 := by exact prefixLift 4160229
  have htrace : WordTrace (prefixWord ++ tailWord_4160229) baseStart_4160229 baseEnd_4160229 := by
    simpa [prefixWord, tailWord_4160229, baseEnd_4160229] using wordTrace_append hprefix tailTrace_4160229
  have hstable : (prefixWord ++ tailWord_4160229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160229).length < 2 ^ (prefixWord ++ tailWord_4160229).sum := by decide
  have hdescent : baseEnd_4160229 < baseStart_4160229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160249 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_4160249 : Nat := 118140960795 + 4160249 * 2 ^ 59
def prefixEnd_4160249 : Nat := 4983230072969 + 3 ^ 40 * 4160249 * 2
def baseEnd_4160249 : Nat := 2136207379386798740354869

theorem tailTrace_4160249 : CollatzResearch.WordTrace tailWord_4160249 prefixEnd_4160249 2136207379386798740354869 := by
  unfold tailWord_4160249
  simp only [CollatzResearch.WordTrace]
  refine ⟨151736746705135861807403801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101157831136757241204935867 151736746705135861807403801)
  ·
    refine ⟨113802560028851896355552851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151736746705135861807403801 113802560028851896355552851)
    ·
      refine ⟨170703840043277844533329277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113802560028851896355552851 170703840043277844533329277)
      ·
        refine ⟨64013940016229191699998479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170703840043277844533329277 64013940016229191699998479)
        ·
          refine ⟨96020910024343787549997719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64013940016229191699998479 96020910024343787549997719)
          ·
            refine ⟨144031365036515681324996579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96020910024343787549997719 144031365036515681324996579)
            ·
              refine ⟨216047047554773521987494869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144031365036515681324996579 216047047554773521987494869)
              ·
                refine ⟨5063602677065004421581911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216047047554773521987494869 5063602677065004421581911)
                ·
                  refine ⟨7595404015597506632372867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063602677065004421581911 7595404015597506632372867)
                  ·
                    refine ⟨11393106023396259948559301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595404015597506632372867 11393106023396259948559301)
                    ·
                      refine ⟨2136207379386798740354869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11393106023396259948559301 2136207379386798740354869)
                      ·
                        rfl

theorem cell23_4160249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_4160249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160249 prefixEnd_4160249 := by exact prefixLift 4160249
  have htrace : WordTrace (prefixWord ++ tailWord_4160249) baseStart_4160249 baseEnd_4160249 := by
    simpa [prefixWord, tailWord_4160249, baseEnd_4160249] using wordTrace_append hprefix tailTrace_4160249
  have hstable : (prefixWord ++ tailWord_4160249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160249).length < 2 ^ (prefixWord ++ tailWord_4160249).sum := by decide
  have hdescent : baseEnd_4160249 < baseStart_4160249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160289 : List Nat := [1, 2, 3, 2, 1, 2, 5, 7]
def baseStart_4160289 : Nat := 118140960795 + 4160289 * 2 ^ 59
def prefixEnd_4160289 : Nat := 4983230072969 + 3 ^ 40 * 4160289 * 2
def baseEnd_4160289 : Nat := 79119552541221429031655

theorem tailTrace_4160289 : CollatzResearch.WordTrace tailWord_4160289 prefixEnd_4160289 79119552541221429031655 := by
  unfold tailWord_4160289
  simp only [CollatzResearch.WordTrace]
  refine ⟨151738205624990948638859921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101158803749993965759239947 151738205624990948638859921)
  ·
    refine ⟨113803654218743211479144941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151738205624990948638859921 113803654218743211479144941)
    ·
      refine ⟨42676370332028704304679353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113803654218743211479144941 42676370332028704304679353)
      ·
        refine ⟨32007277749021528228509515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42676370332028704304679353 32007277749021528228509515)
        ·
          refine ⟨48010916623532292342764273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32007277749021528228509515 48010916623532292342764273)
          ·
            refine ⟨36008187467649219257073205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48010916623532292342764273 36008187467649219257073205)
            ·
              refine ⟨3375767575092114305350613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36008187467649219257073205 3375767575092114305350613)
              ·
                refine ⟨79119552541221429031655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3375767575092114305350613 79119552541221429031655)
                ·
                  rfl

theorem cell23_4160289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 7].length) (baseStart_4160289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160289 prefixEnd_4160289 := by exact prefixLift 4160289
  have htrace : WordTrace (prefixWord ++ tailWord_4160289) baseStart_4160289 baseEnd_4160289 := by
    simpa [prefixWord, tailWord_4160289, baseEnd_4160289] using wordTrace_append hprefix tailTrace_4160289
  have hstable : (prefixWord ++ tailWord_4160289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160289).length < 2 ^ (prefixWord ++ tailWord_4160289).sum := by decide
  have hdescent : baseEnd_4160289 < baseStart_4160289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160300 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_4160300 : Nat := 118140960795 + 4160300 * 2 ^ 59
def prefixEnd_4160300 : Nat := 4983230072969 + 3 ^ 40 * 4160300 * 2
def baseEnd_4160300 : Nat := 2136233566900178040817135

theorem tailTrace_4160300 : CollatzResearch.WordTrace tailWord_4160300 prefixEnd_4160300 2136233566900178040817135 := by
  unfold tailWord_4160300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75869303413975548758755177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101159071218634065011673569 75869303413975548758755177)
  ·
    refine ⟨56901977560481661569066383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75869303413975548758755177 56901977560481661569066383)
    ·
      refine ⟨85352966340722492353599575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56901977560481661569066383 85352966340722492353599575)
      ·
        refine ⟨128029449511083738530399363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85352966340722492353599575 128029449511083738530399363)
        ·
          refine ⟨192044174266625607795599045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128029449511083738530399363 192044174266625607795599045)
          ·
            refine ⟨36008282674992301461674821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192044174266625607795599045 36008282674992301461674821)
            ·
              refine ⟨6751553001561056524064029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36008282674992301461674821 6751553001561056524064029)
              ·
                refine ⟨2531832375585396196524011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6751553001561056524064029 2531832375585396196524011)
                ·
                  refine ⟨3797748563378094294786017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531832375585396196524011 3797748563378094294786017)
                  ·
                    refine ⟨2848311422533570721089513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797748563378094294786017 2848311422533570721089513)
                    ·
                      refine ⟨2136233566900178040817135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848311422533570721089513 2136233566900178040817135)
                      ·
                        rfl

theorem cell23_4160300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_4160300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160300 prefixEnd_4160300 := by exact prefixLift 4160300
  have htrace : WordTrace (prefixWord ++ tailWord_4160300) baseStart_4160300 baseEnd_4160300 := by
    simpa [prefixWord, tailWord_4160300, baseEnd_4160300] using wordTrace_append hprefix tailTrace_4160300
  have hstable : (prefixWord ++ tailWord_4160300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160300).length < 2 ^ (prefixWord ++ tailWord_4160300).sum := by decide
  have hdescent : baseEnd_4160300 < baseStart_4160300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160343 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_4160343 : Nat := 118140960795 + 4160343 * 2 ^ 59
def prefixEnd_4160343 : Nat := 4983230072969 + 3 ^ 40 * 4160343 * 2
def baseEnd_4160343 : Nat := 2136255646568321372579437

theorem tailTrace_4160343 : CollatzResearch.WordTrace tailWord_4160343 prefixEnd_4160343 2136255646568321372579437 := by
  unfold tailWord_4160343
  simp only [CollatzResearch.WordTrace]
  refine ⟨151740175166795315861325683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101160116777863543907550455 151740175166795315861325683)
  ·
    refine ⟨227610262750192973791988525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151740175166795315861325683 227610262750192973791988525)
    ·
      refine ⟨85353848531322365171995697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227610262750192973791988525 85353848531322365171995697)
      ·
        refine ⟨64015386398491773878996773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85353848531322365171995697 64015386398491773878996773)
        ·
          refine ⟨12002884949717207602311895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64015386398491773878996773 12002884949717207602311895)
          ·
            refine ⟨18004327424575811403467843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12002884949717207602311895 18004327424575811403467843)
            ·
              refine ⟨27006491136863717105201765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004327424575811403467843 27006491136863717105201765)
              ·
                refine ⟨5063717088161946957225331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27006491136863717105201765 5063717088161946957225331)
                ·
                  refine ⟨7595575632242920435837997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063717088161946957225331 7595575632242920435837997)
                  ·
                    refine ⟨2848340862091095163439249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7595575632242920435837997 2848340862091095163439249)
                    ·
                      refine ⟨2136255646568321372579437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848340862091095163439249 2136255646568321372579437)
                      ·
                        rfl

theorem cell23_4160343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_4160343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160343 prefixEnd_4160343 := by exact prefixLift 4160343
  have htrace : WordTrace (prefixWord ++ tailWord_4160343) baseStart_4160343 baseEnd_4160343 := by
    simpa [prefixWord, tailWord_4160343, baseEnd_4160343] using wordTrace_append hprefix tailTrace_4160343
  have hstable : (prefixWord ++ tailWord_4160343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160343).length < 2 ^ (prefixWord ++ tailWord_4160343).sum := by decide
  have hdescent : baseEnd_4160343 < baseStart_4160343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160359 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4160359 : Nat := 118140960795 + 4160359 * 2 ^ 59
def prefixEnd_4160359 : Nat := 4983230072969 + 3 ^ 40 * 4160359 * 2
def baseEnd_4160359 : Nat := 2136263862258793309979363

theorem tailTrace_4160359 : CollatzResearch.WordTrace tailWord_4160359 prefixEnd_4160359 2136263862258793309979363 := by
  unfold tailWord_4160359
  simp only [CollatzResearch.WordTrace]
  refine ⟨151740758734737350593908131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101160505823158233729272087 151740758734737350593908131)
  ·
    refine ⟨227611138102106025890862197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151740758734737350593908131 227611138102106025890862197)
    ·
      refine ⟨21338544197072439927268331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227611138102106025890862197 21338544197072439927268331)
      ·
        refine ⟨32007816295608659890902497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21338544197072439927268331 32007816295608659890902497)
        ·
          refine ⟨24005862221706494918176873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32007816295608659890902497 24005862221706494918176873)
          ·
            refine ⟨18004396666279871188632655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24005862221706494918176873 18004396666279871188632655)
            ·
              refine ⟨27006594999419806782948983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004396666279871188632655 27006594999419806782948983)
              ·
                refine ⟨40509892499129710174423475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27006594999419806782948983 40509892499129710174423475)
                ·
                  refine ⟨60764838748694565261635213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40509892499129710174423475 60764838748694565261635213)
                  ·
                    refine ⟨22786814530760461973113205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60764838748694565261635213 22786814530760461973113205)
                    ·
                      refine ⟨2136263862258793309979363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22786814530760461973113205 2136263862258793309979363)
                      ·
                        rfl

theorem cell23_4160359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4160359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160359 prefixEnd_4160359 := by exact prefixLift 4160359
  have htrace : WordTrace (prefixWord ++ tailWord_4160359) baseStart_4160359 baseEnd_4160359 := by
    simpa [prefixWord, tailWord_4160359, baseEnd_4160359] using wordTrace_append hprefix tailTrace_4160359
  have hstable : (prefixWord ++ tailWord_4160359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160359).length < 2 ^ (prefixWord ++ tailWord_4160359).sum := by decide
  have hdescent : baseEnd_4160359 < baseStart_4160359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160379 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 7]
def baseStart_4160379 : Nat := 118140960795 + 4160379 * 2 ^ 59
def prefixEnd_4160379 : Nat := 4983230072969 + 3 ^ 40 * 4160379 * 2
def baseEnd_4160379 : Nat := 237363792430209247969919

theorem tailTrace_4160379 : CollatzResearch.WordTrace tailWord_4160379 prefixEnd_4160379 237363792430209247969919 := by
  unfold tailWord_4160379
  simp only [CollatzResearch.WordTrace]
  refine ⟨151741488194664894009636191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101160992129776596006424127 151741488194664894009636191)
  ·
    refine ⟨227612232291997341014454287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151741488194664894009636191 227612232291997341014454287)
    ·
      refine ⟨341418348437996011521681431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227612232291997341014454287 341418348437996011521681431)
      ·
        refine ⟨512127522656994017282522147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341418348437996011521681431 512127522656994017282522147)
        ·
          refine ⟨768191283985491025923783221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512127522656994017282522147 768191283985491025923783221)
          ·
            refine ⟨72017932873639783680354677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 768191283985491025923783221 72017932873639783680354677)
            ·
              refine ⟨6751681206903729720033251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72017932873639783680354677 6751681206903729720033251)
              ·
                refine ⟨10127521810355594580049877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751681206903729720033251 10127521810355594580049877)
                ·
                  refine ⟨237363792430209247969919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10127521810355594580049877 237363792430209247969919)
                  ·
                    rfl

theorem cell23_4160379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 7].length) (baseStart_4160379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160379 prefixEnd_4160379 := by exact prefixLift 4160379
  have htrace : WordTrace (prefixWord ++ tailWord_4160379) baseStart_4160379 baseEnd_4160379 := by
    simpa [prefixWord, tailWord_4160379, baseEnd_4160379] using wordTrace_append hprefix tailTrace_4160379
  have hstable : (prefixWord ++ tailWord_4160379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160379).length < 2 ^ (prefixWord ++ tailWord_4160379).sum := by decide
  have hdescent : baseEnd_4160379 < baseStart_4160379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160419 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4160419 : Nat := 118140960795 + 4160419 * 2 ^ 59
def prefixEnd_4160419 : Nat := 4983230072969 + 3 ^ 40 * 4160419 * 2
def baseEnd_4160419 : Nat := 2136294671098063075229087

theorem tailTrace_4160419 : CollatzResearch.WordTrace tailWord_4160419 prefixEnd_4160419 2136294671098063075229087 := by
  unfold tailWord_4160419
  simp only [CollatzResearch.WordTrace]
  refine ⟨151742947114519980841092311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101161964743013320560728207 151742947114519980841092311)
  ·
    refine ⟨227614420671779971261638467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151742947114519980841092311 227614420671779971261638467)
    ·
      refine ⟨341421631007669956892457701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227614420671779971261638467 341421631007669956892457701)
      ·
        refine ⟨64016555813938116917335819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341421631007669956892457701 64016555813938116917335819)
        ·
          refine ⟨96024833720907175376003729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64016555813938116917335819 96024833720907175376003729)
          ·
            refine ⟨72018625290680381532002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96024833720907175376003729 72018625290680381532002797)
            ·
              refine ⟨27006984484005143074501049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72018625290680381532002797 27006984484005143074501049)
              ·
                refine ⟨20255238363003857305875787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27006984484005143074501049 20255238363003857305875787)
                ·
                  refine ⟨30382857544505785958813681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255238363003857305875787 30382857544505785958813681)
                  ·
                    refine ⟨22787143158379339469110261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30382857544505785958813681 22787143158379339469110261)
                    ·
                      refine ⟨2136294671098063075229087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22787143158379339469110261 2136294671098063075229087)
                      ·
                        rfl

theorem cell23_4160419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4160419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160419 prefixEnd_4160419 := by exact prefixLift 4160419
  have htrace : WordTrace (prefixWord ++ tailWord_4160419) baseStart_4160419 baseEnd_4160419 := by
    simpa [prefixWord, tailWord_4160419, baseEnd_4160419] using wordTrace_append hprefix tailTrace_4160419
  have hstable : (prefixWord ++ tailWord_4160419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160419).length < 2 ^ (prefixWord ++ tailWord_4160419).sum := by decide
  have hdescent : baseEnd_4160419 < baseStart_4160419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160446 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4160446 : Nat := 118140960795 + 4160446 * 2 ^ 59
def prefixEnd_4160446 : Nat := 4983230072969 + 3 ^ 40 * 4160446 * 2
def baseEnd_4160446 : Nat := 2136308535075734469591463

theorem tailTrace_4160446 : CollatzResearch.WordTrace tailWord_4160446 prefixEnd_4160446 2136308535075734469591463 := by
  unfold tailWord_4160446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967991485677770556540649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101162621256948109634883461 18967991485677770556540649)
  ·
    refine ⟨14225993614258327917405487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18967991485677770556540649 14225993614258327917405487)
    ·
      refine ⟨21338990421387491876108231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225993614258327917405487 21338990421387491876108231)
      ·
        refine ⟨32008485632081237814162347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21338990421387491876108231 32008485632081237814162347)
        ·
          refine ⟨48012728448121856721243521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32008485632081237814162347 48012728448121856721243521)
          ·
            refine ⟨36009546336091392540932641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48012728448121856721243521 36009546336091392540932641)
            ·
              refine ⟨27007159752068544405699481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36009546336091392540932641 27007159752068544405699481)
              ·
                refine ⟨20255369814051408304274611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27007159752068544405699481 20255369814051408304274611)
                ·
                  refine ⟨30383054721077112456411917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255369814051408304274611 30383054721077112456411917)
                  ·
                    refine ⟨11393645520403917171154469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30383054721077112456411917 11393645520403917171154469)
                    ·
                      refine ⟨2136308535075734469591463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11393645520403917171154469 2136308535075734469591463)
                      ·
                        rfl

theorem cell23_4160446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4160446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160446 prefixEnd_4160446 := by exact prefixLift 4160446
  have htrace : WordTrace (prefixWord ++ tailWord_4160446) baseStart_4160446 baseEnd_4160446 := by
    simpa [prefixWord, tailWord_4160446, baseEnd_4160446] using wordTrace_append hprefix tailTrace_4160446
  have hstable : (prefixWord ++ tailWord_4160446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160446).length < 2 ^ (prefixWord ++ tailWord_4160446).sum := by decide
  have hdescent : baseEnd_4160446 < baseStart_4160446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160463 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_4160463 : Nat := 118140960795 + 4160463 * 2 ^ 59
def prefixEnd_4160463 : Nat := 4983230072969 + 3 ^ 40 * 4160463 * 2
def baseEnd_4160463 : Nat := 2136317264246860903078885

theorem tailTrace_4160463 : CollatzResearch.WordTrace tailWord_4160463 prefixEnd_4160463 2136317264246860903078885 := by
  unfold tailWord_4160463
  simp only [CollatzResearch.WordTrace]
  refine ⟨151744551926360576355694043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101163034617573717570462695 151744551926360576355694043)
  ·
    refine ⟨227616827889540864533541065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151744551926360576355694043 227616827889540864533541065)
    ·
      refine ⟨170712620917155648400155799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227616827889540864533541065 170712620917155648400155799)
      ·
        refine ⟨256068931375733472600233699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170712620917155648400155799 256068931375733472600233699)
        ·
          refine ⟨384103397063600208900350549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256068931375733472600233699 384103397063600208900350549)
          ·
            refine ⟨4501211684339064948050983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 384103397063600208900350549 4501211684339064948050983)
            ·
              refine ⟨6751817526508597422076475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501211684339064948050983 6751817526508597422076475)
              ·
                refine ⟨10127726289762896133114713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6751817526508597422076475 10127726289762896133114713)
                ·
                  refine ⟨7595794717322172099836035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10127726289762896133114713 7595794717322172099836035)
                  ·
                    refine ⟨11393692075983258149754053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7595794717322172099836035 11393692075983258149754053)
                    ·
                      refine ⟨2136317264246860903078885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11393692075983258149754053 2136317264246860903078885)
                      ·
                        rfl

theorem cell23_4160463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_4160463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160463 prefixEnd_4160463 := by exact prefixLift 4160463
  have htrace : WordTrace (prefixWord ++ tailWord_4160463) baseStart_4160463 baseEnd_4160463 := by
    simpa [prefixWord, tailWord_4160463, baseEnd_4160463] using wordTrace_append hprefix tailTrace_4160463
  have hstable : (prefixWord ++ tailWord_4160463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160463).length < 2 ^ (prefixWord ++ tailWord_4160463).sum := by decide
  have hdescent : baseEnd_4160463 < baseStart_4160463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160490 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_4160490 : Nat := 118140960795 + 4160490 * 2 ^ 59
def prefixEnd_4160490 : Nat := 4983230072969 + 3 ^ 40 * 4160490 * 2
def baseEnd_4160490 : Nat := 712110376074844099147087

theorem tailTrace_4160490 : CollatzResearch.WordTrace tailWord_4160490 prefixEnd_4160490 712110376074844099147087 := by
  unfold tailWord_4160490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37936384174315689991731731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101163691131508506644617949 37936384174315689991731731)
  ·
    refine ⟨56904576261473534987597597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37936384174315689991731731 56904576261473534987597597)
    ·
      refine ⟨21339216098052575620349099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56904576261473534987597597 21339216098052575620349099)
      ·
        refine ⟨32008824147078863430523649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21339216098052575620349099 32008824147078863430523649)
        ·
          refine ⟨24006618110309147572892737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32008824147078863430523649 24006618110309147572892737)
          ·
            refine ⟨18004963582731860679669553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24006618110309147572892737 18004963582731860679669553)
            ·
              refine ⟨13503722687048895509752165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18004963582731860679669553 13503722687048895509752165)
              ·
                refine ⟨2531948003821667908078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13503722687048895509752165 2531948003821667908078531)
                ·
                  refine ⟨3797922005732501862117797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2531948003821667908078531 3797922005732501862117797)
                  ·
                    refine ⟨712110376074844099147087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3797922005732501862117797 712110376074844099147087)
                    ·
                      rfl

theorem cell23_4160490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_4160490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160490 prefixEnd_4160490 := by exact prefixLift 4160490
  have htrace : WordTrace (prefixWord ++ tailWord_4160490) baseStart_4160490 baseEnd_4160490 := by
    simpa [prefixWord, tailWord_4160490, baseEnd_4160490] using wordTrace_append hprefix tailTrace_4160490
  have hstable : (prefixWord ++ tailWord_4160490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160490).length < 2 ^ (prefixWord ++ tailWord_4160490).sum := by decide
  have hdescent : baseEnd_4160490 < baseStart_4160490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160523 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 5, 2]
def baseStart_4160523 : Nat := 118140960795 + 4160523 * 2 ^ 59
def prefixEnd_4160523 : Nat := 4983230072969 + 3 ^ 40 * 4160523 * 2
def baseEnd_4160523 : Nat := 2136348073086130668328609

theorem tailTrace_4160523 : CollatzResearch.WordTrace tailWord_4160523 prefixEnd_4160523 2136348073086130668328609 := by
  unfold tailWord_4160523
  simp only [CollatzResearch.WordTrace]
  refine ⟨151746740306143206602878223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101164493537428804401918815 151746740306143206602878223)
  ·
    refine ⟨227620110459214809904317335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151746740306143206602878223 227620110459214809904317335)
    ·
      refine ⟨341430165688822214856476003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227620110459214809904317335 341430165688822214856476003)
      ·
        refine ⟨512145248533233322284714005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341430165688822214856476003 512145248533233322284714005)
        ·
          refine ⟨24006808524995311982095969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 512145248533233322284714005 24006808524995311982095969)
          ·
            refine ⟨18005106393746483986571977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24006808524995311982095969 18005106393746483986571977)
            ·
              refine ⟨13503829795309862989928983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18005106393746483986571977 13503829795309862989928983)
              ·
                refine ⟨20255744692964794484893475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13503829795309862989928983 20255744692964794484893475)
                ·
                  refine ⟨30383617039447191727340213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20255744692964794484893475 30383617039447191727340213)
                  ·
                    refine ⟨2848464097448174224438145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30383617039447191727340213 2848464097448174224438145)
                    ·
                      refine ⟨2136348073086130668328609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848464097448174224438145 2136348073086130668328609)
                      ·
                        rfl

theorem cell23_4160523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5, 2].length) (baseStart_4160523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160523 prefixEnd_4160523 := by exact prefixLift 4160523
  have htrace : WordTrace (prefixWord ++ tailWord_4160523) baseStart_4160523 baseEnd_4160523 := by
    simpa [prefixWord, tailWord_4160523, baseEnd_4160523] using wordTrace_append hprefix tailTrace_4160523
  have hstable : (prefixWord ++ tailWord_4160523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160523).length < 2 ^ (prefixWord ++ tailWord_4160523).sum := by decide
  have hdescent : baseEnd_4160523 < baseStart_4160523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160533 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_4160533 : Nat := 118140960795 + 4160533 * 2 ^ 59
def prefixEnd_4160533 : Nat := 4983230072969 + 3 ^ 40 * 4160533 * 2
def baseEnd_4160533 : Nat := 712117735964225209734521

theorem tailTrace_4160533 : CollatzResearch.WordTrace tailWord_4160533 prefixEnd_4160533 712117735964225209734521 := by
  unfold tailWord_4160533
  simp only [CollatzResearch.WordTrace]
  refine ⟨151747105036106978310742253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101164736690737985540494835 151747105036106978310742253)
  ·
    refine ⟨56905164388540116866528345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151747105036106978310742253 56905164388540116866528345)
    ·
      refine ⟨42678873291405087649896259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56905164388540116866528345 42678873291405087649896259)
      ·
        refine ⟨64018309937107631474844389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42678873291405087649896259 64018309937107631474844389)
        ·
          refine ⟨12003433113207680901533323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64018309937107631474844389 12003433113207680901533323)
          ·
            refine ⟨18005149669811521352299985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003433113207680901533323 18005149669811521352299985)
            ·
              refine ⟨13503862252358641014224989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18005149669811521352299985 13503862252358641014224989)
              ·
                refine ⟨5063948344634490380334371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13503862252358641014224989 5063948344634490380334371)
                ·
                  refine ⟨7595922516951735570501557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5063948344634490380334371 7595922516951735570501557)
                  ·
                    refine ⟨712117735964225209734521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7595922516951735570501557 712117735964225209734521)
                    ·
                      rfl

theorem cell23_4160533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_4160533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160533 prefixEnd_4160533 := by exact prefixLift 4160533
  have htrace : WordTrace (prefixWord ++ tailWord_4160533) baseStart_4160533 baseEnd_4160533 := by
    simpa [prefixWord, tailWord_4160533, baseEnd_4160533] using wordTrace_append hprefix tailTrace_4160533
  have hstable : (prefixWord ++ tailWord_4160533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160533).length < 2 ^ (prefixWord ++ tailWord_4160533).sum := by decide
  have hdescent : baseEnd_4160533 < baseStart_4160533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160556 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_4160556 : Nat := 118140960795 + 4160556 * 2 ^ 59
def prefixEnd_4160556 : Nat := 4983230072969 + 3 ^ 40 * 4160556 * 2
def baseEnd_4160556 : Nat := 2136365017947729039215957

theorem tailTrace_4160556 : CollatzResearch.WordTrace tailWord_4160556 prefixEnd_4160556 2136365017947729039215957 := by
  unfold tailWord_4160556
  simp only [CollatzResearch.WordTrace]
  refine ⟨75873971957511826619414761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101165295943349102159219681 75873971957511826619414761)
  ·
    refine ⟨56905478968133869964561071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75873971957511826619414761 56905478968133869964561071)
    ·
      refine ⟨85358218452200804946841607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56905478968133869964561071 85358218452200804946841607)
      ·
        refine ⟨128037327678301207420262411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85358218452200804946841607 128037327678301207420262411)
        ·
          refine ⟨192055991517451811130393617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128037327678301207420262411 192055991517451811130393617)
          ·
            refine ⟨144041993638088858347795213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192055991517451811130393617 144041993638088858347795213)
            ·
              refine ⟨54015747614283321880423205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144041993638088858347795213 54015747614283321880423205)
              ·
                refine ⟨10127952677678122852579351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54015747614283321880423205 10127952677678122852579351)
                ·
                  refine ⟨15191929016517184278869027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10127952677678122852579351 15191929016517184278869027)
                  ·
                    refine ⟨22787893524775776418303541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15191929016517184278869027 22787893524775776418303541)
                    ·
                      refine ⟨2136365017947729039215957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22787893524775776418303541 2136365017947729039215957)
                      ·
                        rfl

theorem cell23_4160556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_4160556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160556 prefixEnd_4160556 := by exact prefixLift 4160556
  have htrace : WordTrace (prefixWord ++ tailWord_4160556) baseStart_4160556 baseEnd_4160556 := by
    simpa [prefixWord, tailWord_4160556, baseEnd_4160556] using wordTrace_append hprefix tailTrace_4160556
  have hstable : (prefixWord ++ tailWord_4160556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160556).length < 2 ^ (prefixWord ++ tailWord_4160556).sum := by decide
  have hdescent : baseEnd_4160556 < baseStart_4160556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160570 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_4160570 : Nat := 118140960795 + 4160570 * 2 ^ 59
def prefixEnd_4160570 : Nat := 4983230072969 + 3 ^ 40 * 4160570 * 2
def baseEnd_4160570 : Nat := 2136372206676891984440893

theorem tailTrace_4160570 : CollatzResearch.WordTrace tailWord_4160570 prefixEnd_4160570 2136372206676891984440893 := by
  unfold tailWord_4160570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937113634243233407459791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101165636357981955753226109 37937113634243233407459791)
  ·
    refine ⟨56905670451364850111189687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37937113634243233407459791 56905670451364850111189687)
    ·
      refine ⟨85358505677047275166784531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56905670451364850111189687 85358505677047275166784531)
      ·
        refine ⟨128037758515570912750176797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85358505677047275166784531 128037758515570912750176797)
        ·
          refine ⟨48014159443339092281316299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128037758515570912750176797 48014159443339092281316299)
          ·
            refine ⟨72021239165008638421974449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48014159443339092281316299 72021239165008638421974449)
            ·
              refine ⟨54015929373756478816480837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72021239165008638421974449 54015929373756478816480837)
              ·
                refine ⟨10127986757579339778090157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54015929373756478816480837 10127986757579339778090157)
                ·
                  refine ⟨3797995034092252416783809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10127986757579339778090157 3797995034092252416783809)
                  ·
                    refine ⟨2848496275569189312587857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3797995034092252416783809 2848496275569189312587857)
                    ·
                      refine ⟨2136372206676891984440893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848496275569189312587857 2136372206676891984440893)
                      ·
                        rfl

theorem cell23_4160570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_4160570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160570 prefixEnd_4160570 := by exact prefixLift 4160570
  have htrace : WordTrace (prefixWord ++ tailWord_4160570) baseStart_4160570 baseEnd_4160570 := by
    simpa [prefixWord, tailWord_4160570, baseEnd_4160570] using wordTrace_append hprefix tailTrace_4160570
  have hstable : (prefixWord ++ tailWord_4160570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160570).length < 2 ^ (prefixWord ++ tailWord_4160570).sum := by decide
  have hdescent : baseEnd_4160570 < baseStart_4160570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160583 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_4160583 : Nat := 118140960795 + 4160583 * 2 ^ 59
def prefixEnd_4160583 : Nat := 4983230072969 + 3 ^ 40 * 4160583 * 2
def baseEnd_4160583 : Nat := 2136378881925400433578333

theorem tailTrace_4160583 : CollatzResearch.WordTrace tailWord_4160583 prefixEnd_4160583 2136378881925400433578333 := by
  unfold tailWord_4160583
  simp only [CollatzResearch.WordTrace]
  refine ⟨151748928685925836850062403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101165952457283891233374935 151748928685925836850062403)
  ·
    refine ⟨227623393028888755275093605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151748928685925836850062403 227623393028888755275093605)
    ·
      refine ⟨42679386192916641614080051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227623393028888755275093605 42679386192916641614080051)
      ·
        refine ⟨64019079289374962421120077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42679386192916641614080051 64019079289374962421120077)
        ·
          refine ⟨24007154733515610907920029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64019079289374962421120077 24007154733515610907920029)
          ·
            refine ⟨9002683025068354090470011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24007154733515610907920029 9002683025068354090470011)
            ·
              refine ⟨13504024537602531135705017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9002683025068354090470011 13504024537602531135705017)
              ·
                refine ⟨10128018403201898351778763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13504024537602531135705017 10128018403201898351778763)
                ·
                  refine ⟨15192027604802847527668145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128018403201898351778763 15192027604802847527668145)
                  ·
                    refine ⟨11394020703602135645751109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15192027604802847527668145 11394020703602135645751109)
                    ·
                      refine ⟨2136378881925400433578333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11394020703602135645751109 2136378881925400433578333)
                      ·
                        rfl

theorem cell23_4160583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_4160583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160583 prefixEnd_4160583 := by exact prefixLift 4160583
  have htrace : WordTrace (prefixWord ++ tailWord_4160583) baseStart_4160583 baseEnd_4160583 := by
    simpa [prefixWord, tailWord_4160583, baseEnd_4160583] using wordTrace_append hprefix tailTrace_4160583
  have hstable : (prefixWord ++ tailWord_4160583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160583).length < 2 ^ (prefixWord ++ tailWord_4160583).sum := by decide
  have hdescent : baseEnd_4160583 < baseStart_4160583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160604 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_4160604 : Nat := 118140960795 + 4160604 * 2 ^ 59
def prefixEnd_4160604 : Nat := 4983230072969 + 3 ^ 40 * 4160604 * 2
def baseEnd_4160604 : Nat := 2136389665019144851415737

theorem tailTrace_4160604 : CollatzResearch.WordTrace tailWord_4160604 prefixEnd_4160604 2136389665019144851415737 := by
  unfold tailWord_4160604
  simp only [CollatzResearch.WordTrace]
  refine ⟨75874847309424878718288433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101166463079233171624384577 75874847309424878718288433)
  ·
    refine ⟨56906135482068659038716325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75874847309424878718288433 56906135482068659038716325)
    ·
      refine ⟨10669900402887873569759311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56906135482068659038716325 10669900402887873569759311)
      ·
        refine ⟨16004850604331810354638967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669900402887873569759311 16004850604331810354638967)
        ·
          refine ⟨24007275906497715531958451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16004850604331810354638967 24007275906497715531958451)
          ·
            refine ⟨36010913859746573297937677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24007275906497715531958451 36010913859746573297937677)
            ·
              refine ⟨13504092697404964986726629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36010913859746573297937677 13504092697404964986726629)
              ·
                refine ⟨2532017380763430935011243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13504092697404964986726629 2532017380763430935011243)
                ·
                  refine ⟨3798026071145146402516865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532017380763430935011243 3798026071145146402516865)
                  ·
                    refine ⟨2848519553358859801887649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798026071145146402516865 2848519553358859801887649)
                    ·
                      refine ⟨2136389665019144851415737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848519553358859801887649 2136389665019144851415737)
                      ·
                        rfl

theorem cell23_4160604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_4160604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160604 prefixEnd_4160604 := by exact prefixLift 4160604
  have htrace : WordTrace (prefixWord ++ tailWord_4160604) baseStart_4160604 baseEnd_4160604 := by
    simpa [prefixWord, tailWord_4160604, baseEnd_4160604] using wordTrace_append hprefix tailTrace_4160604
  have hstable : (prefixWord ++ tailWord_4160604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160604).length < 2 ^ (prefixWord ++ tailWord_4160604).sum := by decide
  have hdescent : baseEnd_4160604 < baseStart_4160604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160610 : List Nat := [3, 3, 2, 2, 1, 3, 1, 8]
def baseStart_4160610 : Nat := 118140960795 + 4160610 * 2 ^ 59
def prefixEnd_4160610 : Nat := 4983230072969 + 3 ^ 40 * 4160610 * 2
def baseEnd_4160610 : Nat := 79125657255669326960767

theorem tailTrace_4160610 : CollatzResearch.WordTrace tailWord_4160610 prefixEnd_4160610 79125657255669326960767 := by
  unfold tailWord_4160610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937478364207005115323821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101166608971218680307530189 37937478364207005115323821)
  ·
    refine ⟨14226554386577626918246433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37937478364207005115323821 14226554386577626918246433)
    ·
      refine ⟨10669915789933220188684825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14226554386577626918246433 10669915789933220188684825)
      ·
        refine ⟨8002436842449915141513619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10669915789933220188684825 8002436842449915141513619)
        ·
          refine ⟨12003655263674872712270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8002436842449915141513619 12003655263674872712270429)
          ·
            refine ⟨4501370723878077267101411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12003655263674872712270429 4501370723878077267101411)
            ·
              refine ⟨6752056085817115900652117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501370723878077267101411 6752056085817115900652117)
              ·
                refine ⟨79125657255669326960767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6752056085817115900652117 79125657255669326960767)
                ·
                  rfl

theorem cell23_4160610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_4160610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160610 prefixEnd_4160610 := by exact prefixLift 4160610
  have htrace : WordTrace (prefixWord ++ tailWord_4160610) baseStart_4160610 baseEnd_4160610 := by
    simpa [prefixWord, tailWord_4160610, baseEnd_4160610] using wordTrace_append hprefix tailTrace_4160610
  have hstable : (prefixWord ++ tailWord_4160610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160610).length < 2 ^ (prefixWord ++ tailWord_4160610).sum := by decide
  have hdescent : baseEnd_4160610 < baseStart_4160610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160620 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_4160620 : Nat := 118140960795 + 4160620 * 2 ^ 59
def prefixEnd_4160620 : Nat := 4983230072969 + 3 ^ 40 * 4160620 * 2
def baseEnd_4160620 : Nat := 2136397880709616788815663

theorem tailTrace_4160620 : CollatzResearch.WordTrace tailWord_4160620 prefixEnd_4160620 2136397880709616788815663 := by
  unfold tailWord_4160620
  simp only [CollatzResearch.WordTrace]
  refine ⟨75875139093395896084579657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101166852124527861446106209 75875139093395896084579657)
  ·
    refine ⟨56906354320046922063434743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75875139093395896084579657 56906354320046922063434743)
    ·
      refine ⟨85359531480070383095152115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56906354320046922063434743 85359531480070383095152115)
      ·
        refine ⟨128039297220105574642728173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85359531480070383095152115 128039297220105574642728173)
        ·
          refine ⟨48014736457539590491023065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128039297220105574642728173 48014736457539590491023065)
          ·
            refine ⟨36011052343154692868267299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48014736457539590491023065 36011052343154692868267299)
            ·
              refine ⟨54016578514732039302400949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36011052343154692868267299 54016578514732039302400949)
              ·
                refine ⟨5064054235756128684600089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54016578514732039302400949 5064054235756128684600089)
                ·
                  refine ⟨3798040676817096513450067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064054235756128684600089 3798040676817096513450067)
                  ·
                    refine ⟨5697061015225644770175101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798040676817096513450067 5697061015225644770175101)
                    ·
                      refine ⟨2136397880709616788815663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697061015225644770175101 2136397880709616788815663)
                      ·
                        rfl

theorem cell23_4160620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_4160620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160620 prefixEnd_4160620 := by exact prefixLift 4160620
  have htrace : WordTrace (prefixWord ++ tailWord_4160620) baseStart_4160620 baseEnd_4160620 := by
    simpa [prefixWord, tailWord_4160620, baseEnd_4160620] using wordTrace_append hprefix tailTrace_4160620
  have hstable : (prefixWord ++ tailWord_4160620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160620).length < 2 ^ (prefixWord ++ tailWord_4160620).sum := by decide
  have hdescent : baseEnd_4160620 < baseStart_4160620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160636 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_4160636 : Nat := 118140960795 + 4160636 * 2 ^ 59
def prefixEnd_4160636 : Nat := 4983230072969 + 3 ^ 40 * 4160636 * 2
def baseEnd_4160636 : Nat := 712135365466696242071863

theorem tailTrace_4160636 : CollatzResearch.WordTrace tailWord_4160636 prefixEnd_4160636 712135365466696242071863 := by
  unfold tailWord_4160636
  simp only [CollatzResearch.WordTrace]
  refine ⟨75875430877366913450870881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101167241169822551267827841 75875430877366913450870881)
  ·
    refine ⟨56906573158025185088153161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75875430877366913450870881 56906573158025185088153161)
    ·
      refine ⟨42679929868518888816114871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56906573158025185088153161 42679929868518888816114871)
      ·
        refine ⟨64019894802778333224172307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42679929868518888816114871 64019894802778333224172307)
        ·
          refine ⟨96029842204167499836258461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64019894802778333224172307 96029842204167499836258461)
          ·
            refine ⟨36011190826562812438596923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96029842204167499836258461 36011190826562812438596923)
            ·
              refine ⟨54016786239844218657895385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36011190826562812438596923 54016786239844218657895385)
              ·
                refine ⟨40512589679883163993421539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54016786239844218657895385 40512589679883163993421539)
                ·
                  refine ⟨60768884519824745990132309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40512589679883163993421539 60768884519824745990132309)
                  ·
                    refine ⟨712135365466696242071863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60768884519824745990132309 712135365466696242071863)
                    ·
                      rfl

theorem cell23_4160636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_4160636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160636 prefixEnd_4160636 := by exact prefixLift 4160636
  have htrace : WordTrace (prefixWord ++ tailWord_4160636) baseStart_4160636 baseEnd_4160636 := by
    simpa [prefixWord, tailWord_4160636, baseEnd_4160636] using wordTrace_append hprefix tailTrace_4160636
  have hstable : (prefixWord ++ tailWord_4160636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160636).length < 2 ^ (prefixWord ++ tailWord_4160636).sum := by decide
  have hdescent : baseEnd_4160636 < baseStart_4160636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160638 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4160638 : Nat := 118140960795 + 4160638 * 2 ^ 59
def prefixEnd_4160638 : Nat := 4983230072969 + 3 ^ 40 * 4160638 * 2
def baseEnd_4160638 : Nat := 2136407123361397718390581

theorem tailTrace_4160638 : CollatzResearch.WordTrace tailWord_4160638 prefixEnd_4160638 2136407123361397718390581 := by
  unfold tailWord_4160638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18968866837590822655414321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101167289800484387495543045 18968866837590822655414321)
  ·
    refine ⟨14226650128193116991560741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18968866837590822655414321 14226650128193116991560741)
    ·
      refine ⟨2667496899036209435917639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14226650128193116991560741 2667496899036209435917639)
      ·
        refine ⟨4001245348554314153876459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667496899036209435917639 4001245348554314153876459)
        ·
          refine ⟨6001868022831471230814689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001245348554314153876459 6001868022831471230814689)
          ·
            refine ⟨4501401017123603423111017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6001868022831471230814689 4501401017123603423111017)
            ·
              refine ⟨3376050762842702567333263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501401017123603423111017 3376050762842702567333263)
              ·
                refine ⟨5064076144264053850999895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376050762842702567333263 5064076144264053850999895)
                ·
                  refine ⟨7596114216396080776499843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064076144264053850999895 7596114216396080776499843)
                  ·
                    refine ⟨11394171324594121164749765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596114216396080776499843 11394171324594121164749765)
                    ·
                      refine ⟨2136407123361397718390581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11394171324594121164749765 2136407123361397718390581)
                      ·
                        rfl

theorem cell23_4160638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4160638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160638 prefixEnd_4160638 := by exact prefixLift 4160638
  have htrace : WordTrace (prefixWord ++ tailWord_4160638) baseStart_4160638 baseEnd_4160638 := by
    simpa [prefixWord, tailWord_4160638, baseEnd_4160638] using wordTrace_append hprefix tailTrace_4160638
  have hstable : (prefixWord ++ tailWord_4160638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160638).length < 2 ^ (prefixWord ++ tailWord_4160638).sum := by decide
  have hdescent : baseEnd_4160638 < baseStart_4160638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160654 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4160654 : Nat := 118140960795 + 4160654 * 2 ^ 59
def prefixEnd_4160654 : Nat := 4983230072969 + 3 ^ 40 * 4160654 * 2
def baseEnd_4160654 : Nat := 2136415339051869655790507

theorem tailTrace_4160654 : CollatzResearch.WordTrace tailWord_4160654 prefixEnd_4160654 2136415339051869655790507 := by
  unfold tailWord_4160654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18968939783583576996987127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101167678845779077317264677 18968939783583576996987127)
  ·
    refine ⟨28453409675375365495480691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18968939783583576996987127 28453409675375365495480691)
    ·
      refine ⟨42680114513063048243221037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28453409675375365495480691 42680114513063048243221037)
      ·
        refine ⟨16005042942398643091207889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42680114513063048243221037 16005042942398643091207889)
        ·
          refine ⟨12003782206798982318405917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16005042942398643091207889 12003782206798982318405917)
          ·
            refine ⟨4501418327549618369402219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12003782206798982318405917 4501418327549618369402219)
            ·
              refine ⟨6752127491324427554103329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501418327549618369402219 6752127491324427554103329)
              ·
                refine ⟨5064095618493320665577497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6752127491324427554103329 5064095618493320665577497)
                ·
                  refine ⟨3798071713869990499183123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064095618493320665577497 3798071713869990499183123)
                  ·
                    refine ⟨5697107570804985748774685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798071713869990499183123 5697107570804985748774685)
                    ·
                      refine ⟨2136415339051869655790507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697107570804985748774685 2136415339051869655790507)
                      ·
                        rfl

theorem cell23_4160654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4160654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160654 prefixEnd_4160654 := by exact prefixLift 4160654
  have htrace : WordTrace (prefixWord ++ tailWord_4160654) baseStart_4160654 baseEnd_4160654 := by
    simpa [prefixWord, tailWord_4160654, baseEnd_4160654] using wordTrace_append hprefix tailTrace_4160654
  have hstable : (prefixWord ++ tailWord_4160654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160654).length < 2 ^ (prefixWord ++ tailWord_4160654).sum := by decide
  have hdescent : baseEnd_4160654 < baseStart_4160654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160670 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4160670 : Nat := 118140960795 + 4160670 * 2 ^ 59
def prefixEnd_4160670 : Nat := 4983230072969 + 3 ^ 40 * 4160670 * 2
def baseEnd_4160670 : Nat := 712141184914113864396811

theorem tailTrace_4160670 : CollatzResearch.WordTrace tailWord_4160670 prefixEnd_4160670 712141184914113864396811 := by
  unfold tailWord_4160670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969012729576331338559933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101168067891073767138986309 18969012729576331338559933)
  ·
    refine ⟨7113379773591124251959975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18969012729576331338559933 7113379773591124251959975)
    ·
      refine ⟨10670069660386686377939963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7113379773591124251959975 10670069660386686377939963)
      ·
        refine ⟨16005104490580029566909945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10670069660386686377939963 16005104490580029566909945)
        ·
          refine ⟨12003828367935022175182459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16005104490580029566909945 12003828367935022175182459)
          ·
            refine ⟨18005742551902533262773689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12003828367935022175182459 18005742551902533262773689)
            ·
              refine ⟨13504306913926899947080267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18005742551902533262773689 13504306913926899947080267)
              ·
                refine ⟨20256460370890349920620401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13504306913926899947080267 20256460370890349920620401)
                ·
                  refine ⟨15192345278167762440465301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20256460370890349920620401 15192345278167762440465301)
                  ·
                    refine ⟨712141184914113864396811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15192345278167762440465301 712141184914113864396811)
                    ·
                      rfl

theorem cell23_4160670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4160670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160670 prefixEnd_4160670 := by exact prefixLift 4160670
  have htrace : WordTrace (prefixWord ++ tailWord_4160670) baseStart_4160670 baseEnd_4160670 := by
    simpa [prefixWord, tailWord_4160670, baseEnd_4160670] using wordTrace_append hprefix tailTrace_4160670
  have hstable : (prefixWord ++ tailWord_4160670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160670).length < 2 ^ (prefixWord ++ tailWord_4160670).sum := by decide
  have hdescent : baseEnd_4160670 < baseStart_4160670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160673 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4160673 : Nat := 118140960795 + 4160673 * 2 ^ 59
def prefixEnd_4160673 : Nat := 4983230072969 + 3 ^ 40 * 4160673 * 2
def baseEnd_4160673 : Nat := 2136425095184305081452919

theorem tailTrace_4160673 : CollatzResearch.WordTrace tailWord_4160673 prefixEnd_4160673 2136425095184305081452919 := by
  unfold tailWord_4160673
  simp only [CollatzResearch.WordTrace]
  refine ⟨151752211255599782220838673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101168140837066521480559115 151752211255599782220838673)
  ·
    refine ⟨113814158441699836665629005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151752211255599782220838673 113814158441699836665629005)
    ·
      refine ⟨42680309415637438749610877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113814158441699836665629005 42680309415637438749610877)
      ·
        refine ⟨16005116030864039531104079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42680309415637438749610877 16005116030864039531104079)
        ·
          refine ⟨24007674046296059296656119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16005116030864039531104079 24007674046296059296656119)
          ·
            refine ⟨36011511069444088944984179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24007674046296059296656119 36011511069444088944984179)
            ·
              refine ⟨54017266604166133417476269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36011511069444088944984179 54017266604166133417476269)
              ·
                refine ⟨20256474976562300031553601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54017266604166133417476269 20256474976562300031553601)
                ·
                  refine ⟨15192356232421725023665201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20256474976562300031553601 15192356232421725023665201)
                  ·
                    refine ⟨11394267174316293767748901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15192356232421725023665201 11394267174316293767748901)
                    ·
                      refine ⟨2136425095184305081452919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11394267174316293767748901 2136425095184305081452919)
                      ·
                        rfl

theorem cell23_4160673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4160673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160673 prefixEnd_4160673 := by exact prefixLift 4160673
  have htrace : WordTrace (prefixWord ++ tailWord_4160673) baseStart_4160673 baseEnd_4160673 := by
    simpa [prefixWord, tailWord_4160673, baseEnd_4160673] using wordTrace_append hprefix tailTrace_4160673
  have hstable : (prefixWord ++ tailWord_4160673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160673).length < 2 ^ (prefixWord ++ tailWord_4160673).sum := by decide
  have hdescent : baseEnd_4160673 < baseStart_4160673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160677 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_4160677 : Nat := 118140960795 + 4160677 * 2 ^ 59
def prefixEnd_4160677 : Nat := 4983230072969 + 3 ^ 40 * 4160677 * 2
def baseEnd_4160677 : Nat := 2136427149106923065802901

theorem tailTrace_4160677 : CollatzResearch.WordTrace tailWord_4160677 prefixEnd_4160677 2136427149106923065802901 := by
  unfold tailWord_4160677
  simp only [CollatzResearch.WordTrace]
  refine ⟨151752357147585290903984285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101168238098390193935989523 151752357147585290903984285)
  ·
    refine ⟨56907133930344484088994107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151752357147585290903984285 56907133930344484088994107)
    ·
      refine ⟨85360700895516726133491161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56907133930344484088994107 85360700895516726133491161)
      ·
        refine ⟨64020525671637544600118371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85360700895516726133491161 64020525671637544600118371)
        ·
          refine ⟨96030788507456316900177557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64020525671637544600118371 96030788507456316900177557)
          ·
            refine ⟨4501443211287014854695823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96030788507456316900177557 4501443211287014854695823)
            ·
              refine ⟨6752164816930522282043735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501443211287014854695823 6752164816930522282043735)
              ·
                refine ⟨10128247225395783423065603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752164816930522282043735 10128247225395783423065603)
                ·
                  refine ⟨15192370838093675134598405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128247225395783423065603 15192370838093675134598405)
                  ·
                    refine ⟨2848569532142564087737201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15192370838093675134598405 2848569532142564087737201)
                    ·
                      refine ⟨2136427149106923065802901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848569532142564087737201 2136427149106923065802901)
                      ·
                        rfl

theorem cell23_4160677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_4160677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160677 prefixEnd_4160677 := by exact prefixLift 4160677
  have htrace : WordTrace (prefixWord ++ tailWord_4160677) baseStart_4160677 baseEnd_4160677 := by
    simpa [prefixWord, tailWord_4160677, baseEnd_4160677] using wordTrace_append hprefix tailTrace_4160677
  have hstable : (prefixWord ++ tailWord_4160677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160677).length < 2 ^ (prefixWord ++ tailWord_4160677).sum := by decide
  have hdescent : baseEnd_4160677 < baseStart_4160677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160728 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4160728 : Nat := 118140960795 + 4160728 * 2 ^ 59
def prefixEnd_4160728 : Nat := 4983230072969 + 3 ^ 40 * 4160728 * 2
def baseEnd_4160728 : Nat := 2136453336620302366265167

theorem tailTrace_4160728 : CollatzResearch.WordTrace tailWord_4160728 prefixEnd_4160728 2136453336620302366265167 := by
  unfold tailWord_4160728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75877108635200263307045419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101169478180267017742727225 75877108635200263307045419)
  ·
    refine ⟨113815662952800394960568129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75877108635200263307045419 113815662952800394960568129)
    ·
      refine ⟨85361747214600296220426097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113815662952800394960568129 85361747214600296220426097)
      ·
        refine ⟨64021310410950222165319573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85361747214600296220426097 64021310410950222165319573)
        ·
          refine ⟨3000998925513291663999355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64021310410950222165319573 3000998925513291663999355)
          ·
            refine ⟨4501498388269937495999033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000998925513291663999355 4501498388269937495999033)
            ·
              refine ⟨3376123791202453121999275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4501498388269937495999033 3376123791202453121999275)
              ·
                refine ⟨5064185686803679682998913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376123791202453121999275 5064185686803679682998913)
                ·
                  refine ⟨3798139265102759762249185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064185686803679682998913 3798139265102759762249185)
                  ·
                    refine ⟨2848604448827069821686889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798139265102759762249185 2848604448827069821686889)
                    ·
                      refine ⟨2136453336620302366265167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848604448827069821686889 2136453336620302366265167)
                      ·
                        rfl

theorem cell23_4160728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4160728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160728 prefixEnd_4160728 := by exact prefixLift 4160728
  have htrace : WordTrace (prefixWord ++ tailWord_4160728) baseStart_4160728 baseEnd_4160728 := by
    simpa [prefixWord, tailWord_4160728, baseEnd_4160728] using wordTrace_append hprefix tailTrace_4160728
  have hstable : (prefixWord ++ tailWord_4160728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160728).length < 2 ^ (prefixWord ++ tailWord_4160728).sum := by decide
  have hdescent : baseEnd_4160728 < baseStart_4160728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160750 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4160750 : Nat := 118140960795 + 4160750 * 2 ^ 59
def prefixEnd_4160750 : Nat := 4983230072969 + 3 ^ 40 * 4160750 * 2
def baseEnd_4160750 : Nat := 2136464633194701280190065

theorem tailTrace_4160750 : CollatzResearch.WordTrace tailWord_4160750 prefixEnd_4160750 2136464633194701280190065 := by
  unfold tailWord_4160750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969377459540103046423963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101170013117547216247594469 18969377459540103046423963)
  ·
    refine ⟨28454066189310154569635945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18969377459540103046423963 28454066189310154569635945)
    ·
      refine ⟨21340549641982615927226959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28454066189310154569635945 21340549641982615927226959)
      ·
        refine ⟨32010824462973923890840439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21340549641982615927226959 32010824462973923890840439)
        ·
          refine ⟨48016236694460885836260659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32010824462973923890840439 48016236694460885836260659)
          ·
            refine ⟨72024355041691328754390989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48016236694460885836260659 72024355041691328754390989)
            ·
              refine ⟨27009133140634248282896621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72024355041691328754390989 27009133140634248282896621)
              ·
                refine ⟨10128424927737843106086233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27009133140634248282896621 10128424927737843106086233)
                ·
                  refine ⟨7596318695803382329564675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10128424927737843106086233 7596318695803382329564675)
                  ·
                    refine ⟨11394478043705073494347013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7596318695803382329564675 11394478043705073494347013)
                    ·
                      refine ⟨2136464633194701280190065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11394478043705073494347013 2136464633194701280190065)
                      ·
                        rfl

theorem cell23_4160750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4160750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160750 prefixEnd_4160750 := by exact prefixLift 4160750
  have htrace : WordTrace (prefixWord ++ tailWord_4160750) baseStart_4160750 baseEnd_4160750 := by
    simpa [prefixWord, tailWord_4160750, baseEnd_4160750] using wordTrace_append hprefix tailTrace_4160750
  have hstable : (prefixWord ++ tailWord_4160750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160750).length < 2 ^ (prefixWord ++ tailWord_4160750).sum := by decide
  have hdescent : baseEnd_4160750 < baseStart_4160750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160777 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 1, 4]
def baseStart_4160777 : Nat := 118140960795 + 4160777 * 2 ^ 59
def prefixEnd_4160777 : Nat := 4983230072969 + 3 ^ 40 * 4160777 * 2
def baseEnd_4160777 : Nat := 712159499057457558184147

theorem tailTrace_4160777 : CollatzResearch.WordTrace tailWord_4160777 prefixEnd_4160777 712159499057457558184147 := by
  unfold tailWord_4160777
  simp only [CollatzResearch.WordTrace]
  refine ⟨151756004447223007982624585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101170669631482005321749723 151756004447223007982624585)
  ·
    refine ⟨113817003335417255986968439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151756004447223007982624585 113817003335417255986968439)
    ·
      refine ⟨170725505003125883980452659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113817003335417255986968439 170725505003125883980452659)
      ·
        refine ⟨256088257504688825970678989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170725505003125883980452659 256088257504688825970678989)
        ·
          refine ⟨96033096564258309739004621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256088257504688825970678989 96033096564258309739004621)
          ·
            refine ⟨36012411211596866152126733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96033096564258309739004621 36012411211596866152126733)
            ·
              refine ⟨13504654204348824807047525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36012411211596866152126733 13504654204348824807047525)
              ·
                refine ⟨2532122663315404651321411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13504654204348824807047525 2532122663315404651321411)
                ·
                  refine ⟨3798183994973106976982117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532122663315404651321411 3798183994973106976982117)
                  ·
                    refine ⟨712159499057457558184147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3798183994973106976982117 712159499057457558184147)
                    ·
                      rfl

theorem cell23_4160777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_4160777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160777 prefixEnd_4160777 := by exact prefixLift 4160777
  have htrace : WordTrace (prefixWord ++ tailWord_4160777) baseStart_4160777 baseEnd_4160777 := by
    simpa [prefixWord, tailWord_4160777, baseEnd_4160777] using wordTrace_append hprefix tailTrace_4160777
  have hstable : (prefixWord ++ tailWord_4160777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160777).length < 2 ^ (prefixWord ++ tailWord_4160777).sum := by decide
  have hdescent : baseEnd_4160777 < baseStart_4160777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160783 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_4160783 : Nat := 118140960795 + 4160783 * 2 ^ 59
def prefixEnd_4160783 : Nat := 4983230072969 + 3 ^ 40 * 4160783 * 2
def baseEnd_4160783 : Nat := 2136481578056299651077413

theorem tailTrace_4160783 : CollatzResearch.WordTrace tailWord_4160783 prefixEnd_4160783 2136481578056299651077413 := by
  unfold tailWord_4160783
  simp only [CollatzResearch.WordTrace]
  refine ⟨151756223285201271007343003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101170815523467514004895335 151756223285201271007343003)
  ·
    refine ⟨227634334927801906511014505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151756223285201271007343003 227634334927801906511014505)
    ·
      refine ⟨170725751195851429883260879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227634334927801906511014505 170725751195851429883260879)
      ·
        refine ⟨256088626793777144824891319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170725751195851429883260879 256088626793777144824891319)
        ·
          refine ⟨384132940190665717237336979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256088626793777144824891319 384132940190665717237336979)
          ·
            refine ⟨576199410285998575856005469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384132940190665717237336979 576199410285998575856005469)
            ·
              refine ⟨216074778857249465946002051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576199410285998575856005469 216074778857249465946002051)
              ·
                refine ⟨324112168285874198919003077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216074778857249465946002051 324112168285874198919003077)
                ·
                  refine ⟨60771031553601412297313077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324112168285874198919003077 60771031553601412297313077)
                  ·
                    refine ⟨5697284208150132402873101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60771031553601412297313077 5697284208150132402873101)
                    ·
                      refine ⟨2136481578056299651077413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697284208150132402873101 2136481578056299651077413)
                      ·
                        rfl

theorem cell23_4160783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_4160783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160783 prefixEnd_4160783 := by exact prefixLift 4160783
  have htrace : WordTrace (prefixWord ++ tailWord_4160783) baseStart_4160783 baseEnd_4160783 := by
    simpa [prefixWord, tailWord_4160783, baseEnd_4160783] using wordTrace_append hprefix tailTrace_4160783
  have hstable : (prefixWord ++ tailWord_4160783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160783).length < 2 ^ (prefixWord ++ tailWord_4160783).sum := by decide
  have hdescent : baseEnd_4160783 < baseStart_4160783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160877 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4160877 : Nat := 118140960795 + 4160877 * 2 ^ 59
def prefixEnd_4160877 : Nat := 4983230072969 + 3 ^ 40 * 4160877 * 2
def baseEnd_4160877 : Nat := 2136529845237822283301981

theorem tailTrace_4160877 : CollatzResearch.WordTrace tailWord_4160877 prefixEnd_4160877 2136529845237822283301981 := by
  unfold tailWord_4160877
  simp only [CollatzResearch.WordTrace]
  refine ⟨151759651746860725061264885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101173101164573816707509923 151759651746860725061264885)
  ·
    refine ⟨14227467351268192974493583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151759651746860725061264885 14227467351268192974493583)
    ·
      refine ⟨21341201026902289461740375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227467351268192974493583 21341201026902289461740375)
      ·
        refine ⟨32011801540353434192610563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21341201026902289461740375 32011801540353434192610563)
        ·
          refine ⟨48017702310530151288915845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32011801540353434192610563 48017702310530151288915845)
          ·
            refine ⟨9003319183224403366671721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48017702310530151288915845 9003319183224403366671721)
            ·
              refine ⟨6752489387418302525003791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9003319183224403366671721 6752489387418302525003791)
              ·
                refine ⟨10128734081127453787505687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6752489387418302525003791 10128734081127453787505687)
                ·
                  refine ⟨15193101121691180681258531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10128734081127453787505687 15193101121691180681258531)
                  ·
                    refine ⟨22789651682536771021887797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15193101121691180681258531 22789651682536771021887797)
                    ·
                      refine ⟨2136529845237822283301981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22789651682536771021887797 2136529845237822283301981)
                      ·
                        rfl

theorem cell23_4160877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4160877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160877 prefixEnd_4160877 := by exact prefixLift 4160877
  have htrace : WordTrace (prefixWord ++ tailWord_4160877) baseStart_4160877 baseEnd_4160877 := by
    simpa [prefixWord, tailWord_4160877, baseEnd_4160877] using wordTrace_append hprefix tailTrace_4160877
  have hstable : (prefixWord ++ tailWord_4160877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160877).length < 2 ^ (prefixWord ++ tailWord_4160877).sum := by decide
  have hdescent : baseEnd_4160877 < baseStart_4160877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160883 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_4160883 : Nat := 118140960795 + 4160883 * 2 ^ 59
def prefixEnd_4160883 : Nat := 4983230072969 + 3 ^ 40 * 4160883 * 2
def baseEnd_4160883 : Nat := 2136532926121749259826953

theorem tailTrace_4160883 : CollatzResearch.WordTrace tailWord_4160883 prefixEnd_4160883 2136532926121749259826953 := by
  unfold tailWord_4160883
  simp only [CollatzResearch.WordTrace]
  refine ⟨151759870584838988085983303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101173247056559325390655535 151759870584838988085983303)
  ·
    refine ⟨227639805877258482128974955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151759870584838988085983303 227639805877258482128974955)
    ·
      refine ⟨341459708815887723193462433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227639805877258482128974955 341459708815887723193462433)
      ·
        refine ⟨256094781611915792395096825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341459708815887723193462433 256094781611915792395096825)
        ·
          refine ⟨192071086208936844296322619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256094781611915792395096825 192071086208936844296322619)
          ·
            refine ⟨288106629313405266444483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192071086208936844296322619 288106629313405266444483929)
            ·
              refine ⟨216079971985053949833362947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288106629313405266444483929 216079971985053949833362947)
              ·
                refine ⟨324119957977580924750044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216079971985053949833362947 324119957977580924750044421)
                ·
                  refine ⟨60772492120796423390633329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324119957977580924750044421 60772492120796423390633329)
                  ·
                    refine ⟨45579369090597317542974997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60772492120796423390633329 45579369090597317542974997)
                    ·
                      refine ⟨2136532926121749259826953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45579369090597317542974997 2136532926121749259826953)
                      ·
                        rfl

theorem cell23_4160883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_4160883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160883 prefixEnd_4160883 := by exact prefixLift 4160883
  have htrace : WordTrace (prefixWord ++ tailWord_4160883) baseStart_4160883 baseEnd_4160883 := by
    simpa [prefixWord, tailWord_4160883, baseEnd_4160883] using wordTrace_append hprefix tailTrace_4160883
  have hstable : (prefixWord ++ tailWord_4160883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160883).length < 2 ^ (prefixWord ++ tailWord_4160883).sum := by decide
  have hdescent : baseEnd_4160883 < baseStart_4160883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160890 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_4160890 : Nat := 118140960795 + 4160890 * 2 ^ 59
def prefixEnd_4160890 : Nat := 4983230072969 + 3 ^ 40 * 4160890 * 2
def baseEnd_4160890 : Nat := 2136536520486330732439421

theorem tailTrace_4160890 : CollatzResearch.WordTrace tailWord_4160890 prefixEnd_4160890 2136536520486330732439421 := by
  unfold tailWord_4160890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940031473953407070372031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101173417263875752187658749 37940031473953407070372031)
  ·
    refine ⟨56910047210930110605558047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37940031473953407070372031 56910047210930110605558047)
    ·
      refine ⟨85365070816395165908337071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56910047210930110605558047 85365070816395165908337071)
      ·
        refine ⟨128047606224592748862505607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85365070816395165908337071 128047606224592748862505607)
        ·
          refine ⟨192071409336889123293758411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128047606224592748862505607 192071409336889123293758411)
          ·
            refine ⟨288107114005333684940637617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192071409336889123293758411 288107114005333684940637617)
            ·
              refine ⟨216080335504000263705478213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288107114005333684940637617 216080335504000263705478213)
              ·
                refine ⟨40515062907000049444777165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216080335504000263705478213 40515062907000049444777165)
                ·
                  refine ⟨15193148590125018541791437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40515062907000049444777165 15193148590125018541791437)
                  ·
                    refine ⟨5697430721296881953171789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15193148590125018541791437 5697430721296881953171789)
                    ·
                      refine ⟨2136536520486330732439421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697430721296881953171789 2136536520486330732439421)
                      ·
                        rfl

theorem cell23_4160890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_4160890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160890 prefixEnd_4160890 := by exact prefixLift 4160890
  have htrace : WordTrace (prefixWord ++ tailWord_4160890) baseStart_4160890 baseEnd_4160890 := by
    simpa [prefixWord, tailWord_4160890, baseEnd_4160890] using wordTrace_append hprefix tailTrace_4160890
  have hstable : (prefixWord ++ tailWord_4160890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160890).length < 2 ^ (prefixWord ++ tailWord_4160890).sum := by decide
  have hdescent : baseEnd_4160890 < baseStart_4160890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160897 : List Nat := [1, 2, 4, 3, 2, 1, 2, 8]
def baseStart_4160897 : Nat := 118140960795 + 4160897 * 2 ^ 59
def prefixEnd_4160897 : Nat := 4983230072969 + 3 ^ 40 * 4160897 * 2
def baseEnd_4160897 : Nat := 79131115364848600187107

theorem tailTrace_4160897 : CollatzResearch.WordTrace tailWord_4160897 prefixEnd_4160897 79131115364848600187107 := by
  unfold tailWord_4160897
  simp only [CollatzResearch.WordTrace]
  refine ⟨151760381206788268476992945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101173587471192178984661963 151760381206788268476992945)
  ·
    refine ⟨113820285905091201357744709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151760381206788268476992945 113820285905091201357744709)
    ·
      refine ⟨21341303607204600254577133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113820285905091201357744709 21341303607204600254577133)
      ·
        refine ⟨8002988852701725095466425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21341303607204600254577133 8002988852701725095466425)
        ·
          refine ⟨6002241639526293821599819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8002988852701725095466425 6002241639526293821599819)
          ·
            refine ⟨9003362459289440732399729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002241639526293821599819 9003362459289440732399729)
            ·
              refine ⟨6752521844467080549299797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9003362459289440732399729 6752521844467080549299797)
              ·
                refine ⟨79131115364848600187107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6752521844467080549299797 79131115364848600187107)
                ·
                  rfl

theorem cell23_4160897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 8].length) (baseStart_4160897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160897 prefixEnd_4160897 := by exact prefixLift 4160897
  have htrace : WordTrace (prefixWord ++ tailWord_4160897) baseStart_4160897 baseEnd_4160897 := by
    simpa [prefixWord, tailWord_4160897, baseEnd_4160897] using wordTrace_append hprefix tailTrace_4160897
  have hstable : (prefixWord ++ tailWord_4160897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160897).length < 2 ^ (prefixWord ++ tailWord_4160897).sum := by decide
  have hdescent : baseEnd_4160897 < baseStart_4160897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160941 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4160941 : Nat := 118140960795 + 4160941 * 2 ^ 59
def prefixEnd_4160941 : Nat := 4983230072969 + 3 ^ 40 * 4160941 * 2
def baseEnd_4160941 : Nat := 2136562707999710032901687

theorem tailTrace_4160941 : CollatzResearch.WordTrace tailWord_4160941 prefixEnd_4160941 2136562707999710032901687 := by
  unfold tailWord_4160941
  simp only [CollatzResearch.WordTrace]
  refine ⟨151761986018628863991594677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101174657345752575994396451 151761986018628863991594677)
  ·
    refine ⟨14227686189246455999212001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151761986018628863991594677 14227686189246455999212001)
    ·
      refine ⟨10670764641934841999409001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14227686189246455999212001 10670764641934841999409001)
      ·
        refine ⟨8003073481451131499556751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10670764641934841999409001 8003073481451131499556751)
        ·
          refine ⟨12004610222176697249335127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003073481451131499556751 12004610222176697249335127)
          ·
            refine ⟨18006915333265045874002691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004610222176697249335127 18006915333265045874002691)
            ·
              refine ⟨27010372999897568811004037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18006915333265045874002691 27010372999897568811004037)
              ·
                refine ⟨5064444937480794152063257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27010372999897568811004037 5064444937480794152063257)
                ·
                  refine ⟨3798333703110595614047443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064444937480794152063257 3798333703110595614047443)
                  ·
                    refine ⟨5697500554665893421071165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798333703110595614047443 5697500554665893421071165)
                    ·
                      refine ⟨2136562707999710032901687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697500554665893421071165 2136562707999710032901687)
                      ·
                        rfl

theorem cell23_4160941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4160941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160941 prefixEnd_4160941 := by exact prefixLift 4160941
  have htrace : WordTrace (prefixWord ++ tailWord_4160941) baseStart_4160941 baseEnd_4160941 := by
    simpa [prefixWord, tailWord_4160941, baseEnd_4160941] using wordTrace_append hprefix tailTrace_4160941
  have hstable : (prefixWord ++ tailWord_4160941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160941).length < 2 ^ (prefixWord ++ tailWord_4160941).sum := by decide
  have hdescent : baseEnd_4160941 < baseStart_4160941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160960 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_4160960 : Nat := 118140960795 + 4160960 * 2 ^ 59
def prefixEnd_4160960 : Nat := 4983230072969 + 3 ^ 40 * 4160960 * 2
def baseEnd_4160960 : Nat := 2136572464132145458564099

theorem tailTrace_4160960 : CollatzResearch.WordTrace tailWord_4160960 prefixEnd_4160960 2136572464132145458564099 := by
  unfold tailWord_4160960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75881339502780015118268167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101175119337040020157690889 75881339502780015118268167)
  ·
    refine ⟨113822009254170022677402251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75881339502780015118268167 113822009254170022677402251)
    ·
      refine ⟨170733013881255034016103377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113822009254170022677402251 170733013881255034016103377)
      ·
        refine ⟨128049760410941275512077533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170733013881255034016103377 128049760410941275512077533)
        ·
          refine ⟨48018660154102978317029075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128049760410941275512077533 48018660154102978317029075)
          ·
            refine ⟨72027990231154467475543613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48018660154102978317029075 72027990231154467475543613)
            ·
              refine ⟨27010496336682925303328855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72027990231154467475543613 27010496336682925303328855)
              ·
                refine ⟨40515744505024387954993283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27010496336682925303328855 40515744505024387954993283)
                ·
                  refine ⟨60773616757536581932489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40515744505024387954993283 60773616757536581932489925)
                  ·
                    refine ⟨11395053142038109112341861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60773616757536581932489925 11395053142038109112341861)
                    ·
                      refine ⟨2136572464132145458564099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11395053142038109112341861 2136572464132145458564099)
                      ·
                        rfl

theorem cell23_4160960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_4160960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160960 prefixEnd_4160960 := by exact prefixLift 4160960
  have htrace : WordTrace (prefixWord ++ tailWord_4160960) baseStart_4160960 baseEnd_4160960 := by
    simpa [prefixWord, tailWord_4160960, baseEnd_4160960] using wordTrace_append hprefix tailTrace_4160960
  have hstable : (prefixWord ++ tailWord_4160960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160960).length < 2 ^ (prefixWord ++ tailWord_4160960).sum := by decide
  have hdescent : baseEnd_4160960 < baseStart_4160960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4160970 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_4160970 : Nat := 118140960795 + 4160970 * 2 ^ 59
def prefixEnd_4160970 : Nat := 4983230072969 + 3 ^ 40 * 4160970 * 2
def baseEnd_4160970 : Nat := 237397510993187824382117

theorem tailTrace_4160970 : CollatzResearch.WordTrace tailWord_4160970 prefixEnd_4160970 237397510993187824382117 := by
  unfold tailWord_4160970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37940760933880950486100091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101175362490349201296266909 37940760933880950486100091)
  ·
    refine ⟨56911141400821425729150137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37940760933880950486100091 56911141400821425729150137)
    ·
      refine ⟨42683356050616069296862603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56911141400821425729150137 42683356050616069296862603)
      ·
        refine ⟨64025034075924103945293905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42683356050616069296862603 64025034075924103945293905)
        ·
          refine ⟨48018775556943077958970429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64025034075924103945293905 48018775556943077958970429)
          ·
            refine ⟨18007040833853654234613911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48018775556943077958970429 18007040833853654234613911)
            ·
              refine ⟨27010561250780481351920867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18007040833853654234613911 27010561250780481351920867)
              ·
                refine ⟨40515841876170722027881301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27010561250780481351920867 40515841876170722027881301)
                ·
                  refine ⟨237397510993187824382117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40515841876170722027881301 237397510993187824382117)
                  ·
                    rfl

theorem cell23_4160970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_4160970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4160970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4160970 prefixEnd_4160970 := by exact prefixLift 4160970
  have htrace : WordTrace (prefixWord ++ tailWord_4160970) baseStart_4160970 baseEnd_4160970 := by
    simpa [prefixWord, tailWord_4160970, baseEnd_4160970] using wordTrace_append hprefix tailTrace_4160970
  have hstable : (prefixWord ++ tailWord_4160970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4160970).length < 2 ^ (prefixWord ++ tailWord_4160970).sum := by decide
  have hdescent : baseEnd_4160970 < baseStart_4160970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4160970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161007 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 7, 2]
def baseStart_4161007 : Nat := 118140960795 + 4161007 * 2 ^ 59
def prefixEnd_4161007 : Nat := 4983230072969 + 3 ^ 40 * 4161007 * 2
def baseEnd_4161007 : Nat := 2136596597722906774676383

theorem tailTrace_4161007 : CollatzResearch.WordTrace tailWord_4161007 prefixEnd_4161007 2136596597722906774676383 := by
  unfold tailWord_4161007
  simp only [CollatzResearch.WordTrace]
  refine ⟨151764393236389757263497275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101176262157593171508998183 151764393236389757263497275)
  ·
    refine ⟨227646589854584635895245913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151764393236389757263497275 227646589854584635895245913)
    ·
      refine ⟨170734942390938476921434435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227646589854584635895245913 170734942390938476921434435)
      ·
        refine ⟨256102413586407715382151653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170734942390938476921434435 256102413586407715382151653)
        ·
          refine ⟨48019202547451446634153435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256102413586407715382151653 48019202547451446634153435)
          ·
            refine ⟨72028803821177169951230153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48019202547451446634153435 72028803821177169951230153)
            ·
              refine ⟨54021602865882877463422615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72028803821177169951230153 54021602865882877463422615)
              ·
                refine ⟨81032404298824316195133923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54021602865882877463422615 81032404298824316195133923)
                ·
                  refine ⟨121548606448236474292700885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81032404298824316195133923 121548606448236474292700885)
                  ·
                    refine ⟨2848795463630542366235177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121548606448236474292700885 2848795463630542366235177)
                    ·
                      refine ⟨2136596597722906774676383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848795463630542366235177 2136596597722906774676383)
                      ·
                        rfl

theorem cell23_4161007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7, 2].length) (baseStart_4161007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161007 prefixEnd_4161007 := by exact prefixLift 4161007
  have htrace : WordTrace (prefixWord ++ tailWord_4161007) baseStart_4161007 baseEnd_4161007 := by
    simpa [prefixWord, tailWord_4161007, baseEnd_4161007] using wordTrace_append hprefix tailTrace_4161007
  have hstable : (prefixWord ++ tailWord_4161007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161007).length < 2 ^ (prefixWord ++ tailWord_4161007).sum := by decide
  have hdescent : baseEnd_4161007 < baseStart_4161007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161014 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4161014 : Nat := 118140960795 + 4161014 * 2 ^ 59
def prefixEnd_4161014 : Nat := 4983230072969 + 3 ^ 40 * 4161014 * 2
def baseEnd_4161014 : Nat := 2136600192087488247288851

theorem tailTrace_4161014 : CollatzResearch.WordTrace tailWord_4161014 prefixEnd_4161014 2136600192087488247288851 := by
  unfold tailWord_4161014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9485290534210274841187631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101176432364909598306001397 9485290534210274841187631)
  ·
    refine ⟨14227935801315412261781447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9485290534210274841187631 14227935801315412261781447)
    ·
      refine ⟨21341903701973118392672171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227935801315412261781447 21341903701973118392672171)
      ·
        refine ⟨32012855552959677589008257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21341903701973118392672171 32012855552959677589008257)
        ·
          refine ⟨24009641664719758191756193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32012855552959677589008257 24009641664719758191756193)
          ·
            refine ⟨18007231248539818643817145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24009641664719758191756193 18007231248539818643817145)
            ·
              refine ⟨13505423436404863982862859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18007231248539818643817145 13505423436404863982862859)
              ·
                refine ⟨20258135154607295974294289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13505423436404863982862859 20258135154607295974294289)
                ·
                  refine ⟨15193601365955471980720717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20258135154607295974294289 15193601365955471980720717)
                  ·
                    refine ⟨5697600512233301992770269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15193601365955471980720717 5697600512233301992770269)
                    ·
                      refine ⟨2136600192087488247288851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697600512233301992770269 2136600192087488247288851)
                      ·
                        rfl

theorem cell23_4161014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4161014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161014 prefixEnd_4161014 := by exact prefixLift 4161014
  have htrace : WordTrace (prefixWord ++ tailWord_4161014) baseStart_4161014 baseEnd_4161014 := by
    simpa [prefixWord, tailWord_4161014, baseEnd_4161014] using wordTrace_append hprefix tailTrace_4161014
  have hstable : (prefixWord ++ tailWord_4161014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161014).length < 2 ^ (prefixWord ++ tailWord_4161014).sum := by decide
  have hdescent : baseEnd_4161014 < baseStart_4161014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161038 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_4161038 : Nat := 118140960795 + 4161038 * 2 ^ 59
def prefixEnd_4161038 : Nat := 4983230072969 + 3 ^ 40 * 4161038 * 2
def baseEnd_4161038 : Nat := 237401390624799572598749

theorem tailTrace_4161038 : CollatzResearch.WordTrace tailWord_4161038 prefixEnd_4161038 237401390624799572598749 := by
  unfold tailWord_4161038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970690487409681194734471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101177015932851633038583845 18970690487409681194734471)
  ·
    refine ⟨28456035731114521792101707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18970690487409681194734471 28456035731114521792101707)
    ·
      refine ⟨42684053596671782688152561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28456035731114521792101707 42684053596671782688152561)
      ·
        refine ⟨32013040197503837016114421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42684053596671782688152561 32013040197503837016114421)
        ·
          refine ⟨3001222518515984720260727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32013040197503837016114421 3001222518515984720260727)
          ·
            refine ⟨4501833777773977080391091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001222518515984720260727 4501833777773977080391091)
            ·
              refine ⟨6752750666660965620586637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4501833777773977080391091 6752750666660965620586637)
              ·
                refine ⟨2532281499997862107719989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6752750666660965620586637 2532281499997862107719989)
                ·
                  refine ⟨237401390624799572598749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2532281499997862107719989 237401390624799572598749)
                  ·
                    rfl

theorem cell23_4161038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_4161038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161038 prefixEnd_4161038 := by exact prefixLift 4161038
  have htrace : WordTrace (prefixWord ++ tailWord_4161038) baseStart_4161038 baseEnd_4161038 := by
    simpa [prefixWord, tailWord_4161038, baseEnd_4161038] using wordTrace_append hprefix tailTrace_4161038
  have hstable : (prefixWord ++ tailWord_4161038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161038).length < 2 ^ (prefixWord ++ tailWord_4161038).sum := by decide
  have hdescent : baseEnd_4161038 < baseStart_4161038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161161 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 1, 1, 4]
def baseStart_4161161 : Nat := 118140960795 + 4161161 * 2 ^ 59
def prefixEnd_4161161 : Nat := 4983230072969 + 3 ^ 40 * 4161161 * 2
def baseEnd_4161161 : Nat := 2136675673743699172150675

theorem tailTrace_4161161 : CollatzResearch.WordTrace tailWord_4161161 prefixEnd_4161161 2136675673743699172150675 := by
  unfold tailWord_4161161
  simp only [CollatzResearch.WordTrace]
  refine ⟨151770010077831841564603337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101180006718554561043068891 151770010077831841564603337)
  ·
    refine ⟨113827507558373881173452503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151770010077831841564603337 113827507558373881173452503)
    ·
      refine ⟨170741261337560821760178755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113827507558373881173452503 170741261337560821760178755)
      ·
        refine ⟨256111892006341232640268133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170741261337560821760178755 256111892006341232640268133)
        ·
          refine ⟨48020979751188981120050275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256111892006341232640268133 48020979751188981120050275)
          ·
            refine ⟨72031469626783471680075413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48020979751188981120050275 72031469626783471680075413)
            ·
              refine ⟨3376475138755475235003535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72031469626783471680075413 3376475138755475235003535)
              ·
                refine ⟨5064712708133212852505303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376475138755475235003535 5064712708133212852505303)
                ·
                  refine ⟨7597069062199819278757955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5064712708133212852505303 7597069062199819278757955)
                  ·
                    refine ⟨11395603593299728918136933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7597069062199819278757955 11395603593299728918136933)
                    ·
                      refine ⟨2136675673743699172150675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11395603593299728918136933 2136675673743699172150675)
                      ·
                        rfl

theorem cell23_4161161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 1, 1, 4].length) (baseStart_4161161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161161 prefixEnd_4161161 := by exact prefixLift 4161161
  have htrace : WordTrace (prefixWord ++ tailWord_4161161) baseStart_4161161 baseEnd_4161161 := by
    simpa [prefixWord, tailWord_4161161, baseEnd_4161161] using wordTrace_append hprefix tailTrace_4161161
  have hstable : (prefixWord ++ tailWord_4161161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161161).length < 2 ^ (prefixWord ++ tailWord_4161161).sum := by decide
  have hdescent : baseEnd_4161161 < baseStart_4161161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161188 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_4161188 : Nat := 118140960795 + 4161188 * 2 ^ 59
def prefixEnd_4161188 : Nat := 4983230072969 + 3 ^ 40 * 4161188 * 2
def baseEnd_4161188 : Nat := 712229845907123522171017

theorem tailTrace_4161188 : CollatzResearch.WordTrace tailWord_4161188 prefixEnd_4161188 712229845907123522171017 := by
  unfold tailWord_4161188
  simp only [CollatzResearch.WordTrace]
  refine ⟨75885497424367012587918109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101180663232489350117224145 75885497424367012587918109)
  ·
    refine ⟨28457061534137629720469291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75885497424367012587918109 28457061534137629720469291)
    ·
      refine ⟨42685592301206444580703937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28457061534137629720469291 42685592301206444580703937)
      ·
        refine ⟨32014194225904833435527953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42685592301206444580703937 32014194225904833435527953)
        ·
          refine ⟨24010645669428625076645965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32014194225904833435527953 24010645669428625076645965)
          ·
            refine ⟨9003992126035734403742237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24010645669428625076645965 9003992126035734403742237)
            ·
              refine ⟨3376497047263400401403339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9003992126035734403742237 3376497047263400401403339)
              ·
                refine ⟨5064745570895100602105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376497047263400401403339 5064745570895100602105009)
                ·
                  refine ⟨3798559178171325451578757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5064745570895100602105009 3798559178171325451578757)
                  ·
                    refine ⟨712229845907123522171017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3798559178171325451578757 712229845907123522171017)
                    ·
                      rfl

theorem cell23_4161188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_4161188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161188 prefixEnd_4161188 := by exact prefixLift 4161188
  have htrace : WordTrace (prefixWord ++ tailWord_4161188) baseStart_4161188 baseEnd_4161188 := by
    simpa [prefixWord, tailWord_4161188, baseEnd_4161188] using wordTrace_append hprefix tailTrace_4161188
  have hstable : (prefixWord ++ tailWord_4161188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161188).length < 2 ^ (prefixWord ++ tailWord_4161188).sum := by decide
  have hdescent : baseEnd_4161188 < baseStart_4161188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161212 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_4161212 : Nat := 118140960795 + 4161212 * 2 ^ 59
def prefixEnd_4161212 : Nat := 4983230072969 + 3 ^ 40 * 4161212 * 2
def baseEnd_4161212 : Nat := 2136701861257078472612941

theorem tailTrace_4161212 : CollatzResearch.WordTrace tailWord_4161212 prefixEnd_4161212 2136701861257078472612941 := by
  unfold tailWord_4161212
  simp only [CollatzResearch.WordTrace]
  refine ⟨75885935100323538637354945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101181246800431384849806593 75885935100323538637354945)
  ·
    refine ⟨56914451325242653978016209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75885935100323538637354945 56914451325242653978016209)
    ·
      refine ⟨42685838493931990483512157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56914451325242653978016209 42685838493931990483512157)
      ·
        refine ⟨16007189435224496431317059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42685838493931990483512157 16007189435224496431317059)
        ·
          refine ⟨24010784152836744646975589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16007189435224496431317059 24010784152836744646975589)
          ·
            refine ⟨4502022028656889621307923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24010784152836744646975589 4502022028656889621307923)
            ·
              refine ⟨6753033042985334431961885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502022028656889621307923 6753033042985334431961885)
              ·
                refine ⟨2532387391119500411985707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6753033042985334431961885 2532387391119500411985707)
                ·
                  refine ⟨3798581086679250617978561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2532387391119500411985707 3798581086679250617978561)
                  ·
                    refine ⟨2848935815009437963483921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798581086679250617978561 2848935815009437963483921)
                    ·
                      refine ⟨2136701861257078472612941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848935815009437963483921 2136701861257078472612941)
                      ·
                        rfl

theorem cell23_4161212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_4161212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161212 prefixEnd_4161212 := by exact prefixLift 4161212
  have htrace : WordTrace (prefixWord ++ tailWord_4161212) baseStart_4161212 baseEnd_4161212 := by
    simpa [prefixWord, tailWord_4161212, baseEnd_4161212] using wordTrace_append hprefix tailTrace_4161212
  have hstable : (prefixWord ++ tailWord_4161212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161212).length < 2 ^ (prefixWord ++ tailWord_4161212).sum := by decide
  have hdescent : baseEnd_4161212 < baseStart_4161212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161227 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 6]
def baseStart_4161227 : Nat := 118140960795 + 4161227 * 2 ^ 59
def prefixEnd_4161227 : Nat := 4983230072969 + 3 ^ 40 * 4161227 * 2
def baseEnd_4161227 : Nat := 712236521155631971308457

theorem tailTrace_4161227 : CollatzResearch.WordTrace tailWord_4161227 prefixEnd_4161227 712236521155631971308457 := by
  unfold tailWord_4161227
  simp only [CollatzResearch.WordTrace]
  refine ⟨151772417295592734836505935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101181611530395156557670623 151772417295592734836505935)
  ·
    refine ⟨227658625943389102254758903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151772417295592734836505935 227658625943389102254758903)
    ·
      refine ⟨341487938915083653382138355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227658625943389102254758903 341487938915083653382138355)
      ·
        refine ⟨512231908372625480073207533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341487938915083653382138355 512231908372625480073207533)
        ·
          refine ⟨192086965639734555027452825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512231908372625480073207533 192086965639734555027452825)
          ·
            refine ⟨144065224229800916270589619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192086965639734555027452825 144065224229800916270589619)
            ·
              refine ⟨216097836344701374405884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144065224229800916270589619 216097836344701374405884429)
              ·
                refine ⟨81036688629263015402206661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216097836344701374405884429 81036688629263015402206661)
                ·
                  refine ⟨15194379117986815387913749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81036688629263015402206661 15194379117986815387913749)
                  ·
                    refine ⟨712236521155631971308457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15194379117986815387913749 712236521155631971308457)
                    ·
                      rfl

theorem cell23_4161227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_4161227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161227 prefixEnd_4161227 := by exact prefixLift 4161227
  have htrace : WordTrace (prefixWord ++ tailWord_4161227) baseStart_4161227 baseEnd_4161227 := by
    simpa [prefixWord, tailWord_4161227, baseEnd_4161227] using wordTrace_append hprefix tailTrace_4161227
  have hstable : (prefixWord ++ tailWord_4161227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161227).length < 2 ^ (prefixWord ++ tailWord_4161227).sum := by decide
  have hdescent : baseEnd_4161227 < baseStart_4161227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161255 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4161255 : Nat := 118140960795 + 4161255 * 2 ^ 59
def prefixEnd_4161255 : Nat := 4983230072969 + 3 ^ 40 * 4161255 * 2
def baseEnd_4161255 : Nat := 2136723940925221804375243

theorem tailTrace_4161255 : CollatzResearch.WordTrace tailWord_4161255 prefixEnd_4161255 2136723940925221804375243 := by
  unfold tailWord_4161255
  simp only [CollatzResearch.WordTrace]
  refine ⟨151773438539491295618525219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101182292359660863745683479 151773438539491295618525219)
  ·
    refine ⟨227660157809236943427787829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151773438539491295618525219 227660157809236943427787829)
    ·
      refine ⟨21343139794615963446355109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227660157809236943427787829 21343139794615963446355109)
      ·
        refine ⟨4001838711490493146191583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21343139794615963446355109 4001838711490493146191583)
        ·
          refine ⟨6002758067235739719287375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001838711490493146191583 6002758067235739719287375)
          ·
            refine ⟨9004137100853609578931063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002758067235739719287375 9004137100853609578931063)
            ·
              refine ⟨13506205651280414368396595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004137100853609578931063 13506205651280414368396595)
              ·
                refine ⟨20259308476920621552594893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506205651280414368396595 20259308476920621552594893)
                ·
                  refine ⟨7597240678845233082223085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20259308476920621552594893 7597240678845233082223085)
                  ·
                    refine ⟨2848965254566962405833657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7597240678845233082223085 2848965254566962405833657)
                    ·
                      refine ⟨2136723940925221804375243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2848965254566962405833657 2136723940925221804375243)
                      ·
                        rfl

theorem cell23_4161255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4161255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161255 prefixEnd_4161255 := by exact prefixLift 4161255
  have htrace : WordTrace (prefixWord ++ tailWord_4161255) baseStart_4161255 baseEnd_4161255 := by
    simpa [prefixWord, tailWord_4161255, baseEnd_4161255] using wordTrace_append hprefix tailTrace_4161255
  have hstable : (prefixWord ++ tailWord_4161255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161255).length < 2 ^ (prefixWord ++ tailWord_4161255).sum := by decide
  have hdescent : baseEnd_4161255 < baseStart_4161255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161257 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 9]
def baseStart_4161257 : Nat := 118140960795 + 4161257 * 2 ^ 59
def prefixEnd_4161257 : Nat := 4983230072969 + 3 ^ 40 * 4161257 * 2
def baseEnd_4161257 : Nat := 237413885320725644061137

theorem tailTrace_4161257 : CollatzResearch.WordTrace tailWord_4161257 prefixEnd_4161257 237413885320725644061137 := by
  unfold tailWord_4161257
  simp only [CollatzResearch.WordTrace]
  refine ⟨151773511485484049960098025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101182340990322699973398683 151773511485484049960098025)
  ·
    refine ⟨113830133614113037470073519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151773511485484049960098025 113830133614113037470073519)
    ·
      refine ⟨170745200421169556205110279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113830133614113037470073519 170745200421169556205110279)
      ·
        refine ⟨256117800631754334307665419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170745200421169556205110279 256117800631754334307665419)
        ·
          refine ⟨384176700947631501461498129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256117800631754334307665419 384176700947631501461498129)
          ·
            refine ⟨288132525710723626096123597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384176700947631501461498129 288132525710723626096123597)
            ·
              refine ⟨108049697141521359786046349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288132525710723626096123597 108049697141521359786046349)
              ·
                refine ⟨40518636428070509919767381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108049697141521359786046349 40518636428070509919767381)
                ·
                  refine ⟨237413885320725644061137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40518636428070509919767381 237413885320725644061137)
                  ·
                    rfl

theorem cell23_4161257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_4161257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161257 prefixEnd_4161257 := by exact prefixLift 4161257
  have htrace : WordTrace (prefixWord ++ tailWord_4161257) baseStart_4161257 baseEnd_4161257 := by
    simpa [prefixWord, tailWord_4161257, baseEnd_4161257] using wordTrace_append hprefix tailTrace_4161257
  have hstable : (prefixWord ++ tailWord_4161257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161257).length < 2 ^ (prefixWord ++ tailWord_4161257).sum := by decide
  have hdescent : baseEnd_4161257 < baseStart_4161257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161298 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4161298 : Nat := 118140960795 + 4161298 * 2 ^ 59
def prefixEnd_4161298 : Nat := 4983230072969 + 3 ^ 40 * 4161298 * 2
def baseEnd_4161298 : Nat := 2136746020593365136137545

theorem tailTrace_4161298 : CollatzResearch.WordTrace tailWord_4161298 prefixEnd_4161298 2136746020593365136137545 := by
  unfold tailWord_4161298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37943751719583878490585137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101183337918890342641560365 37943751719583878490585137)
  ·
    refine ⟨28457813789687908867938853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37943751719583878490585137 28457813789687908867938853)
    ·
      refine ⟨5335840085566482912738535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28457813789687908867938853 5335840085566482912738535)
      ·
        refine ⟨8003760128349724369107803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335840085566482912738535 8003760128349724369107803)
        ·
          refine ⟨12005640192524586553661705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003760128349724369107803 12005640192524586553661705)
          ·
            refine ⟨9004230144393439915246279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12005640192524586553661705 9004230144393439915246279)
            ·
              refine ⟨13506345216590159872869419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004230144393439915246279 13506345216590159872869419)
              ·
                refine ⟨20259517824885239809304129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506345216590159872869419 20259517824885239809304129)
                ·
                  refine ⟨15194638368663929856978097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20259517824885239809304129 15194638368663929856978097)
                  ·
                    refine ⟨11395978776497947392733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15194638368663929856978097 11395978776497947392733573)
                    ·
                      refine ⟨2136746020593365136137545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11395978776497947392733573 2136746020593365136137545)
                      ·
                        rfl

theorem cell23_4161298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4161298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161298 prefixEnd_4161298 := by exact prefixLift 4161298
  have htrace : WordTrace (prefixWord ++ tailWord_4161298) baseStart_4161298 baseEnd_4161298 := by
    simpa [prefixWord, tailWord_4161298, baseEnd_4161298] using wordTrace_append hprefix tailTrace_4161298
  have hstable : (prefixWord ++ tailWord_4161298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161298).length < 2 ^ (prefixWord ++ tailWord_4161298).sum := by decide
  have hdescent : baseEnd_4161298 < baseStart_4161298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161301 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_4161301 : Nat := 118140960795 + 4161301 * 2 ^ 59
def prefixEnd_4161301 : Nat := 4983230072969 + 3 ^ 40 * 4161301 * 2
def baseEnd_4161301 : Nat := 2136747561035328624400031

theorem tailTrace_4161301 : CollatzResearch.WordTrace tailWord_4161301 prefixEnd_4161301 2136747561035328624400031 := by
  unfold tailWord_4161301
  simp only [CollatzResearch.WordTrace]
  refine ⟨151775116297324645474699757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101183410864883096983133171 151775116297324645474699757)
  ·
    refine ⟨56915668611496742053012409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151775116297324645474699757 56915668611496742053012409)
    ·
      refine ⟨42686751458622556539759307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56915668611496742053012409 42686751458622556539759307)
      ·
        refine ⟨64030127187933834809638961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42686751458622556539759307 64030127187933834809638961)
        ·
          refine ⟨48022595390950376107229221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64030127187933834809638961 48022595390950376107229221)
          ·
            refine ⟨9004236635803195520105479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48022595390950376107229221 9004236635803195520105479)
            ·
              refine ⟨13506354953704793280158219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004236635803195520105479 13506354953704793280158219)
              ·
                refine ⟨20259532430557189920237329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506354953704793280158219 20259532430557189920237329)
                ·
                  refine ⟨15194649322917892440177997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20259532430557189920237329 15194649322917892440177997)
                  ·
                    refine ⟨5697993496094209665066749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15194649322917892440177997 5697993496094209665066749)
                    ·
                      refine ⟨2136747561035328624400031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5697993496094209665066749 2136747561035328624400031)
                      ·
                        rfl

theorem cell23_4161301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_4161301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161301 prefixEnd_4161301 := by exact prefixLift 4161301
  have htrace : WordTrace (prefixWord ++ tailWord_4161301) baseStart_4161301 baseEnd_4161301 := by
    simpa [prefixWord, tailWord_4161301, baseEnd_4161301] using wordTrace_append hprefix tailTrace_4161301
  have hstable : (prefixWord ++ tailWord_4161301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161301).length < 2 ^ (prefixWord ++ tailWord_4161301).sum := by decide
  have hdescent : baseEnd_4161301 < baseStart_4161301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161304 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_4161304 : Nat := 118140960795 + 4161304 * 2 ^ 59
def prefixEnd_4161304 : Nat := 4983230072969 + 3 ^ 40 * 4161304 * 2
def baseEnd_4161304 : Nat := 712249700492430704220839

theorem tailTrace_4161304 : CollatzResearch.WordTrace tailWord_4161304 prefixEnd_4161304 712249700492430704220839 := by
  unfold tailWord_4161304
  simp only [CollatzResearch.WordTrace]
  refine ⟨75887612858156888493529483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101183483810875851324705977 75887612858156888493529483)
  ·
    refine ⟨113831419287235332740294225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75887612858156888493529483 113831419287235332740294225)
    ·
      refine ⟨85373564465426499555220669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113831419287235332740294225 85373564465426499555220669)
      ·
        refine ⟨32015086674534937333207751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85373564465426499555220669 32015086674534937333207751)
        ·
          refine ⟨48022630011802405999811627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32015086674534937333207751 48022630011802405999811627)
          ·
            refine ⟨72033945017703608999717441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48022630011802405999811627 72033945017703608999717441)
            ·
              refine ⟨54025458763277706749788081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72033945017703608999717441 54025458763277706749788081)
              ·
                refine ⟨40519094072458280062341061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54025458763277706749788081 40519094072458280062341061)
                ·
                  refine ⟨7597330138585927511688949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40519094072458280062341061 7597330138585927511688949)
                  ·
                    refine ⟨712249700492430704220839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7597330138585927511688949 712249700492430704220839)
                    ·
                      rfl

theorem cell23_4161304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_4161304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161304 prefixEnd_4161304 := by exact prefixLift 4161304
  have htrace : WordTrace (prefixWord ++ tailWord_4161304) baseStart_4161304 baseEnd_4161304 := by
    simpa [prefixWord, tailWord_4161304, baseEnd_4161304] using wordTrace_append hprefix tailTrace_4161304
  have hstable : (prefixWord ++ tailWord_4161304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161304).length < 2 ^ (prefixWord ++ tailWord_4161304).sum := by decide
  have hdescent : baseEnd_4161304 < baseStart_4161304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161311 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 5, 2]
def baseStart_4161311 : Nat := 118140960795 + 4161311 * 2 ^ 59
def prefixEnd_4161311 : Nat := 4983230072969 + 3 ^ 40 * 4161311 * 2
def baseEnd_4161311 : Nat := 2136752695841873585274985

theorem tailTrace_4161311 : CollatzResearch.WordTrace tailWord_4161311 prefixEnd_4161311 2136752695841873585274985 := by
  unfold tailWord_4161311
  simp only [CollatzResearch.WordTrace]
  refine ⟨151775481027288417182563787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101183654018192278121709191 151775481027288417182563787)
  ·
    refine ⟨227663221540932625773845681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151775481027288417182563787 227663221540932625773845681)
    ·
      refine ⟨170747416155699469330384261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227663221540932625773845681 170747416155699469330384261)
      ·
        refine ⟨32015140529193650499447049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170747416155699469330384261 32015140529193650499447049)
        ·
          refine ⟨24011355396895237874585287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32015140529193650499447049 24011355396895237874585287)
          ·
            refine ⟨36017033095342856811877931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24011355396895237874585287 36017033095342856811877931)
            ·
              refine ⟨54025549643014285217816897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36017033095342856811877931 54025549643014285217816897)
              ·
                refine ⟨40519162232260713913362673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54025549643014285217816897 40519162232260713913362673)
                ·
                  refine ⟨30389371674195535435022005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40519162232260713913362673 30389371674195535435022005)
                  ·
                    refine ⟨2849003594455831447033313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30389371674195535435022005 2849003594455831447033313)
                    ·
                      refine ⟨2136752695841873585274985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849003594455831447033313 2136752695841873585274985)
                      ·
                        rfl

theorem cell23_4161311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_4161311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161311 prefixEnd_4161311 := by exact prefixLift 4161311
  have htrace : WordTrace (prefixWord ++ tailWord_4161311) baseStart_4161311 baseEnd_4161311 := by
    simpa [prefixWord, tailWord_4161311, baseEnd_4161311] using wordTrace_append hprefix tailTrace_4161311
  have hstable : (prefixWord ++ tailWord_4161311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161311).length < 2 ^ (prefixWord ++ tailWord_4161311).sum := by decide
  have hdescent : baseEnd_4161311 < baseStart_4161311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161351 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 3, 4]
def baseStart_4161351 : Nat := 118140960795 + 4161351 * 2 ^ 59
def prefixEnd_4161351 : Nat := 4983230072969 + 3 ^ 40 * 4161351 * 2
def baseEnd_4161351 : Nat := 712257745022684476258267

theorem tailTrace_4161351 : CollatzResearch.WordTrace tailWord_4161351 prefixEnd_4161351 712257745022684476258267 := by
  unfold tailWord_4161351
  simp only [CollatzResearch.WordTrace]
  refine ⟨151776939947143504014019907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101184626631429002676013271 151776939947143504014019907)
  ·
    refine ⟨227665409920715256021029861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151776939947143504014019907 227665409920715256021029861)
    ·
      refine ⟨42687264360134110503943099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227665409920715256021029861 42687264360134110503943099)
      ·
        refine ⟨64030896540201165755914649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42687264360134110503943099 64030896540201165755914649)
        ·
          refine ⟨48023172405150874316935987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64030896540201165755914649 48023172405150874316935987)
          ·
            refine ⟨72034758607726311475403981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48023172405150874316935987 72034758607726311475403981)
            ·
              refine ⟨27013034477897366803276493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72034758607726311475403981 27013034477897366803276493)
              ·
                refine ⟨10129887929211512551228685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27013034477897366803276493 10129887929211512551228685)
                ·
                  refine ⟨3798707973454317206710757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10129887929211512551228685 3798707973454317206710757)
                  ·
                    refine ⟨712257745022684476258267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3798707973454317206710757 712257745022684476258267)
                    ·
                      rfl

theorem cell23_4161351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_4161351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161351 prefixEnd_4161351 := by exact prefixLift 4161351
  have htrace : WordTrace (prefixWord ++ tailWord_4161351) baseStart_4161351 baseEnd_4161351 := by
    simpa [prefixWord, tailWord_4161351, baseEnd_4161351] using wordTrace_append hprefix tailTrace_4161351
  have hstable : (prefixWord ++ tailWord_4161351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161351).length < 2 ^ (prefixWord ++ tailWord_4161351).sum := by decide
  have hdescent : baseEnd_4161351 < baseStart_4161351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161354 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4161354 : Nat := 118140960795 + 4161354 * 2 ^ 59
def prefixEnd_4161354 : Nat := 4983230072969 + 3 ^ 40 * 4161354 * 2
def baseEnd_4161354 : Nat := 2136774775510016917037287

theorem tailTrace_4161354 : CollatzResearch.WordTrace tailWord_4161354 prefixEnd_4161354 2136774775510016917037287 := by
  unfold tailWord_4161354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37944262341533158881594779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101184699577421757017586077 37944262341533158881594779)
  ·
    refine ⟨56916393512299738322392169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37944262341533158881594779 56916393512299738322392169)
    ·
      refine ⟨42687295134224803741794127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56916393512299738322392169 42687295134224803741794127)
      ·
        refine ⟨64030942701337205612691191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42687295134224803741794127 64030942701337205612691191)
        ·
          refine ⟨96046414052005808419036787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64030942701337205612691191 96046414052005808419036787)
          ·
            refine ⟨144069621078008712628555181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96046414052005808419036787 144069621078008712628555181)
            ·
              refine ⟨54026107904253267235708193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144069621078008712628555181 54026107904253267235708193)
              ·
                refine ⟨40519580928189950426781145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54026107904253267235708193 40519580928189950426781145)
                ·
                  refine ⟨30389685696142462820085859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40519580928189950426781145 30389685696142462820085859)
                  ·
                    refine ⟨45584528544213694230128789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30389685696142462820085859 45584528544213694230128789)
                    ·
                      refine ⟨2136774775510016917037287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45584528544213694230128789 2136774775510016917037287)
                      ·
                        rfl

theorem cell23_4161354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4161354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161354 prefixEnd_4161354 := by exact prefixLift 4161354
  have htrace : WordTrace (prefixWord ++ tailWord_4161354) baseStart_4161354 baseEnd_4161354 := by
    simpa [prefixWord, tailWord_4161354, baseEnd_4161354] using wordTrace_append hprefix tailTrace_4161354
  have hstable : (prefixWord ++ tailWord_4161354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161354).length < 2 ^ (prefixWord ++ tailWord_4161354).sum := by decide
  have hdescent : baseEnd_4161354 < baseStart_4161354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161361 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_4161361 : Nat := 118140960795 + 4161361 * 2 ^ 59
def prefixEnd_4161361 : Nat := 4983230072969 + 3 ^ 40 * 4161361 * 2
def baseEnd_4161361 : Nat := 2136778369874598389649755

theorem tailTrace_4161361 : CollatzResearch.WordTrace tailWord_4161361 prefixEnd_4161361 2136778369874598389649755 := by
  unfold tailWord_4161361
  simp only [CollatzResearch.WordTrace]
  refine ⟨151777304677107275721883937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101184869784738183814589291 151777304677107275721883937)
  ·
    refine ⟨113832978507830456791412953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151777304677107275721883937 113832978507830456791412953)
    ·
      refine ⟨85374733880872842593559715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113832978507830456791412953 85374733880872842593559715)
      ·
        refine ⟨128062100821309263890339573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85374733880872842593559715 128062100821309263890339573)
        ·
          refine ⟨12005821951997743489719335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128062100821309263890339573 12005821951997743489719335)
          ·
            refine ⟨18008732927996615234579003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005821951997743489719335 18008732927996615234579003)
            ·
              refine ⟨27013099391994922851868505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18008732927996615234579003 27013099391994922851868505)
              ·
                refine ⟨20259824543996192138901379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27013099391994922851868505 20259824543996192138901379)
                ·
                  refine ⟨30389736815994288208352069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20259824543996192138901379 30389736815994288208352069)
                  ·
                    refine ⟨5698075652998929039066013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30389736815994288208352069 5698075652998929039066013)
                    ·
                      refine ⟨2136778369874598389649755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698075652998929039066013 2136778369874598389649755)
                      ·
                        rfl

theorem cell23_4161361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_4161361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161361 prefixEnd_4161361 := by exact prefixLift 4161361
  have htrace : WordTrace (prefixWord ++ tailWord_4161361) baseStart_4161361 baseEnd_4161361 := by
    simpa [prefixWord, tailWord_4161361, baseEnd_4161361] using wordTrace_append hprefix tailTrace_4161361
  have hstable : (prefixWord ++ tailWord_4161361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161361).length < 2 ^ (prefixWord ++ tailWord_4161361).sum := by decide
  have hdescent : baseEnd_4161361 < baseStart_4161361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161378 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4161378 : Nat := 118140960795 + 4161378 * 2 ^ 59
def prefixEnd_4161378 : Nat := 4983230072969 + 3 ^ 40 * 4161378 * 2
def baseEnd_4161378 : Nat := 2136787099045724823137177

theorem tailTrace_4161378 : CollatzResearch.WordTrace tailWord_4161378 prefixEnd_4161378 2136787099045724823137177 := by
  unfold tailWord_4161378
  simp only [CollatzResearch.WordTrace]
  refine ⟨37944481179511421906313197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101185283145363791750168525 37944481179511421906313197)
  ·
    refine ⟨14229180442316783214867449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37944481179511421906313197 14229180442316783214867449)
    ·
      refine ⟨10671885331737587411150587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229180442316783214867449 10671885331737587411150587)
      ·
        refine ⟨16007827997606381116725881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10671885331737587411150587 16007827997606381116725881)
        ·
          refine ⟨12005870998204785837544411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16007827997606381116725881 12005870998204785837544411)
          ·
            refine ⟨18008806497307178756316617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12005870998204785837544411 18008806497307178756316617)
            ·
              refine ⟨13506604872980384067237463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18008806497307178756316617 13506604872980384067237463)
              ·
                refine ⟨20259907309470576100856195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506604872980384067237463 20259907309470576100856195)
                ·
                  refine ⟨30389860964205864151284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20259907309470576100856195 30389860964205864151284293)
                  ·
                    refine ⟨5698098930788599528365805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30389860964205864151284293 5698098930788599528365805)
                    ·
                      refine ⟨2136787099045724823137177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698098930788599528365805 2136787099045724823137177)
                      ·
                        rfl

theorem cell23_4161378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4161378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161378 prefixEnd_4161378 := by exact prefixLift 4161378
  have htrace : WordTrace (prefixWord ++ tailWord_4161378) baseStart_4161378 baseEnd_4161378 := by
    simpa [prefixWord, tailWord_4161378, baseEnd_4161378] using wordTrace_append hprefix tailTrace_4161378
  have hstable : (prefixWord ++ tailWord_4161378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161378).length < 2 ^ (prefixWord ++ tailWord_4161378).sum := by decide
  have hdescent : baseEnd_4161378 < baseStart_4161378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161404 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_4161404 : Nat := 118140960795 + 4161404 * 2 ^ 59
def prefixEnd_4161404 : Nat := 4983230072969 + 3 ^ 40 * 4161404 * 2
def baseEnd_4161404 : Nat := 2136800449542741721412057

theorem tailTrace_4161404 : CollatzResearch.WordTrace tailWord_4161404 prefixEnd_4161404 2136800449542741721412057 := by
  unfold tailWord_4161404
  simp only [CollatzResearch.WordTrace]
  refine ⟨75889436507975747032849633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101185915343967662710466177 75889436507975747032849633)
  ·
    refine ⟨56917077380981810274637225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75889436507975747032849633 56917077380981810274637225)
    ·
      refine ⟨42687808035736357705977919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56917077380981810274637225 42687808035736357705977919)
      ·
        refine ⟨64031712053604536558966879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42687808035736357705977919 64031712053604536558966879)
        ·
          refine ⟨96047568080406804838450319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64031712053604536558966879 96047568080406804838450319)
          ·
            refine ⟨144071352120610207257675479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96047568080406804838450319 144071352120610207257675479)
            ·
              refine ⟨216107028180915310886513219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144071352120610207257675479 216107028180915310886513219)
              ·
                refine ⟨324160542271372966329769829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216107028180915310886513219 324160542271372966329769829)
                ·
                  refine ⟨60780101675882431186831843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324160542271372966329769829 60780101675882431186831843)
                  ·
                    refine ⟨91170152513823646780247765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60780101675882431186831843 91170152513823646780247765)
                    ·
                      refine ⟨2136800449542741721412057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91170152513823646780247765 2136800449542741721412057)
                      ·
                        rfl

theorem cell23_4161404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_4161404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161404 prefixEnd_4161404 := by exact prefixLift 4161404
  have htrace : WordTrace (prefixWord ++ tailWord_4161404) baseStart_4161404 baseEnd_4161404 := by
    simpa [prefixWord, tailWord_4161404, baseEnd_4161404] using wordTrace_append hprefix tailTrace_4161404
  have hstable : (prefixWord ++ tailWord_4161404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161404).length < 2 ^ (prefixWord ++ tailWord_4161404).sum := by decide
  have hdescent : baseEnd_4161404 < baseStart_4161404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161415 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 6]
def baseStart_4161415 : Nat := 118140960795 + 4161415 * 2 ^ 59
def prefixEnd_4161415 : Nat := 4983230072969 + 3 ^ 40 * 4161415 * 2
def baseEnd_4161415 : Nat := 237422899758882353152723

theorem tailTrace_4161415 : CollatzResearch.WordTrace tailWord_4161415 prefixEnd_4161415 237422899758882353152723 := by
  unfold tailWord_4161415
  simp only [CollatzResearch.WordTrace]
  refine ⟨151779274218911642944349699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101186182812607761962899799 151779274218911642944349699)
  ·
    refine ⟨227668911328367464416524549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151779274218911642944349699 227668911328367464416524549)
    ·
      refine ⟨42687920874068899578098353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227668911328367464416524549 42687920874068899578098353)
      ·
        refine ⟨32015940655551674683573765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42687920874068899578098353 32015940655551674683573765)
        ·
          refine ⟨6002988872915939003170081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32015940655551674683573765 6002988872915939003170081)
          ·
            refine ⟨4502241654686954252377561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6002988872915939003170081 4502241654686954252377561)
            ·
              refine ⟨3376681241015215689283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502241654686954252377561 3376681241015215689283171)
              ·
                refine ⟨5065021861522823533924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376681241015215689283171 5065021861522823533924757)
                ·
                  refine ⟨237422899758882353152723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5065021861522823533924757 237422899758882353152723)
                  ·
                    rfl

theorem cell23_4161415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 6].length) (baseStart_4161415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161415 prefixEnd_4161415 := by exact prefixLift 4161415
  have htrace : WordTrace (prefixWord ++ tailWord_4161415) baseStart_4161415 baseEnd_4161415 := by
    simpa [prefixWord, tailWord_4161415, baseEnd_4161415] using wordTrace_append hprefix tailTrace_4161415
  have hstable : (prefixWord ++ tailWord_4161415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161415).length < 2 ^ (prefixWord ++ tailWord_4161415).sum := by decide
  have hdescent : baseEnd_4161415 < baseStart_4161415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161428 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4161428 : Nat := 118140960795 + 4161428 * 2 ^ 59
def prefixEnd_4161428 : Nat := 4983230072969 + 3 ^ 40 * 4161428 * 2
def baseEnd_4161428 : Nat := 712270924359483209170649

theorem tailTrace_4161428 : CollatzResearch.WordTrace tailWord_4161428 prefixEnd_4161428 712270924359483209170649 := by
  unfold tailWord_4161428
  simp only [CollatzResearch.WordTrace]
  refine ⟨75889874183932273082286469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101186498911909697443048625 75889874183932273082286469)
  ·
    refine ⟨14229351409487301202928713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75889874183932273082286469 14229351409487301202928713)
    ·
      refine ⟨10672013557115475902196535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14229351409487301202928713 10672013557115475902196535)
      ·
        refine ⟨16008020335673213853294803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672013557115475902196535 16008020335673213853294803)
        ·
          refine ⟨24012030503509820779942205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008020335673213853294803 24012030503509820779942205)
          ·
            refine ⟨9004511438816182792478327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24012030503509820779942205 9004511438816182792478327)
            ·
              refine ⟨13506767158224274188717491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004511438816182792478327 13506767158224274188717491)
              ·
                refine ⟨20260150737336411283076237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13506767158224274188717491 20260150737336411283076237)
                ·
                  refine ⟨7597556526501154231153589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20260150737336411283076237 7597556526501154231153589)
                  ·
                    refine ⟨712270924359483209170649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7597556526501154231153589 712270924359483209170649)
                    ·
                      rfl

theorem cell23_4161428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4161428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161428 prefixEnd_4161428 := by exact prefixLift 4161428
  have htrace : WordTrace (prefixWord ++ tailWord_4161428) baseStart_4161428 baseEnd_4161428 := by
    simpa [prefixWord, tailWord_4161428, baseEnd_4161428] using wordTrace_append hprefix tailTrace_4161428
  have hstable : (prefixWord ++ tailWord_4161428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161428).length < 2 ^ (prefixWord ++ tailWord_4161428).sum := by decide
  have hdescent : baseEnd_4161428 < baseStart_4161428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161451 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3]
def baseStart_4161451 : Nat := 118140960795 + 4161451 * 2 ^ 59
def prefixEnd_4161451 : Nat := 4983230072969 + 3 ^ 40 * 4161451 * 2
def baseEnd_4161451 : Nat := 2136824583133503037524341

theorem tailTrace_4161451 : CollatzResearch.WordTrace tailWord_4161451 prefixEnd_4161451 2136824583133503037524341 := by
  unfold tailWord_4161451
  simp only [CollatzResearch.WordTrace]
  refine ⟨151780587246781221092660207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187058164520814061773471 151780587246781221092660207)
  ·
    refine ⟨227670880870171831638990311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151780587246781221092660207 227670880870171831638990311)
    ·
      refine ⟨341506321305257747458485467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227670880870171831638990311 341506321305257747458485467)
      ·
        refine ⟨512259481957886621187728201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341506321305257747458485467 512259481957886621187728201)
        ·
          refine ⟨384194611468414965890796151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512259481957886621187728201 384194611468414965890796151)
          ·
            refine ⟨576291917202622448836194227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384194611468414965890796151 576291917202622448836194227)
            ·
              refine ⟨864437875803933673254291341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576291917202622448836194227 864437875803933673254291341)
              ·
                refine ⟨324164203426475127470359253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864437875803933673254291341 324164203426475127470359253)
                ·
                  refine ⟨7597598517808010800086545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 324164203426475127470359253 7597598517808010800086545)
                  ·
                    refine ⟨5698198888356008100064909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7597598517808010800086545 5698198888356008100064909)
                    ·
                      refine ⟨2136824583133503037524341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698198888356008100064909 2136824583133503037524341)
                      ·
                        rfl

theorem cell23_4161451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 3].length) (baseStart_4161451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161451 prefixEnd_4161451 := by exact prefixLift 4161451
  have htrace : WordTrace (prefixWord ++ tailWord_4161451) baseStart_4161451 baseEnd_4161451 := by
    simpa [prefixWord, tailWord_4161451, baseEnd_4161451] using wordTrace_append hprefix tailTrace_4161451
  have hstable : (prefixWord ++ tailWord_4161451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161451).length < 2 ^ (prefixWord ++ tailWord_4161451).sum := by decide
  have hdescent : baseEnd_4161451 < baseStart_4161451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161465 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4161465 : Nat := 118140960795 + 4161465 * 2 ^ 59
def prefixEnd_4161465 : Nat := 4983230072969 + 3 ^ 40 * 4161465 * 2
def baseEnd_4161465 : Nat := 2136831771862665982749277

theorem tailTrace_4161465 : CollatzResearch.WordTrace tailWord_4161465 prefixEnd_4161465 2136831771862665982749277 := by
  unfold tailWord_4161465
  simp only [CollatzResearch.WordTrace]
  refine ⟨151781097868730501483669849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187398579153667655779899 151781097868730501483669849)
  ·
    refine ⟨113835823401547876112752387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151781097868730501483669849 113835823401547876112752387)
    ·
      refine ⟨170753735102321814169128581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113835823401547876112752387 170753735102321814169128581)
      ·
        refine ⟨32016325331685340156711609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170753735102321814169128581 32016325331685340156711609)
        ·
          refine ⟨24012243998764005117533707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32016325331685340156711609 24012243998764005117533707)
          ·
            refine ⟨36018365998146007676300561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24012243998764005117533707 36018365998146007676300561)
            ·
              refine ⟨27013774498609505757225421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36018365998146007676300561 27013774498609505757225421)
              ·
                refine ⟨10130165436978564658959533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27013774498609505757225421 10130165436978564658959533)
                ·
                  refine ⟨3798812038866961747109825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10130165436978564658959533 3798812038866961747109825)
                  ·
                    refine ⟨2849109029150221310332369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798812038866961747109825 2849109029150221310332369)
                    ·
                      refine ⟨2136831771862665982749277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849109029150221310332369 2136831771862665982749277)
                      ·
                        rfl

theorem cell23_4161465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4161465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161465 prefixEnd_4161465 := by exact prefixLift 4161465
  have htrace : WordTrace (prefixWord ++ tailWord_4161465) baseStart_4161465 baseEnd_4161465 := by
    simpa [prefixWord, tailWord_4161465, baseEnd_4161465] using wordTrace_append hprefix tailTrace_4161465
  have hstable : (prefixWord ++ tailWord_4161465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161465).length < 2 ^ (prefixWord ++ tailWord_4161465).sum := by decide
  have hdescent : baseEnd_4161465 < baseStart_4161465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161481 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_4161481 : Nat := 118140960795 + 4161481 * 2 ^ 59
def prefixEnd_4161481 : Nat := 4983230072969 + 3 ^ 40 * 4161481 * 2
def baseEnd_4161481 : Nat := 2136839987553137920149203

theorem tailTrace_4161481 : CollatzResearch.WordTrace tailWord_4161481 prefixEnd_4161481 2136839987553137920149203 := by
  unfold tailWord_4161481
  simp only [CollatzResearch.WordTrace]
  refine ⟨151781681436672536216252297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101187787624448357477501531 151781681436672536216252297)
  ·
    refine ⟨113836261077504402162189223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151781681436672536216252297 113836261077504402162189223)
    ·
      refine ⟨170754391616256603243283835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113836261077504402162189223 170754391616256603243283835)
      ·
        refine ⟨256131587424384904864925753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170754391616256603243283835 256131587424384904864925753)
        ·
          refine ⟨192098690568288678648694315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256131587424384904864925753 192098690568288678648694315)
          ·
            refine ⟨288148035852433017973041473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192098690568288678648694315 288148035852433017973041473)
            ·
              refine ⟨216111026889324763479781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288148035852433017973041473 216111026889324763479781105)
              ·
                refine ⟨162083270166993572609835829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216111026889324763479781105 162083270166993572609835829)
                ·
                  refine ⟨15195306578155647432172109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162083270166993572609835829 15195306578155647432172109)
                  ·
                    refine ⟨5698239966808367787064541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15195306578155647432172109 5698239966808367787064541)
                    ·
                      refine ⟨2136839987553137920149203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698239966808367787064541 2136839987553137920149203)
                      ·
                        rfl

theorem cell23_4161481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_4161481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161481 prefixEnd_4161481 := by exact prefixLift 4161481
  have htrace : WordTrace (prefixWord ++ tailWord_4161481) baseStart_4161481 baseEnd_4161481 := by
    simpa [prefixWord, tailWord_4161481, baseEnd_4161481] using wordTrace_append hprefix tailTrace_4161481
  have hstable : (prefixWord ++ tailWord_4161481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161481).length < 2 ^ (prefixWord ++ tailWord_4161481).sum := by decide
  have hdescent : baseEnd_4161481 < baseStart_4161481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161531 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 6]
def baseStart_4161531 : Nat := 118140960795 + 4161531 * 2 ^ 59
def prefixEnd_4161531 : Nat := 4983230072969 + 3 ^ 40 * 4161531 * 2
def baseEnd_4161531 : Nat := 712288553861954241507991

theorem tailTrace_4161531 : CollatzResearch.WordTrace tailWord_4161531 prefixEnd_4161531 712288553861954241507991 := by
  unfold tailWord_4161531
  simp only [CollatzResearch.WordTrace]
  refine ⟨151783505086491394755572447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101189003390994263170381631 151783505086491394755572447)
  ·
    refine ⟨227675257629737092133358671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151783505086491394755572447 227675257629737092133358671)
    ·
      refine ⟨341512886444605638200038007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227675257629737092133358671 341512886444605638200038007)
      ·
        refine ⟨512269329666908457300057011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341512886444605638200038007 512269329666908457300057011)
        ·
          refine ⟨768403994500362685950085517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512269329666908457300057011 768403994500362685950085517)
          ·
            refine ⟨288151497937636007231282069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768403994500362685950085517 288151497937636007231282069)
            ·
              refine ⟨13507101465826687838966347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288151497937636007231282069 13507101465826687838966347)
              ·
                refine ⟨20260652198740031758449521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13507101465826687838966347 20260652198740031758449521)
                ·
                  refine ⟨15195489149055023818837141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20260652198740031758449521 15195489149055023818837141)
                  ·
                    refine ⟨712288553861954241507991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15195489149055023818837141 712288553861954241507991)
                    ·
                      rfl

theorem cell23_4161531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_4161531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161531 prefixEnd_4161531 := by exact prefixLift 4161531
  have htrace : WordTrace (prefixWord ++ tailWord_4161531) baseStart_4161531 baseEnd_4161531 := by
    simpa [prefixWord, tailWord_4161531, baseEnd_4161531] using wordTrace_append hprefix tailTrace_4161531
  have hstable : (prefixWord ++ tailWord_4161531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161531).length < 2 ^ (prefixWord ++ tailWord_4161531).sum := by decide
  have hdescent : baseEnd_4161531 < baseStart_4161531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161532 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_4161532 : Nat := 118140960795 + 4161532 * 2 ^ 59
def prefixEnd_4161532 : Nat := 4983230072969 + 3 ^ 40 * 4161532 * 2
def baseEnd_4161532 : Nat := 2136866175066517220611469

theorem tailTrace_4161532 : CollatzResearch.WordTrace tailWord_4161532 prefixEnd_4161532 2136866175066517220611469 := by
  unfold tailWord_4161532
  simp only [CollatzResearch.WordTrace]
  refine ⟨75891770779743885963179425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101189027706325181284239233 75891770779743885963179425)
  ·
    refine ⟨56918828084807914472384569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75891770779743885963179425 56918828084807914472384569)
    ·
      refine ⟨42689121063605935854288427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56918828084807914472384569 42689121063605935854288427)
      ·
        refine ⟨64033681595408903781432641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42689121063605935854288427 64033681595408903781432641)
        ·
          refine ⟨48025261196556677836074481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64033681595408903781432641 48025261196556677836074481)
          ·
            refine ⟨36018945897417508377055861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48025261196556677836074481 36018945897417508377055861)
            ·
              refine ⟨3376776177882891410348987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36018945897417508377055861 3376776177882891410348987)
              ·
                refine ⟨5065164266824337115523481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376776177882891410348987 5065164266824337115523481)
                ·
                  refine ⟨3798873200118252836642611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065164266824337115523481 3798873200118252836642611)
                  ·
                    refine ⟨5698309800177379254963917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3798873200118252836642611 5698309800177379254963917)
                    ·
                      refine ⟨2136866175066517220611469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698309800177379254963917 2136866175066517220611469)
                      ·
                        rfl

theorem cell23_4161532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_4161532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161532 prefixEnd_4161532 := by exact prefixLift 4161532
  have htrace : WordTrace (prefixWord ++ tailWord_4161532) baseStart_4161532 baseEnd_4161532 := by
    simpa [prefixWord, tailWord_4161532, baseEnd_4161532] using wordTrace_append hprefix tailTrace_4161532
  have hstable : (prefixWord ++ tailWord_4161532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161532).length < 2 ^ (prefixWord ++ tailWord_4161532).sum := by decide
  have hdescent : baseEnd_4161532 < baseStart_4161532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161555 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 4, 2, 2]
def baseStart_4161555 : Nat := 118140960795 + 4161555 * 2 ^ 59
def prefixEnd_4161555 : Nat := 4983230072969 + 3 ^ 40 * 4161555 * 2
def baseEnd_4161555 : Nat := 2136877985121570630623863

theorem tailTrace_4161555 : CollatzResearch.WordTrace tailWord_4161555 prefixEnd_4161555 2136877985121570630623863 := by
  unfold tailWord_4161555
  simp only [CollatzResearch.WordTrace]
  refine ⟨151784380438404446854446119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101189586958936297902964079 151784380438404446854446119)
  ·
    refine ⟨227676570657606670281669179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151784380438404446854446119 227676570657606670281669179)
    ·
      refine ⟨341514855986410005422503769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227676570657606670281669179 341514855986410005422503769)
      ·
        refine ⟨256136141989807504066877827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341514855986410005422503769 256136141989807504066877827)
        ·
          refine ⟨384204212984711256100316741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256136141989807504066877827 384204212984711256100316741)
          ·
            refine ⟨72038289934633360518809389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384204212984711256100316741 72038289934633360518809389)
            ·
              refine ⟨27014358725487510194553521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72038289934633360518809389 27014358725487510194553521)
              ·
                refine ⟨20260769044115632645915141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27014358725487510194553521 20260769044115632645915141)
                ·
                  refine ⟨3798894195771681121109089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20260769044115632645915141 3798894195771681121109089)
                  ·
                    refine ⟨2849170646828760840831817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798894195771681121109089 2849170646828760840831817)
                    ·
                      refine ⟨2136877985121570630623863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849170646828760840831817 2136877985121570630623863)
                      ·
                        rfl

theorem cell23_4161555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 2, 2].length) (baseStart_4161555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161555 prefixEnd_4161555 := by exact prefixLift 4161555
  have htrace : WordTrace (prefixWord ++ tailWord_4161555) baseStart_4161555 baseEnd_4161555 := by
    simpa [prefixWord, tailWord_4161555, baseEnd_4161555] using wordTrace_append hprefix tailTrace_4161555
  have hstable : (prefixWord ++ tailWord_4161555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161555).length < 2 ^ (prefixWord ++ tailWord_4161555).sum := by decide
  have hdescent : baseEnd_4161555 < baseStart_4161555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161571 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4161571 : Nat := 118140960795 + 4161571 * 2 ^ 59
def prefixEnd_4161571 : Nat := 4983230072969 + 3 ^ 40 * 4161571 * 2
def baseEnd_4161571 : Nat := 2136886200812042568023789

theorem tailTrace_4161571 : CollatzResearch.WordTrace tailWord_4161571 prefixEnd_4161571 2136886200812042568023789 := by
  unfold tailWord_4161571
  simp only [CollatzResearch.WordTrace]
  refine ⟨151784964006346481587028567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101189976004230987724685711 151784964006346481587028567)
  ·
    refine ⟨227677446009519722380542851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151784964006346481587028567 227677446009519722380542851)
    ·
      refine ⟨341516169014279583570814277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227677446009519722380542851 341516169014279583570814277)
      ·
        refine ⟨64034281690177421919527677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341516169014279583570814277 64034281690177421919527677)
        ·
          refine ⟨24012855633816533219822879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64034281690177421919527677 24012855633816533219822879)
          ·
            refine ⟨36019283450724799829734319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24012855633816533219822879 36019283450724799829734319)
            ·
              refine ⟨54028925176087199744601479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36019283450724799829734319 54028925176087199744601479)
              ·
                refine ⟨81043387764130799616902219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54028925176087199744601479 81043387764130799616902219)
                ·
                  refine ⟨121565081646196199425353329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81043387764130799616902219 121565081646196199425353329)
                  ·
                    refine ⟨91173811234647149569014997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121565081646196199425353329 91173811234647149569014997)
                    ·
                      refine ⟨2136886200812042568023789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91173811234647149569014997 2136886200812042568023789)
                      ·
                        rfl

theorem cell23_4161571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4161571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161571 prefixEnd_4161571 := by exact prefixLift 4161571
  have htrace : WordTrace (prefixWord ++ tailWord_4161571) baseStart_4161571 baseEnd_4161571 := by
    simpa [prefixWord, tailWord_4161571, baseEnd_4161571] using wordTrace_append hprefix tailTrace_4161571
  have hstable : (prefixWord ++ tailWord_4161571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161571).length < 2 ^ (prefixWord ++ tailWord_4161571).sum := by decide
  have hdescent : baseEnd_4161571 < baseStart_4161571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161589 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_4161589 : Nat := 118140960795 + 4161589 * 2 ^ 59
def prefixEnd_4161589 : Nat := 4983230072969 + 3 ^ 40 * 4161589 * 2
def baseEnd_4161589 : Nat := 2136895443463823497598707

theorem tailTrace_4161589 : CollatzResearch.WordTrace tailWord_4161589 prefixEnd_4161589 2136895443463823497598707 := by
  unfold tailWord_4161589
  simp only [CollatzResearch.WordTrace]
  refine ⟨151785620520281270661183821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101190413680187513774122547 151785620520281270661183821)
  ·
    refine ⟨56919607695105476497943933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151785620520281270661183821 56919607695105476497943933)
    ·
      refine ⟨21344852885664553686728975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56919607695105476497943933 21344852885664553686728975)
      ·
        refine ⟨32017279328496830530093463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21344852885664553686728975 32017279328496830530093463)
        ·
          refine ⟨48025918992745245795140195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32017279328496830530093463 48025918992745245795140195)
          ·
            refine ⟨72038878489117868692710293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48025918992745245795140195 72038878489117868692710293)
            ·
              refine ⟨3376822429177400094970795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72038878489117868692710293 3376822429177400094970795)
              ·
                refine ⟨5065233643766100142456193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376822429177400094970795 5065233643766100142456193)
                ·
                  refine ⟨3798925232824575106842145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065233643766100142456193 3798925232824575106842145)
                  ·
                    refine ⟨2849193924618431330131609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3798925232824575106842145 2849193924618431330131609)
                    ·
                      refine ⟨2136895443463823497598707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849193924618431330131609 2136895443463823497598707)
                      ·
                        rfl

theorem cell23_4161589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_4161589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161589 prefixEnd_4161589 := by exact prefixLift 4161589
  have htrace : WordTrace (prefixWord ++ tailWord_4161589) baseStart_4161589 baseEnd_4161589 := by
    simpa [prefixWord, tailWord_4161589, baseEnd_4161589] using wordTrace_append hprefix tailTrace_4161589
  have hstable : (prefixWord ++ tailWord_4161589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161589).length < 2 ^ (prefixWord ++ tailWord_4161589).sum := by decide
  have hdescent : baseEnd_4161589 < baseStart_4161589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161591 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 7]
def baseStart_4161591 : Nat := 118140960795 + 4161591 * 2 ^ 59
def prefixEnd_4161591 : Nat := 4983230072969 + 3 ^ 40 * 4161591 * 2
def baseEnd_4161591 : Nat := 712298823475044163257899

theorem tailTrace_4161591 : CollatzResearch.WordTrace tailWord_4161591 prefixEnd_4161591 712298823475044163257899 := by
  unfold tailWord_4161591
  simp only [CollatzResearch.WordTrace]
  refine ⟨151785693466274025002756627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101190462310849350001837751 151785693466274025002756627)
  ·
    refine ⟨227678540199411037504134941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151785693466274025002756627 227678540199411037504134941)
    ·
      refine ⟨85379452574779139064050603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227678540199411037504134941 85379452574779139064050603)
      ·
        refine ⟨128069178862168708596075905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85379452574779139064050603 128069178862168708596075905)
        ·
          refine ⟨96051884146626531447056929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128069178862168708596075905 96051884146626531447056929)
          ·
            refine ⟨72038913109969898585292697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96051884146626531447056929 72038913109969898585292697)
            ·
              refine ⟨54029184832477423938969523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72038913109969898585292697 54029184832477423938969523)
              ·
                refine ⟨81043777248716135908454285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54029184832477423938969523 81043777248716135908454285)
                ·
                  refine ⟨30391416468268550965670357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81043777248716135908454285 30391416468268550965670357)
                  ·
                    refine ⟨712298823475044163257899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30391416468268550965670357 712298823475044163257899)
                    ·
                      rfl

theorem cell23_4161591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_4161591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161591 prefixEnd_4161591 := by exact prefixLift 4161591
  have htrace : WordTrace (prefixWord ++ tailWord_4161591) baseStart_4161591 baseEnd_4161591 := by
    simpa [prefixWord, tailWord_4161591, baseEnd_4161591] using wordTrace_append hprefix tailTrace_4161591
  have hstable : (prefixWord ++ tailWord_4161591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161591).length < 2 ^ (prefixWord ++ tailWord_4161591).sum := by decide
  have hdescent : baseEnd_4161591 < baseStart_4161591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161629 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 5]
def baseStart_4161629 : Nat := 118140960795 + 4161629 * 2 ^ 59
def prefixEnd_4161629 : Nat := 4983230072969 + 3 ^ 40 * 4161629 * 2
def baseEnd_4161629 : Nat := 237435109187778149010947

theorem tailTrace_4161629 : CollatzResearch.WordTrace tailWord_4161629 prefixEnd_4161629 237435109187778149010947 := by
  unfold tailWord_4161629
  simp only [CollatzResearch.WordTrace]
  refine ⟨151787079440136357492639941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101191386293424238328426627 151787079440136357492639941)
  ·
    refine ⟨28460077395025567029869989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151787079440136357492639941 28460077395025567029869989)
    ·
      refine ⟨5336264511567293818100623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28460077395025567029869989 5336264511567293818100623)
      ·
        refine ⟨8004396767350940727150935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336264511567293818100623 8004396767350940727150935)
        ·
          refine ⟨12006595151026411090726403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8004396767350940727150935 12006595151026411090726403)
          ·
            refine ⟨18009892726539616636089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006595151026411090726403 18009892726539616636089605)
            ·
              refine ⟨3376854886226178119266801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18009892726539616636089605 3376854886226178119266801)
              ·
                refine ⟨2532641164669633589450101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3376854886226178119266801 2532641164669633589450101)
                ·
                  refine ⟨237435109187778149010947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2532641164669633589450101 237435109187778149010947)
                  ·
                    rfl

theorem cell23_4161629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_4161629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161629 prefixEnd_4161629 := by exact prefixLift 4161629
  have htrace : WordTrace (prefixWord ++ tailWord_4161629) baseStart_4161629 baseEnd_4161629 := by
    simpa [prefixWord, tailWord_4161629, baseEnd_4161629] using wordTrace_append hprefix tailTrace_4161629
  have hstable : (prefixWord ++ tailWord_4161629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161629).length < 2 ^ (prefixWord ++ tailWord_4161629).sum := by decide
  have hdescent : baseEnd_4161629 < baseStart_4161629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161655 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 3, 4]
def baseStart_4161655 : Nat := 118140960795 + 4161655 * 2 ^ 59
def prefixEnd_4161655 : Nat := 4983230072969 + 3 ^ 40 * 4161655 * 2
def baseEnd_4161655 : Nat := 712309777729006746457801

theorem tailTrace_4161655 : CollatzResearch.WordTrace tailWord_4161655 prefixEnd_4161655 712309777729006746457801 := by
  unfold tailWord_4161655
  simp only [CollatzResearch.WordTrace]
  refine ⟨151788027738042163933086419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101192018492028109288724279 151788027738042163933086419)
  ·
    refine ⟨227682041607063245899629629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151788027738042163933086419 227682041607063245899629629)
    ·
      refine ⟨85380765602648717212361111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227682041607063245899629629 85380765602648717212361111)
      ·
        refine ⟨128071148403973075818541667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85380765602648717212361111 128071148403973075818541667)
        ·
          refine ⟨192106722605959613727812501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128071148403973075818541667 192106722605959613727812501)
          ·
            refine ⟨9005002622154356893491211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192106722605959613727812501 9005002622154356893491211)
            ·
              refine ⟨13507503933231535340236817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005002622154356893491211 13507503933231535340236817)
              ·
                refine ⟨10130627949923651505177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13507503933231535340236817 10130627949923651505177613)
                ·
                  refine ⟨3798985481221369314441605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10130627949923651505177613 3798985481221369314441605)
                  ·
                    refine ⟨712309777729006746457801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3798985481221369314441605 712309777729006746457801)
                    ·
                      rfl

theorem cell23_4161655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_4161655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161655 prefixEnd_4161655 := by exact prefixLift 4161655
  have htrace : WordTrace (prefixWord ++ tailWord_4161655) baseStart_4161655 baseEnd_4161655 := by
    simpa [prefixWord, tailWord_4161655, baseEnd_4161655] using wordTrace_append hprefix tailTrace_4161655
  have hstable : (prefixWord ++ tailWord_4161655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161655).length < 2 ^ (prefixWord ++ tailWord_4161655).sum := by decide
  have hdescent : baseEnd_4161655 < baseStart_4161655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161668 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 8]
def baseStart_4161668 : Nat := 118140960795 + 4161668 * 2 ^ 59
def prefixEnd_4161668 : Nat := 4983230072969 + 3 ^ 40 * 4161668 * 2
def baseEnd_4161668 : Nat := 237437334270614298723427

theorem tailTrace_4161668 : CollatzResearch.WordTrace tailWord_4161668 prefixEnd_4161668 237437334270614298723427 := by
  unfold tailWord_4161668
  simp only [CollatzResearch.WordTrace]
  refine ⟨75894250943497533576654829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101192334591330044768873105 75894250943497533576654829)
  ·
    refine ⟨28460344103811575091245561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75894250943497533576654829 28460344103811575091245561)
    ·
      refine ⟨21345258077858681318434171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28460344103811575091245561 21345258077858681318434171)
      ·
        refine ⟨32017887116788021977651257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21345258077858681318434171 32017887116788021977651257)
        ·
          refine ⟨24013415337591016483238443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32017887116788021977651257 24013415337591016483238443)
          ·
            refine ⟨36020123006386524724857665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24013415337591016483238443 36020123006386524724857665)
            ·
              refine ⟨27015092254789893543643249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36020123006386524724857665 27015092254789893543643249)
              ·
                refine ⟨20261319191092420157732437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27015092254789893543643249 20261319191092420157732437)
                ·
                  refine ⟨237437334270614298723427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20261319191092420157732437 237437334270614298723427)
                  ·
                    rfl

theorem cell23_4161668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_4161668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161668 prefixEnd_4161668 := by exact prefixLift 4161668
  have htrace : WordTrace (prefixWord ++ tailWord_4161668) baseStart_4161668 baseEnd_4161668 := by
    simpa [prefixWord, tailWord_4161668, baseEnd_4161668] using wordTrace_append hprefix tailTrace_4161668
  have hstable : (prefixWord ++ tailWord_4161668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161668).length < 2 ^ (prefixWord ++ tailWord_4161668).sum := by decide
  have hdescent : baseEnd_4161668 < baseStart_4161668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161732 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4161732 : Nat := 118140960795 + 4161732 * 2 ^ 59
def prefixEnd_4161732 : Nat := 4983230072969 + 3 ^ 40 * 4161732 * 2
def baseEnd_4161732 : Nat := 712322957065805479370183

theorem tailTrace_4161732 : CollatzResearch.WordTrace tailWord_4161732 prefixEnd_4161732 712322957065805479370183 := by
  unfold tailWord_4161732
  simp only [CollatzResearch.WordTrace]
  refine ⟨75895418079381603041819725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101193890772508804055759633 75895418079381603041819725)
  ·
    refine ⟨28460781779768101140682397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75895418079381603041819725 28460781779768101140682397)
    ·
      refine ⟨10672793167413037927755899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28460781779768101140682397 10672793167413037927755899)
      ·
        refine ⟨16009189751119556891633849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10672793167413037927755899 16009189751119556891633849)
        ·
          refine ⟨12006892313339667668725387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16009189751119556891633849 12006892313339667668725387)
          ·
            refine ⟨18010338470009501503088081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006892313339667668725387 18010338470009501503088081)
            ·
              refine ⟨13507753852507126127316061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010338470009501503088081 13507753852507126127316061)
              ·
                refine ⟨5065407694690172297743523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13507753852507126127316061 5065407694690172297743523)
                ·
                  refine ⟨7598111542035258446615285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065407694690172297743523 7598111542035258446615285)
                  ·
                    refine ⟨712322957065805479370183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7598111542035258446615285 712322957065805479370183)
                    ·
                      rfl

theorem cell23_4161732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4161732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161732 prefixEnd_4161732 := by exact prefixLift 4161732
  have htrace : WordTrace (prefixWord ++ tailWord_4161732) baseStart_4161732 baseEnd_4161732 := by
    simpa [prefixWord, tailWord_4161732, baseEnd_4161732] using wordTrace_append hprefix tailTrace_4161732
  have hstable : (prefixWord ++ tailWord_4161732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161732).length < 2 ^ (prefixWord ++ tailWord_4161732).sum := by decide
  have hdescent : baseEnd_4161732 < baseStart_4161732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161745 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_4161745 : Nat := 118140960795 + 4161745 * 2 ^ 59
def prefixEnd_4161745 : Nat := 4983230072969 + 3 ^ 40 * 4161745 * 2
def baseEnd_4161745 : Nat := 712325182148641629082663

theorem tailTrace_4161745 : CollatzResearch.WordTrace tailWord_4161745 prefixEnd_4161745 712325182148641629082663 := by
  unfold tailWord_4161745
  simp only [CollatzResearch.WordTrace]
  refine ⟨151791310307716109303862689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101194206871810739535908459 151791310307716109303862689)
  ·
    refine ⟨113843482730787081977897017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151791310307716109303862689 113843482730787081977897017)
    ·
      refine ⟨85382612048090311483422763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113843482730787081977897017 85382612048090311483422763)
      ·
        refine ⟨128073918072135467225134145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85382612048090311483422763 128073918072135467225134145)
        ·
          refine ⟨96055438554101600418850609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128073918072135467225134145 96055438554101600418850609)
          ·
            refine ⟨72041578915576200314137957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96055438554101600418850609 72041578915576200314137957)
            ·
              refine ⟨13507796046670537558900867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72041578915576200314137957 13507796046670537558900867)
              ·
                refine ⟨20261694070005806338351301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13507796046670537558900867 20261694070005806338351301)
                ·
                  refine ⟨3799067638126088688440869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20261694070005806338351301 3799067638126088688440869)
                  ·
                    refine ⟨712325182148641629082663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799067638126088688440869 712325182148641629082663)
                    ·
                      rfl

theorem cell23_4161745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_4161745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161745 prefixEnd_4161745 := by exact prefixLift 4161745
  have htrace : WordTrace (prefixWord ++ tailWord_4161745) baseStart_4161745 baseEnd_4161745 := by
    simpa [prefixWord, tailWord_4161745, baseEnd_4161745] using wordTrace_append hprefix tailTrace_4161745
  have hstable : (prefixWord ++ tailWord_4161745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161745).length < 2 ^ (prefixWord ++ tailWord_4161745).sum := by decide
  have hdescent : baseEnd_4161745 < baseStart_4161745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161765 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4161765 : Nat := 118140960795 + 4161765 * 2 ^ 59
def prefixEnd_4161765 : Nat := 4983230072969 + 3 ^ 40 * 4161765 * 2
def baseEnd_4161765 : Nat := 2136985816059014808997897

theorem tailTrace_4161765 : CollatzResearch.WordTrace tailWord_4161765 prefixEnd_4161765 2136985816059014808997897 := by
  unfold tailWord_4161765
  simp only [CollatzResearch.WordTrace]
  refine ⟨151792039767643652719590749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101194693178429101813060499 151792039767643652719590749)
  ·
    refine ⟨56922014912866369769846531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151792039767643652719590749 56922014912866369769846531)
    ·
      refine ⟨85383022369299554654769797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56922014912866369769846531 85383022369299554654769797)
      ·
        refine ⟨16009316694243666497769337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85383022369299554654769797 16009316694243666497769337)
        ·
          refine ⟨12006987520682749873327003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16009316694243666497769337 12006987520682749873327003)
          ·
            refine ⟨18010481281024124809990505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12006987520682749873327003 18010481281024124809990505)
            ·
              refine ⟨13507860960768093607492879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18010481281024124809990505 13507860960768093607492879)
              ·
                refine ⟨20261791441152140411239319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13507860960768093607492879 20261791441152140411239319)
                ·
                  refine ⟨30392687161728210616858979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20261791441152140411239319 30392687161728210616858979)
                  ·
                    refine ⟨45589030742592315925288469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30392687161728210616858979 45589030742592315925288469)
                    ·
                      refine ⟨2136985816059014808997897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45589030742592315925288469 2136985816059014808997897)
                      ·
                        rfl

theorem cell23_4161765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4161765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161765 prefixEnd_4161765 := by exact prefixLift 4161765
  have htrace : WordTrace (prefixWord ++ tailWord_4161765) baseStart_4161765 baseEnd_4161765 := by
    simpa [prefixWord, tailWord_4161765, baseEnd_4161765] using wordTrace_append hprefix tailTrace_4161765
  have hstable : (prefixWord ++ tailWord_4161765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161765).length < 2 ^ (prefixWord ++ tailWord_4161765).sum := by decide
  have hdescent : baseEnd_4161765 < baseStart_4161765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161802 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4161802 : Nat := 118140960795 + 4161802 * 2 ^ 59
def prefixEnd_4161802 : Nat := 4983230072969 + 3 ^ 40 * 4161802 * 2
def baseEnd_4161802 : Nat := 2137004814843231164235227

theorem tailTrace_4161802 : CollatzResearch.WordTrace tailWord_4161802 prefixEnd_4161802 2137004814843231164235227 := by
  unfold tailWord_4161802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37948347317127402009671915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101195592845673072025791773 37948347317127402009671915)
  ·
    refine ⟨56922520975691103014507873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37948347317127402009671915 56922520975691103014507873)
    ·
      refine ⟨42691890731768327260880905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56922520975691103014507873 42691890731768327260880905)
      ·
        refine ⟨32018918048826245445660679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42691890731768327260880905 32018918048826245445660679)
        ·
          refine ⟨48028377073239368168491019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32018918048826245445660679 48028377073239368168491019)
          ·
            refine ⟨72042565609859052252736529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48028377073239368168491019 72042565609859052252736529)
            ·
              refine ⟨54031924207394289189552397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72042565609859052252736529 54031924207394289189552397)
              ·
                refine ⟨20261971577772858446082149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54031924207394289189552397 20261971577772858446082149)
                ·
                  refine ⟨3799119670832410958640403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20261971577772858446082149 3799119670832410958640403)
                  ·
                    refine ⟨5698679506248616437960605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799119670832410958640403 5698679506248616437960605)
                    ·
                      refine ⟨2137004814843231164235227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698679506248616437960605 2137004814843231164235227)
                      ·
                        rfl

theorem cell23_4161802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4161802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161802 prefixEnd_4161802 := by exact prefixLift 4161802
  have htrace : WordTrace (prefixWord ++ tailWord_4161802) baseStart_4161802 baseEnd_4161802 := by
    simpa [prefixWord, tailWord_4161802, baseEnd_4161802] using wordTrace_append hprefix tailTrace_4161802
  have hstable : (prefixWord ++ tailWord_4161802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161802).length < 2 ^ (prefixWord ++ tailWord_4161802).sum := by decide
  have hdescent : baseEnd_4161802 < baseStart_4161802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161845 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4161845 : Nat := 118140960795 + 4161845 * 2 ^ 59
def prefixEnd_4161845 : Nat := 4983230072969 + 3 ^ 40 * 4161845 * 2
def baseEnd_4161845 : Nat := 2137026894511374495997529

theorem tailTrace_4161845 : CollatzResearch.WordTrace tailWord_4161845 prefixEnd_4161845 2137026894511374495997529 := by
  unfold tailWord_4161845
  simp only [CollatzResearch.WordTrace]
  refine ⟨151794957607353826382502989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101196638404902550921668659 151794957607353826382502989)
  ·
    refine ⟨56923109102757684893438621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151794957607353826382502989 56923109102757684893438621)
    ·
      refine ⟨21346165913534131835039483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56923109102757684893438621 21346165913534131835039483)
      ·
        refine ⟨32019248870301197752559225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21346165913534131835039483 32019248870301197752559225)
        ·
          refine ⟨24014436652725898314419419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32019248870301197752559225 24014436652725898314419419)
          ·
            refine ⟨36021654979088847471629129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24014436652725898314419419 36021654979088847471629129)
            ·
              refine ⟨27016241234316635603721847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36021654979088847471629129 27016241234316635603721847)
              ·
                refine ⟨40524361851474953405582771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27016241234316635603721847 40524361851474953405582771)
                ·
                  refine ⟨60786542777212430108374157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40524361851474953405582771 60786542777212430108374157)
                  ·
                    refine ⟨22794953541454661290640309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60786542777212430108374157 22794953541454661290640309)
                    ·
                      refine ⟨2137026894511374495997529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22794953541454661290640309 2137026894511374495997529)
                      ·
                        rfl

theorem cell23_4161845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4161845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161845 prefixEnd_4161845 := by exact prefixLift 4161845
  have htrace : WordTrace (prefixWord ++ tailWord_4161845) baseStart_4161845 baseEnd_4161845 := by
    simpa [prefixWord, tailWord_4161845, baseEnd_4161845] using wordTrace_append hprefix tailTrace_4161845
  have hstable : (prefixWord ++ tailWord_4161845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161845).length < 2 ^ (prefixWord ++ tailWord_4161845).sum := by decide
  have hdescent : baseEnd_4161845 < baseStart_4161845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161855 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_4161855 : Nat := 118140960795 + 4161855 * 2 ^ 59
def prefixEnd_4161855 : Nat := 4983230072969 + 3 ^ 40 * 4161855 * 2
def baseEnd_4161855 : Nat := 2137032029317919456872483

theorem tailTrace_4161855 : CollatzResearch.WordTrace tailWord_4161855 prefixEnd_4161855 2137032029317919456872483 := by
  unfold tailWord_4161855
  simp only [CollatzResearch.WordTrace]
  refine ⟨151795322337317598090367019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101196881558211732060244679 151795322337317598090367019)
  ·
    refine ⟨227692983505976397135550529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151795322337317598090367019 227692983505976397135550529)
    ·
      refine ⟨170769737629482297851662897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227692983505976397135550529 170769737629482297851662897)
      ·
        refine ⟨128077303222111723388747173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170769737629482297851662897 128077303222111723388747173)
        ·
          refine ⟨24014494354145948135390095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128077303222111723388747173 24014494354145948135390095)
          ·
            refine ⟨36021741531218922203085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24014494354145948135390095 36021741531218922203085143)
            ·
              refine ⟨54032612296828383304627715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36021741531218922203085143 54032612296828383304627715)
              ·
                refine ⟨81048918445242574956941573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54032612296828383304627715 81048918445242574956941573)
                ·
                  refine ⟨15196672208482982804426545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81048918445242574956941573 15196672208482982804426545)
                  ·
                    refine ⟨11397504156362237103319909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15196672208482982804426545 11397504156362237103319909)
                    ·
                      refine ⟨2137032029317919456872483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11397504156362237103319909 2137032029317919456872483)
                      ·
                        rfl

theorem cell23_4161855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_4161855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161855 prefixEnd_4161855 := by exact prefixLift 4161855
  have htrace : WordTrace (prefixWord ++ tailWord_4161855) baseStart_4161855 baseEnd_4161855 := by
    simpa [prefixWord, tailWord_4161855, baseEnd_4161855] using wordTrace_append hprefix tailTrace_4161855
  have hstable : (prefixWord ++ tailWord_4161855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161855).length < 2 ^ (prefixWord ++ tailWord_4161855).sum := by decide
  have hdescent : baseEnd_4161855 < baseStart_4161855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161875 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3]
def baseStart_4161875 : Nat := 118140960795 + 4161875 * 2 ^ 59
def prefixEnd_4161875 : Nat := 4983230072969 + 3 ^ 40 * 4161875 * 2
def baseEnd_4161875 : Nat := 2137042298931009378622391

theorem tailTrace_4161875 : CollatzResearch.WordTrace tailWord_4161875 prefixEnd_4161875 2137042298931009378622391 := by
  unfold tailWord_4161875
  simp only [CollatzResearch.WordTrace]
  refine ⟨151796051797245141506095079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101197367864830094337396719 151796051797245141506095079)
  ·
    refine ⟨227694077695867712259142619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151796051797245141506095079 227694077695867712259142619)
    ·
      refine ⟨341541116543801568388713929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227694077695867712259142619 341541116543801568388713929)
      ·
        refine ⟨256155837407851176291535447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341541116543801568388713929 256155837407851176291535447)
        ·
          refine ⟨384233756111776764437303171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256155837407851176291535447 384233756111776764437303171)
          ·
            refine ⟨576350634167665146655954757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384233756111776764437303171 576350634167665146655954757)
            ·
              refine ⟨108065743906437214997991517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 576350634167665146655954757 108065743906437214997991517)
              ·
                refine ⟨40524653964913955624246819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108065743906437214997991517 40524653964913955624246819)
                ·
                  refine ⟨60786980947370933436370229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40524653964913955624246819 60786980947370933436370229)
                  ·
                    refine ⟨5698779463816025009659709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60786980947370933436370229 5698779463816025009659709)
                    ·
                      refine ⟨2137042298931009378622391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698779463816025009659709 2137042298931009378622391)
                      ·
                        rfl

theorem cell23_4161875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_4161875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161875 prefixEnd_4161875 := by exact prefixLift 4161875
  have htrace : WordTrace (prefixWord ++ tailWord_4161875) baseStart_4161875 baseEnd_4161875 := by
    simpa [prefixWord, tailWord_4161875, baseEnd_4161875] using wordTrace_append hprefix tailTrace_4161875
  have hstable : (prefixWord ++ tailWord_4161875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161875).length < 2 ^ (prefixWord ++ tailWord_4161875).sum := by decide
  have hdescent : baseEnd_4161875 < baseStart_4161875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161876 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_4161876 : Nat := 118140960795 + 4161876 * 2 ^ 59
def prefixEnd_4161876 : Nat := 4983230072969 + 3 ^ 40 * 4161876 * 2
def baseEnd_4161876 : Nat := 2137042812411663874709887

theorem tailTrace_4161876 : CollatzResearch.WordTrace tailWord_4161876 prefixEnd_4161876 2137042812411663874709887 := by
  unfold tailWord_4161876
  simp only [CollatzResearch.WordTrace]
  refine ⟨75898044135120759338440741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101197392180161012451254321 75898044135120759338440741)
  ·
    refine ⟨14230883275335142375957639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75898044135120759338440741 14230883275335142375957639)
    ·
      refine ⟨21346324913002713563936459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14230883275335142375957639 21346324913002713563936459)
      ·
        refine ⟨32019487369504070345904689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21346324913002713563936459 32019487369504070345904689)
        ·
          refine ⟨24014615527128052759428517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32019487369504070345904689 24014615527128052759428517)
          ·
            refine ⟨4502740411336509892392847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24014615527128052759428517 4502740411336509892392847)
            ·
              refine ⟨6754110617004764838589271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502740411336509892392847 6754110617004764838589271)
              ·
                refine ⟨10131165925507147257883907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754110617004764838589271 10131165925507147257883907)
                ·
                  refine ⟨15196748888260720886825861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10131165925507147257883907 15196748888260720886825861)
                  ·
                    refine ⟨2849390416548885166279849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15196748888260720886825861 2849390416548885166279849)
                    ·
                      refine ⟨2137042812411663874709887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849390416548885166279849 2137042812411663874709887)
                      ·
                        rfl

theorem cell23_4161876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_4161876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161876 prefixEnd_4161876 := by exact prefixLift 4161876
  have htrace : WordTrace (prefixWord ++ tailWord_4161876) baseStart_4161876 baseEnd_4161876 := by
    simpa [prefixWord, tailWord_4161876, baseEnd_4161876] using wordTrace_append hprefix tailTrace_4161876
  have hstable : (prefixWord ++ tailWord_4161876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161876).length < 2 ^ (prefixWord ++ tailWord_4161876).sum := by decide
  have hdescent : baseEnd_4161876 < baseStart_4161876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161905 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_4161905 : Nat := 118140960795 + 4161905 * 2 ^ 59
def prefixEnd_4161905 : Nat := 4983230072969 + 3 ^ 40 * 4161905 * 2
def baseEnd_4161905 : Nat := 2137057703350644261247253

theorem tailTrace_4161905 : CollatzResearch.WordTrace tailWord_4161905 prefixEnd_4161905 2137057703350644261247253 := by
  unfold tailWord_4161905
  simp only [CollatzResearch.WordTrace]
  refine ⟨151797145987136456629687169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101198097324757637753124779 151797145987136456629687169)
  ·
    refine ⟨113847859490352342472265377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151797145987136456629687169 113847859490352342472265377)
    ·
      refine ⟨85385894617764256854199033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113847859490352342472265377 85385894617764256854199033)
      ·
        refine ⟨64039420963323192640649275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85385894617764256854199033 64039420963323192640649275)
        ·
          refine ⟨96059131444984788960973913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64039420963323192640649275 96059131444984788960973913)
          ·
            refine ⟨72044348583738591720730435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96059131444984788960973913 72044348583738591720730435)
            ·
              refine ⟨108066522875607887581095653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72044348583738591720730435 108066522875607887581095653)
              ·
                refine ⟨20262473039176478921455435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108066522875607887581095653 20262473039176478921455435)
                ·
                  refine ⟨30393709558764718382183153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20262473039176478921455435 30393709558764718382183153)
                  ·
                    refine ⟨22795282169073538786637365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30393709558764718382183153 22795282169073538786637365)
                    ·
                      refine ⟨2137057703350644261247253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22795282169073538786637365 2137057703350644261247253)
                      ·
                        rfl

theorem cell23_4161905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_4161905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161905 prefixEnd_4161905 := by exact prefixLift 4161905
  have htrace : WordTrace (prefixWord ++ tailWord_4161905) baseStart_4161905 baseEnd_4161905 := by
    simpa [prefixWord, tailWord_4161905, baseEnd_4161905] using wordTrace_append hprefix tailTrace_4161905
  have hstable : (prefixWord ++ tailWord_4161905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161905).length < 2 ^ (prefixWord ++ tailWord_4161905).sum := by decide
  have hdescent : baseEnd_4161905 < baseStart_4161905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161969 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4161969 : Nat := 118140960795 + 4161969 * 2 ^ 59
def prefixEnd_4161969 : Nat := 4983230072969 + 3 ^ 40 * 4161969 * 2
def baseEnd_4161969 : Nat := 2137090566112532010846959

theorem tailTrace_4161969 : CollatzResearch.WordTrace tailWord_4161969 prefixEnd_4161969 2137090566112532010846959 := by
  unfold tailWord_4161969
  simp only [CollatzResearch.WordTrace]
  refine ⟨151799480258904595560016961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101199653505936397040011307 151799480258904595560016961)
  ·
    refine ⟨113849610194178446670012721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151799480258904595560016961 113849610194178446670012721)
    ·
      refine ⟨85387207645633835002509541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113849610194178446670012721 85387207645633835002509541)
      ·
        refine ⟨16010101433556344062970539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85387207645633835002509541 16010101433556344062970539)
        ·
          refine ⟨24015152150334516094455809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010101433556344062970539 24015152150334516094455809)
          ·
            refine ⟨18011364112750887070841857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24015152150334516094455809 18011364112750887070841857)
            ·
              refine ⟨13508523084563165303131393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18011364112750887070841857 13508523084563165303131393)
              ·
                refine ⟨10131392313422373977348545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13508523084563165303131393 10131392313422373977348545)
                ·
                  refine ⟨7598544235066780483011409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10131392313422373977348545 7598544235066780483011409)
                  ·
                    refine ⟨5698908176300085362258557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598544235066780483011409 5698908176300085362258557)
                    ·
                      refine ⟨2137090566112532010846959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5698908176300085362258557 2137090566112532010846959)
                      ·
                        rfl

theorem cell23_4161969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4161969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161969 prefixEnd_4161969 := by exact prefixLift 4161969
  have htrace : WordTrace (prefixWord ++ tailWord_4161969) baseStart_4161969 baseEnd_4161969 := by
    simpa [prefixWord, tailWord_4161969, baseEnd_4161969] using wordTrace_append hprefix tailTrace_4161969
  have hstable : (prefixWord ++ tailWord_4161969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161969).length < 2 ^ (prefixWord ++ tailWord_4161969).sum := by decide
  have hdescent : baseEnd_4161969 < baseStart_4161969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4161995 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_4161995 : Nat := 118140960795 + 4161995 * 2 ^ 59
def prefixEnd_4161995 : Nat := 4983230072969 + 3 ^ 40 * 4161995 * 2
def baseEnd_4161995 : Nat := 2137103916609548909121839

theorem tailTrace_4161995 : CollatzResearch.WordTrace tailWord_4161995 prefixEnd_4161995 2137103916609548909121839 := by
  unfold tailWord_4161995
  simp only [CollatzResearch.WordTrace]
  refine ⟨151800428556810402000463439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101200285704540268000308959 151800428556810402000463439)
  ·
    refine ⟨227700642835215603000695159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151800428556810402000463439 227700642835215603000695159)
    ·
      refine ⟨341550964252823404501042739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227700642835215603000695159 341550964252823404501042739)
      ·
        refine ⟨512326446379235106751564109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341550964252823404501042739 512326446379235106751564109)
        ·
          refine ⟨192122417392213165031836541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512326446379235106751564109 192122417392213165031836541)
          ·
            refine ⟨72045906522079936886938703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192122417392213165031836541 72045906522079936886938703)
            ·
              refine ⟨108068859783119905330408055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72045906522079936886938703 108068859783119905330408055)
              ·
                refine ⟨162103289674679857995612083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108068859783119905330408055 162103289674679857995612083)
                ·
                  refine ⟨243154934512019786993418125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162103289674679857995612083 243154934512019786993418125)
                  ·
                    refine ⟨91183100442007420122531797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243154934512019786993418125 91183100442007420122531797)
                    ·
                      refine ⟨2137103916609548909121839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91183100442007420122531797 2137103916609548909121839)
                      ·
                        rfl

theorem cell23_4161995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_4161995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4161995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4161995 prefixEnd_4161995 := by exact prefixLift 4161995
  have htrace : WordTrace (prefixWord ++ tailWord_4161995) baseStart_4161995 baseEnd_4161995 := by
    simpa [prefixWord, tailWord_4161995, baseEnd_4161995] using wordTrace_append hprefix tailTrace_4161995
  have hstable : (prefixWord ++ tailWord_4161995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4161995).length < 2 ^ (prefixWord ++ tailWord_4161995).sum := by decide
  have hdescent : baseEnd_4161995 < baseStart_4161995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4161995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162009 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 5, 2]
def baseStart_4162009 : Nat := 118140960795 + 4162009 * 2 ^ 59
def prefixEnd_4162009 : Nat := 4983230072969 + 3 ^ 40 * 4162009 * 2
def baseEnd_4162009 : Nat := 2137111105338711854346775

theorem tailTrace_4162009 : CollatzResearch.WordTrace tailWord_4162009 prefixEnd_4162009 2137111105338711854346775 := by
  unfold tailWord_4162009
  simp only [CollatzResearch.WordTrace]
  refine ⟨151800939178759682391473081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101200626119173121594315387 151800939178759682391473081)
  ·
    refine ⟨113850704384069761793604811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151800939178759682391473081 113850704384069761793604811)
    ·
      refine ⟨170776056576104642690407217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113850704384069761793604811 170776056576104642690407217)
      ·
        refine ⟨128082042432078482017805413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170776056576104642690407217 128082042432078482017805413)
        ·
          refine ⟨24015382956014715378338515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128082042432078482017805413 24015382956014715378338515)
          ·
            refine ⟨36023074434022073067507773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24015382956014715378338515 36023074434022073067507773)
            ·
              refine ⟨13508652912758277400315415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36023074434022073067507773 13508652912758277400315415)
              ·
                refine ⟨20262979369137416100473123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13508652912758277400315415 20262979369137416100473123)
                ·
                  refine ⟨30394469053706124150709685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20262979369137416100473123 30394469053706124150709685)
                  ·
                    refine ⟨2849481473784949139129033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30394469053706124150709685 2849481473784949139129033)
                    ·
                      refine ⟨2137111105338711854346775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849481473784949139129033 2137111105338711854346775)
                      ·
                        rfl

theorem cell23_4162009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_4162009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162009 prefixEnd_4162009 := by exact prefixLift 4162009
  have htrace : WordTrace (prefixWord ++ tailWord_4162009) baseStart_4162009 baseEnd_4162009 := by
    simpa [prefixWord, tailWord_4162009, baseEnd_4162009] using wordTrace_append hprefix tailTrace_4162009
  have hstable : (prefixWord ++ tailWord_4162009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162009).length < 2 ^ (prefixWord ++ tailWord_4162009).sum := by decide
  have hdescent : baseEnd_4162009 < baseStart_4162009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162042 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_4162042 : Nat := 118140960795 + 4162042 * 2 ^ 59
def prefixEnd_4162042 : Nat := 4983230072969 + 3 ^ 40 * 4162042 * 2
def baseEnd_4162042 : Nat := 2137128050200310225234123

theorem tailTrace_4162042 : CollatzResearch.WordTrace tailWord_4162042 prefixEnd_4162042 2137128050200310225234123 := by
  unfold tailWord_4162042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950535696910032256856095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101201428525093419351616253 37950535696910032256856095)
  ·
    refine ⟨56925803545365048385284143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37950535696910032256856095 56925803545365048385284143)
    ·
      refine ⟨85388705318047572577926215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56925803545365048385284143 85388705318047572577926215)
      ·
        refine ⟨128083057977071358866889323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85388705318047572577926215 128083057977071358866889323)
        ·
          refine ⟨192124586965607038300333985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128083057977071358866889323 192124586965607038300333985)
          ·
            refine ⟨144093440224205278725250489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192124586965607038300333985 144093440224205278725250489)
            ·
              refine ⟨108070080168153959043937867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144093440224205278725250489 108070080168153959043937867)
              ·
                refine ⟨162105120252230938565906801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108070080168153959043937867 162105120252230938565906801)
                ·
                  refine ⟨121578840189173203924430101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162105120252230938565906801 121578840189173203924430101)
                  ·
                    refine ⟨5699008133867493933957661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121578840189173203924430101 5699008133867493933957661)
                    ·
                      refine ⟨2137128050200310225234123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699008133867493933957661 2137128050200310225234123)
                      ·
                        rfl

theorem cell23_4162042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_4162042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162042 prefixEnd_4162042 := by exact prefixLift 4162042
  have htrace : WordTrace (prefixWord ++ tailWord_4162042) baseStart_4162042 baseEnd_4162042 := by
    simpa [prefixWord, tailWord_4162042, baseEnd_4162042] using wordTrace_append hprefix tailTrace_4162042
  have hstable : (prefixWord ++ tailWord_4162042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162042).length < 2 ^ (prefixWord ++ tailWord_4162042).sum := by decide
  have hdescent : baseEnd_4162042 < baseStart_4162042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162049 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4162049 : Nat := 118140960795 + 4162049 * 2 ^ 59
def prefixEnd_4162049 : Nat := 4983230072969 + 3 ^ 40 * 4162049 * 2
def baseEnd_4162049 : Nat := 712377214854963899282197

theorem tailTrace_4162049 : CollatzResearch.WordTrace tailWord_4162049 prefixEnd_4162049 712377214854963899282197 := by
  unfold tailWord_4162049
  simp only [CollatzResearch.WordTrace]
  refine ⟨151802398098614769222929201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101201598732409846148619467 151802398098614769222929201)
  ·
    refine ⟨113851798573961076917196901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151802398098614769222929201 113851798573961076917196901)
    ·
      refine ⟨21347212232617701921974419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113851798573961076917196901 21347212232617701921974419)
      ·
        refine ⟨32020818348926552882961629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347212232617701921974419 32020818348926552882961629)
        ·
          refine ⟨12007806880847457331110611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32020818348926552882961629 12007806880847457331110611)
          ·
            refine ⟨18011710321271185996665917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12007806880847457331110611 18011710321271185996665917)
            ·
              refine ⟨6754391370476694748749719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18011710321271185996665917 6754391370476694748749719)
              ·
                refine ⟨10131587055715042123124579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754391370476694748749719 10131587055715042123124579)
                ·
                  refine ⟨15197380583572563184686869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10131587055715042123124579 15197380583572563184686869)
                  ·
                    refine ⟨712377214854963899282197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15197380583572563184686869 712377214854963899282197)
                    ·
                      rfl

theorem cell23_4162049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4162049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162049 prefixEnd_4162049 := by exact prefixLift 4162049
  have htrace : WordTrace (prefixWord ++ tailWord_4162049) baseStart_4162049 baseEnd_4162049 := by
    simpa [prefixWord, tailWord_4162049, baseEnd_4162049] using wordTrace_append hprefix tailTrace_4162049
  have hstable : (prefixWord ++ tailWord_4162049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162049).length < 2 ^ (prefixWord ++ tailWord_4162049).sum := by decide
  have hdescent : baseEnd_4162049 < baseStart_4162049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162076 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4162076 : Nat := 118140960795 + 4162076 * 2 ^ 59
def prefixEnd_4162076 : Nat := 4983230072969 + 3 ^ 40 * 4162076 * 2
def baseEnd_4162076 : Nat := 2137145508542563092208967

theorem tailTrace_4162076 : CollatzResearch.WordTrace tailWord_4162076 prefixEnd_4162076 2137145508542563092208967 := by
  unfold tailWord_4162076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75901691434758476417081041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101202255246344635222774721 75901691434758476417081041)
  ·
    refine ⟨56926268576068857312810781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75901691434758476417081041 56926268576068857312810781)
    ·
      refine ⟨21347350716025821492304043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56926268576068857312810781 21347350716025821492304043)
      ·
        refine ⟨32021026074038732238456065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21347350716025821492304043 32021026074038732238456065)
        ·
          refine ⟨24015769555529049178842049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32021026074038732238456065 24015769555529049178842049)
          ·
            refine ⟨18011827166646786884131537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24015769555529049178842049 18011827166646786884131537)
            ·
              refine ⟨13508870374985090163098653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18011827166646786884131537 13508870374985090163098653)
              ·
                refine ⟨5065826390619408811161995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13508870374985090163098653 5065826390619408811161995)
                ·
                  refine ⟨7598739585929113216742993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5065826390619408811161995 7598739585929113216742993)
                  ·
                    refine ⟨5699054689446834912557245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7598739585929113216742993 5699054689446834912557245)
                    ·
                      refine ⟨2137145508542563092208967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699054689446834912557245 2137145508542563092208967)
                      ·
                        rfl

theorem cell23_4162076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4162076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162076 prefixEnd_4162076 := by exact prefixLift 4162076
  have htrace : WordTrace (prefixWord ++ tailWord_4162076) baseStart_4162076 baseEnd_4162076 := by
    simpa [prefixWord, tailWord_4162076, baseEnd_4162076] using wordTrace_append hprefix tailTrace_4162076
  have hstable : (prefixWord ++ tailWord_4162076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162076).length < 2 ^ (prefixWord ++ tailWord_4162076).sum := by decide
  have hdescent : baseEnd_4162076 < baseStart_4162076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162090 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4162090 : Nat := 118140960795 + 4162090 * 2 ^ 59
def prefixEnd_4162090 : Nat := 4983230072969 + 3 ^ 40 * 4162090 * 2
def baseEnd_4162090 : Nat := 2137152697271726037433903

theorem tailTrace_4162090 : CollatzResearch.WordTrace tailWord_4162090 prefixEnd_4162090 2137152697271726037433903 := by
  unfold tailWord_4162090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950973372866558306292931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101202595660977488816781149 37950973372866558306292931)
  ·
    refine ⟨56926460059299837459439397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37950973372866558306292931 56926460059299837459439397)
    ·
      refine ⟨10673711261118719523644887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56926460059299837459439397 10673711261118719523644887)
      ·
        refine ⟨16010566891678079285467331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673711261118719523644887 16010566891678079285467331)
        ·
          refine ⟨24015850337517118928200997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010566891678079285467331 24015850337517118928200997)
          ·
            refine ⟨4502971938284459799037687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24015850337517118928200997 4502971938284459799037687)
            ·
              refine ⟨6754457907426689698556531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4502971938284459799037687 6754457907426689698556531)
              ·
                refine ⟨10131686861140034547834797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754457907426689698556531 10131686861140034547834797)
                ·
                  refine ⟨3799382572927512955438049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10131686861140034547834797 3799382572927512955438049)
                  ·
                    refine ⟨2849536929695634716578537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3799382572927512955438049 2849536929695634716578537)
                    ·
                      refine ⟨2137152697271726037433903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849536929695634716578537 2137152697271726037433903)
                      ·
                        rfl

theorem cell23_4162090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4162090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162090 prefixEnd_4162090 := by exact prefixLift 4162090
  have htrace : WordTrace (prefixWord ++ tailWord_4162090) baseStart_4162090 baseEnd_4162090 := by
    simpa [prefixWord, tailWord_4162090, baseEnd_4162090] using wordTrace_append hprefix tailTrace_4162090
  have hstable : (prefixWord ++ tailWord_4162090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162090).length < 2 ^ (prefixWord ++ tailWord_4162090).sum := by decide
  have hdescent : baseEnd_4162090 < baseStart_4162090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162100 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4162100 : Nat := 118140960795 + 4162100 * 2 ^ 59
def prefixEnd_4162100 : Nat := 4983230072969 + 3 ^ 40 * 4162100 * 2
def baseEnd_4162100 : Nat := 712385944026090332769619

theorem tailTrace_4162100 : CollatzResearch.WordTrace tailWord_4162100 prefixEnd_4162100 712385944026090332769619 := by
  unfold tailWord_4162100
  simp only [CollatzResearch.WordTrace]
  refine ⟨75902129110715002466517877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101202838814286669955357169 75902129110715002466517877)
  ·
    refine ⟨7115824604129531481236051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75902129110715002466517877 7115824604129531481236051)
    ·
      refine ⟨10673736906194297221854077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7115824604129531481236051 10673736906194297221854077)
      ·
        refine ⟨4002651339822861458195279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10673736906194297221854077 4002651339822861458195279)
        ·
          refine ⟨6003977009734292187292919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002651339822861458195279 6003977009734292187292919)
          ·
            refine ⟨9005965514601438280939379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003977009734292187292919 9005965514601438280939379)
            ·
              refine ⟨13508948271902157421409069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9005965514601438280939379 13508948271902157421409069)
              ·
                refine ⟨5065855601963309033028401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13508948271902157421409069 5065855601963309033028401)
                ·
                  refine ⟨3799391701472481774771301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065855601963309033028401 3799391701472481774771301)
                  ·
                    refine ⟨712385944026090332769619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799391701472481774771301 712385944026090332769619)
                    ·
                      rfl

theorem cell23_4162100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4162100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162100 prefixEnd_4162100 := by exact prefixLift 4162100
  have htrace : WordTrace (prefixWord ++ tailWord_4162100) baseStart_4162100 baseEnd_4162100 := by
    simpa [prefixWord, tailWord_4162100, baseEnd_4162100] using wordTrace_append hprefix tailTrace_4162100
  have hstable : (prefixWord ++ tailWord_4162100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162100).length < 2 ^ (prefixWord ++ tailWord_4162100).sum := by decide
  have hdescent : baseEnd_4162100 < baseStart_4162100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162140 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4162140 : Nat := 118140960795 + 4162140 * 2 ^ 59
def prefixEnd_4162140 : Nat := 4983230072969 + 3 ^ 40 * 4162140 * 2
def baseEnd_4162140 : Nat := 2137178371304450841808673

theorem tailTrace_4162140 : CollatzResearch.WordTrace tailWord_4162140 prefixEnd_4162140 2137178371304450841808673 := by
  unfold tailWord_4162140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75902858570642545882245937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101203811427523394509661249 75902858570642545882245937)
  ·
    refine ⟨56927143927981909411684453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75902858570642545882245937 56927143927981909411684453)
    ·
      refine ⟨10673839486496608014690835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56927143927981909411684453 10673839486496608014690835)
      ·
        refine ⟨16010759229744912022036253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673839486496608014690835 16010759229744912022036253)
        ·
          refine ⟨6004034711154342008263595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16010759229744912022036253 6004034711154342008263595)
          ·
            refine ⟨9006052066731513012395393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004034711154342008263595 9006052066731513012395393)
            ·
              refine ⟨6754539050048634759296545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9006052066731513012395393 6754539050048634759296545)
              ·
                refine ⟨5065904287536476069472409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6754539050048634759296545 5065904287536476069472409)
                ·
                  refine ⟨3799428215652357052104307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5065904287536476069472409 3799428215652357052104307)
                  ·
                    refine ⟨5699142323478535578156461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799428215652357052104307 5699142323478535578156461)
                    ·
                      refine ⟨2137178371304450841808673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699142323478535578156461 2137178371304450841808673)
                      ·
                        rfl

theorem cell23_4162140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4162140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162140 prefixEnd_4162140 := by exact prefixLift 4162140
  have htrace : WordTrace (prefixWord ++ tailWord_4162140) baseStart_4162140 baseEnd_4162140 := by
    simpa [prefixWord, tailWord_4162140, baseEnd_4162140] using wordTrace_append hprefix tailTrace_4162140
  have hstable : (prefixWord ++ tailWord_4162140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162140).length < 2 ^ (prefixWord ++ tailWord_4162140).sum := by decide
  have hdescent : baseEnd_4162140 < baseStart_4162140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162169 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 7]
def baseStart_4162169 : Nat := 118140960795 + 4162169 * 2 ^ 59
def prefixEnd_4162169 : Nat := 4983230072969 + 3 ^ 40 * 4162169 * 2
def baseEnd_4162169 : Nat := 237465918027047914260671

theorem tailTrace_4162169 : CollatzResearch.WordTrace tailWord_4162169 prefixEnd_4162169 237465918027047914260671 := by
  unfold tailWord_4162169
  simp only [CollatzResearch.WordTrace]
  refine ⟨151806774858180029717297561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101204516572120019811531707 151806774858180029717297561)
  ·
    refine ⟨113855081143635022287973171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151806774858180029717297561 113855081143635022287973171)
    ·
      refine ⟨170782621715452533431959757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113855081143635022287973171 170782621715452533431959757)
      ·
        refine ⟨64043483143294700036984909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170782621715452533431959757 64043483143294700036984909)
        ·
          refine ⟨24016306178735512513869341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64043483143294700036984909 24016306178735512513869341)
          ·
            refine ⟨9006114817025817192701003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24016306178735512513869341 9006114817025817192701003)
            ·
              refine ⟨13509172225538725789051505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006114817025817192701003 13509172225538725789051505)
              ·
                refine ⟨10131879169154044341788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13509172225538725789051505 10131879169154044341788629)
                ·
                  refine ⟨237465918027047914260671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10131879169154044341788629 237465918027047914260671)
                  ·
                    rfl

theorem cell23_4162169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_4162169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162169 prefixEnd_4162169 := by exact prefixLift 4162169
  have htrace : WordTrace (prefixWord ++ tailWord_4162169) baseStart_4162169 baseEnd_4162169 := by
    simpa [prefixWord, tailWord_4162169, baseEnd_4162169] using wordTrace_append hprefix tailTrace_4162169
  have hstable : (prefixWord ++ tailWord_4162169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162169).length < 2 ^ (prefixWord ++ tailWord_4162169).sum := by decide
  have hdescent : baseEnd_4162169 < baseStart_4162169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162199 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 4, 5]
def baseStart_4162199 : Nat := 118140960795 + 4162199 * 2 ^ 59
def prefixEnd_4162199 : Nat := 4983230072969 + 3 ^ 40 * 4162199 * 2
def baseEnd_4162199 : Nat := 712402888887688703656967

theorem tailTrace_4162199 : CollatzResearch.WordTrace tailWord_4162199 prefixEnd_4162199 712402888887688703656967 := by
  unfold tailWord_4162199
  simp only [CollatzResearch.WordTrace]
  refine ⟨151807869048071344840889651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101205246032047563227259767 151807869048071344840889651)
  ·
    refine ⟨227711803572107017261334477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151807869048071344840889651 227711803572107017261334477)
    ·
      refine ⟨85391926339540131473000429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227711803572107017261334477 85391926339540131473000429)
      ·
        refine ⟨32021972377327549302375161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85391926339540131473000429 32021972377327549302375161)
        ·
          refine ⟨24016479282995661976781371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32021972377327549302375161 24016479282995661976781371)
          ·
            refine ⟨36024718924493492965172057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24016479282995661976781371 36024718924493492965172057)
            ·
              refine ⟨27018539193370119723879043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36024718924493492965172057 27018539193370119723879043)
              ·
                refine ⟨40527808790055179585818565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27018539193370119723879043 40527808790055179585818565)
                ·
                  refine ⟨7598964148135346172340981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40527808790055179585818565 7598964148135346172340981)
                  ·
                    refine ⟨712402888887688703656967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7598964148135346172340981 712402888887688703656967)
                    ·
                      rfl

theorem cell23_4162199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_4162199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162199 prefixEnd_4162199 := by exact prefixLift 4162199
  have htrace : WordTrace (prefixWord ++ tailWord_4162199) baseStart_4162199 baseEnd_4162199 := by
    simpa [prefixWord, tailWord_4162199, baseEnd_4162199] using wordTrace_append hprefix tailTrace_4162199
  have hstable : (prefixWord ++ tailWord_4162199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162199).length < 2 ^ (prefixWord ++ tailWord_4162199).sum := by decide
  have hdescent : baseEnd_4162199 < baseStart_4162199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162236 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4162236 : Nat := 118140960795 + 4162236 * 2 ^ 59
def prefixEnd_4162236 : Nat := 4983230072969 + 3 ^ 40 * 4162236 * 2
def baseEnd_4162236 : Nat := 2137227665447282466208231

theorem tailTrace_4162236 : CollatzResearch.WordTrace tailWord_4162236 prefixEnd_4162236 2137227665447282466208231 := by
  unfold tailWord_4162236
  simp only [CollatzResearch.WordTrace]
  refine ⟨75904609274468650079993281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101206145699291533439991041 75904609274468650079993281)
  ·
    refine ⟨56928456955851487559994961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75904609274468650079993281 56928456955851487559994961)
    ·
      refine ⟨42696342716888615669996221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56928456955851487559994961 42696342716888615669996221)
      ·
        refine ⟨16011128518833230876248583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42696342716888615669996221 16011128518833230876248583)
        ·
          refine ⟨24016692778249846314372875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16011128518833230876248583 24016692778249846314372875)
          ·
            refine ⟨36025039167374769471559313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24016692778249846314372875 36025039167374769471559313)
            ·
              refine ⟨27018779375531077103669485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36025039167374769471559313 27018779375531077103669485)
              ·
                refine ⟨10132042265824153913876057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27018779375531077103669485 10132042265824153913876057)
                ·
                  refine ⟨7599031699368115435407043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132042265824153913876057 7599031699368115435407043)
                  ·
                    refine ⟨11398547549052173153110565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7599031699368115435407043 11398547549052173153110565)
                    ·
                      refine ⟨2137227665447282466208231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11398547549052173153110565 2137227665447282466208231)
                      ·
                        rfl

theorem cell23_4162236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4162236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162236 prefixEnd_4162236 := by exact prefixLift 4162236
  have htrace : WordTrace (prefixWord ++ tailWord_4162236) baseStart_4162236 baseEnd_4162236 := by
    simpa [prefixWord, tailWord_4162236, baseEnd_4162236] using wordTrace_append hprefix tailTrace_4162236
  have hstable : (prefixWord ++ tailWord_4162236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162236).length < 2 ^ (prefixWord ++ tailWord_4162236).sum := by decide
  have hdescent : baseEnd_4162236 < baseStart_4162236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162263 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 3, 4]
def baseStart_4162263 : Nat := 118140960795 + 4162263 * 2 ^ 59
def prefixEnd_4162263 : Nat := 4983230072969 + 3 ^ 40 * 4162263 * 2
def baseEnd_4162263 : Nat := 712413843141651286856869

theorem tailTrace_4162263 : CollatzResearch.WordTrace tailWord_4162263 prefixEnd_4162263 712413843141651286856869 := by
  unfold tailWord_4162263
  simp only [CollatzResearch.WordTrace]
  refine ⟨151810203319839483771219443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101206802213226322514146295 151810203319839483771219443)
  ·
    refine ⟨227715304979759225656829165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151810203319839483771219443 227715304979759225656829165)
    ·
      refine ⟨85393239367409709621310937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227715304979759225656829165 85393239367409709621310937)
      ·
        refine ⟨64044929525557282215983203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85393239367409709621310937 64044929525557282215983203)
        ·
          refine ⟨96067394288335923323974805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64044929525557282215983203 96067394288335923323974805)
          ·
            refine ⟨4503159107265746405811319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96067394288335923323974805 4503159107265746405811319)
            ·
              refine ⟨6754738660898619608716979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503159107265746405811319 6754738660898619608716979)
              ·
                refine ⟨10132107991347929413075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754738660898619608716979 10132107991347929413075469)
                ·
                  refine ⟨3799540496755473529903301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10132107991347929413075469 3799540496755473529903301)
                  ·
                    refine ⟨712413843141651286856869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799540496755473529903301 712413843141651286856869)
                    ·
                      rfl

theorem cell23_4162263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_4162263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162263 prefixEnd_4162263 := by exact prefixLift 4162263
  have htrace : WordTrace (prefixWord ++ tailWord_4162263) baseStart_4162263 baseEnd_4162263 := by
    simpa [prefixWord, tailWord_4162263, baseEnd_4162263] using wordTrace_append hprefix tailTrace_4162263
  have hstable : (prefixWord ++ tailWord_4162263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162263).length < 2 ^ (prefixWord ++ tailWord_4162263).sum := by decide
  have hdescent : baseEnd_4162263 < baseStart_4162263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162276 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 6]
def baseStart_4162276 : Nat := 118140960795 + 4162276 * 2 ^ 59
def prefixEnd_4162276 : Nat := 4983230072969 + 3 ^ 40 * 4162276 * 2
def baseEnd_4162276 : Nat := 237472022741495812189783

theorem tailTrace_4162276 : CollatzResearch.WordTrace tailWord_4162276 prefixEnd_4162276 237472022741495812189783 := by
  unfold tailWord_4162276
  simp only [CollatzResearch.WordTrace]
  refine ⟨75905338734396193495721341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101207118312528257994295121 75905338734396193495721341)
  ·
    refine ⟨28464502025398572560895503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75905338734396193495721341 28464502025398572560895503)
    ·
      refine ⟨42696753038097858841343255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28464502025398572560895503 42696753038097858841343255)
      ·
        refine ⟨64045129557146788262014883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42696753038097858841343255 64045129557146788262014883)
        ·
          refine ⟨96067694335720182393022325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64045129557146788262014883 96067694335720182393022325)
          ·
            refine ⟨9006346343973767099345843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96067694335720182393022325 9006346343973767099345843)
            ·
              refine ⟨13509519515960650649018765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006346343973767099345843 13509519515960650649018765)
              ·
                refine ⟨5066069818485243993382037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13509519515960650649018765 5066069818485243993382037)
                ·
                  refine ⟨237472022741495812189783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5066069818485243993382037 237472022741495812189783)
                  ·
                    rfl

theorem cell23_4162276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_4162276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162276 prefixEnd_4162276 := by exact prefixLift 4162276
  have htrace : WordTrace (prefixWord ++ tailWord_4162276) baseStart_4162276 baseEnd_4162276 := by
    simpa [prefixWord, tailWord_4162276, baseEnd_4162276] using wordTrace_append hprefix tailTrace_4162276
  have hstable : (prefixWord ++ tailWord_4162276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162276).length < 2 ^ (prefixWord ++ tailWord_4162276).sum := by decide
  have hdescent : baseEnd_4162276 < baseStart_4162276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162313 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 2, 3, 2]
def baseStart_4162313 : Nat := 118140960795 + 4162313 * 2 ^ 59
def prefixEnd_4162313 : Nat := 4983230072969 + 3 ^ 40 * 4162313 * 2
def baseEnd_4162313 : Nat := 2137267203457678664945377

theorem tailTrace_4162313 : CollatzResearch.WordTrace tailWord_4162313 prefixEnd_4162313 2137267203457678664945377 := by
  unfold tailWord_4162313
  simp only [CollatzResearch.WordTrace]
  refine ⟨151812026969658342310539593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101208017979772228207026395 151812026969658342310539593)
  ·
    refine ⟨113859020227243756732904695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151812026969658342310539593 113859020227243756732904695)
    ·
      refine ⟨170788530340865635099357043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113859020227243756732904695 170788530340865635099357043)
      ·
        refine ⟨256182795511298452649035565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170788530340865635099357043 256182795511298452649035565)
        ·
          refine ⟨96068548316736919743388337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256182795511298452649035565 96068548316736919743388337)
          ·
            refine ⟨72051411237552689807541253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96068548316736919743388337 72051411237552689807541253)
            ·
              refine ⟨13509639607041129338913985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72051411237552689807541253 13509639607041129338913985)
              ·
                refine ⟨10132229705280847004185489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13509639607041129338913985 10132229705280847004185489)
                ·
                  refine ⟨7599172278960635253139117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132229705280847004185489 7599172278960635253139117)
                  ·
                    refine ⟨2849689604610238219927169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7599172278960635253139117 2849689604610238219927169)
                    ·
                      refine ⟨2137267203457678664945377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849689604610238219927169 2137267203457678664945377)
                      ·
                        rfl

theorem cell23_4162313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3, 2].length) (baseStart_4162313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162313 prefixEnd_4162313 := by exact prefixLift 4162313
  have htrace : WordTrace (prefixWord ++ tailWord_4162313) baseStart_4162313 baseEnd_4162313 := by
    simpa [prefixWord, tailWord_4162313, baseEnd_4162313] using wordTrace_append hprefix tailTrace_4162313
  have hstable : (prefixWord ++ tailWord_4162313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162313).length < 2 ^ (prefixWord ++ tailWord_4162313).sum := by decide
  have hdescent : baseEnd_4162313 < baseStart_4162313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162319 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 6]
def baseStart_4162319 : Nat := 118140960795 + 4162319 * 2 ^ 59
def prefixEnd_4162319 : Nat := 4983230072969 + 3 ^ 40 * 4162319 * 2
def baseEnd_4162319 : Nat := 712423428113868547156783

theorem tailTrace_4162319 : CollatzResearch.WordTrace tailWord_4162319 prefixEnd_4162319 712423428113868547156783 := by
  unfold tailWord_4162319
  simp only [CollatzResearch.WordTrace]
  refine ⟨151812245807636605335258011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101208163871757736890172007 151812245807636605335258011)
  ·
    refine ⟨227718368711454908002887017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151812245807636605335258011 227718368711454908002887017)
    ·
      refine ⟨170788776533591181002165263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227718368711454908002887017 170788776533591181002165263)
      ·
        refine ⟨256183164800386771503247895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170788776533591181002165263 256183164800386771503247895)
        ·
          refine ⟨384274747200580157254871843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256183164800386771503247895 384274747200580157254871843)
          ·
            refine ⟨576412120800870235882307765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384274747200580157254871843 576412120800870235882307765)
            ·
              refine ⟨54038636325081584613966353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 576412120800870235882307765 54038636325081584613966353)
              ·
                refine ⟨40528977243811188460474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54038636325081584613966353 40528977243811188460474765)
                ·
                  refine ⟨15198366466429195672678037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40528977243811188460474765 15198366466429195672678037)
                  ·
                    refine ⟨712423428113868547156783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15198366466429195672678037 712423428113868547156783)
                    ·
                      rfl

theorem cell23_4162319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_4162319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162319 prefixEnd_4162319 := by exact prefixLift 4162319
  have htrace : WordTrace (prefixWord ++ tailWord_4162319) baseStart_4162319 baseEnd_4162319 := by
    simpa [prefixWord, tailWord_4162319, baseEnd_4162319] using wordTrace_append hprefix tailTrace_4162319
  have hstable : (prefixWord ++ tailWord_4162319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162319).length < 2 ^ (prefixWord ++ tailWord_4162319).sum := by decide
  have hdescent : baseEnd_4162319 < baseStart_4162319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162336 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_4162336 : Nat := 118140960795 + 4162336 * 2 ^ 59
def prefixEnd_4162336 : Nat := 4983230072969 + 3 ^ 40 * 4162336 * 2
def baseEnd_4162336 : Nat := 712426337837577358319257

theorem tailTrace_4162336 : CollatzResearch.WordTrace tailWord_4162336 prefixEnd_4162336 712426337837577358319257 := by
  unfold tailWord_4162336
  simp only [CollatzResearch.WordTrace]
  refine ⟨75906432924287508619313431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101208577232383344825751241 75906432924287508619313431)
  ·
    refine ⟨113859649386431262928970147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75906432924287508619313431 113859649386431262928970147)
    ·
      refine ⟨170789474079646894393455221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113859649386431262928970147 170789474079646894393455221)
      ·
        refine ⟨16011513194966896349386427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170789474079646894393455221 16011513194966896349386427)
        ·
          refine ⟨24017269792450344524079641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16011513194966896349386427 24017269792450344524079641)
          ·
            refine ⟨18012952344337758393059731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24017269792450344524079641 18012952344337758393059731)
            ·
              refine ⟨27019428516506637589589597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18012952344337758393059731 27019428516506637589589597)
              ·
                refine ⟨10132285693689989096096099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27019428516506637589589597 10132285693689989096096099)
                ·
                  refine ⟨15198428540534983644144149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10132285693689989096096099 15198428540534983644144149)
                  ·
                    refine ⟨712426337837577358319257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15198428540534983644144149 712426337837577358319257)
                    ·
                      rfl

theorem cell23_4162336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_4162336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162336 prefixEnd_4162336 := by exact prefixLift 4162336
  have htrace : WordTrace (prefixWord ++ tailWord_4162336) baseStart_4162336 baseEnd_4162336 := by
    simpa [prefixWord, tailWord_4162336, baseEnd_4162336] using wordTrace_append hprefix tailTrace_4162336
  have hstable : (prefixWord ++ tailWord_4162336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162336).length < 2 ^ (prefixWord ++ tailWord_4162336).sum := by decide
  have hdescent : baseEnd_4162336 < baseStart_4162336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162377 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 1, 2, 2]
def baseStart_4162377 : Nat := 118140960795 + 4162377 * 2 ^ 59
def prefixEnd_4162377 : Nat := 4983230072969 + 3 ^ 40 * 4162377 * 2
def baseEnd_4162377 : Nat := 2137300066219566414545083

theorem tailTrace_4162377 : CollatzResearch.WordTrace tailWord_4162377 prefixEnd_4162377 2137300066219566414545083 := by
  unfold tailWord_4162377
  simp only [CollatzResearch.WordTrace]
  refine ⟨151814361241426481240869385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101209574160950987493912923 151814361241426481240869385)
  ·
    refine ⟨113860770931069860930652039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151814361241426481240869385 113860770931069860930652039)
    ·
      refine ⟨170791156396604791395978059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113860770931069860930652039 170791156396604791395978059)
      ·
        refine ⟨256186734594907187093967089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170791156396604791395978059 256186734594907187093967089)
        ·
          refine ⟨192140050946180390320475317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256186734594907187093967089 192140050946180390320475317)
          ·
            refine ⟨18013129776204411592544561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192140050946180390320475317 18013129776204411592544561)
            ·
              refine ⟨13509847332153308694408421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18013129776204411592544561 13509847332153308694408421)
              ·
                refine ⟨2533096374778745380201579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13509847332153308694408421 2533096374778745380201579)
                ·
                  refine ⟨3799644562168118070302369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533096374778745380201579 3799644562168118070302369)
                  ·
                    refine ⟨2849733421626088552726777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3799644562168118070302369 2849733421626088552726777)
                    ·
                      refine ⟨2137300066219566414545083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2849733421626088552726777 2137300066219566414545083)
                      ·
                        rfl

theorem cell23_4162377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 2, 2].length) (baseStart_4162377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162377 prefixEnd_4162377 := by exact prefixLift 4162377
  have htrace : WordTrace (prefixWord ++ tailWord_4162377) baseStart_4162377 baseEnd_4162377 := by
    simpa [prefixWord, tailWord_4162377, baseEnd_4162377] using wordTrace_append hprefix tailTrace_4162377
  have hstable : (prefixWord ++ tailWord_4162377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162377).length < 2 ^ (prefixWord ++ tailWord_4162377).sum := by decide
  have hdescent : baseEnd_4162377 < baseStart_4162377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162393 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_4162393 : Nat := 118140960795 + 4162393 * 2 ^ 59
def prefixEnd_4162393 : Nat := 4983230072969 + 3 ^ 40 * 4162393 * 2
def baseEnd_4162393 : Nat := 2137308281910038351945009

theorem tailTrace_4162393 : CollatzResearch.WordTrace tailWord_4162393 prefixEnd_4162393 2137308281910038351945009 := by
  unfold tailWord_4162393
  simp only [CollatzResearch.WordTrace]
  refine ⟨151814944809368515973451833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101209963206245677315634555 151814944809368515973451833)
  ·
    refine ⟨113861208607026386980088875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151814944809368515973451833 113861208607026386980088875)
    ·
      refine ⟨170791812910539580470133313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113861208607026386980088875 170791812910539580470133313)
      ·
        refine ⟨128093859682904685352599985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170791812910539580470133313 128093859682904685352599985)
        ·
          refine ⟨96070394762178514014449989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128093859682904685352599985 96070394762178514014449989)
          ·
            refine ⟨18013199017908471377709373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96070394762178514014449989 18013199017908471377709373)
            ·
              refine ⟨6754949631715676766641015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18013199017908471377709373 6754949631715676766641015)
              ·
                refine ⟨10132424447573515149961523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6754949631715676766641015 10132424447573515149961523)
                ·
                  refine ⟨15198636671360272724942285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10132424447573515149961523 15198636671360272724942285)
                  ·
                    refine ⟨5699488751760102271853357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15198636671360272724942285 5699488751760102271853357)
                    ·
                      refine ⟨2137308281910038351945009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699488751760102271853357 2137308281910038351945009)
                      ·
                        rfl

theorem cell23_4162393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_4162393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162393 prefixEnd_4162393 := by exact prefixLift 4162393
  have htrace : WordTrace (prefixWord ++ tailWord_4162393) baseStart_4162393 baseEnd_4162393 := by
    simpa [prefixWord, tailWord_4162393, baseEnd_4162393] using wordTrace_append hprefix tailTrace_4162393
  have hstable : (prefixWord ++ tailWord_4162393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162393).length < 2 ^ (prefixWord ++ tailWord_4162393).sum := by decide
  have hdescent : baseEnd_4162393 < baseStart_4162393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162436 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4162436 : Nat := 118140960795 + 4162436 * 2 ^ 59
def prefixEnd_4162436 : Nat := 4983230072969 + 3 ^ 40 * 4162436 * 2
def baseEnd_4162436 : Nat := 2137330361578181683707311

theorem tailTrace_4162436 : CollatzResearch.WordTrace tailWord_4162436 prefixEnd_4162436 2137330361578181683707311 := by
  unfold tailWord_4162436
  simp only [CollatzResearch.WordTrace]
  refine ⟨75908256574106367158633581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101211008765475156211511441 75908256574106367158633581)
  ·
    refine ⟨28465596215289887684487593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75908256574106367158633581 28465596215289887684487593)
    ·
      refine ⟨21349197161467415763365695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28465596215289887684487593 21349197161467415763365695)
      ·
        refine ⟨32023795742201123645048543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21349197161467415763365695 32023795742201123645048543)
        ·
          refine ⟨48035693613301685467572815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32023795742201123645048543 48035693613301685467572815)
          ·
            refine ⟨72053540419952528201359223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48035693613301685467572815 72053540419952528201359223)
            ·
              refine ⟨108080310629928792302038835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72053540419952528201359223 108080310629928792302038835)
              ·
                refine ⟨162120465944893188453058253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108080310629928792302038835 162120465944893188453058253)
                ·
                  refine ⟨60795174729334945669896845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162120465944893188453058253 60795174729334945669896845)
                  ·
                    refine ⟨22798190523500604626211317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60795174729334945669896845 22798190523500604626211317)
                    ·
                      refine ⟨2137330361578181683707311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22798190523500604626211317 2137330361578181683707311)
                      ·
                        rfl

theorem cell23_4162436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4162436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162436 prefixEnd_4162436 := by exact prefixLift 4162436
  have htrace : WordTrace (prefixWord ++ tailWord_4162436) baseStart_4162436 baseEnd_4162436 := by
    simpa [prefixWord, tailWord_4162436, baseEnd_4162436] using wordTrace_append hprefix tailTrace_4162436
  have hstable : (prefixWord ++ tailWord_4162436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162436).length < 2 ^ (prefixWord ++ tailWord_4162436).sum := by decide
  have hdescent : baseEnd_4162436 < baseStart_4162436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
