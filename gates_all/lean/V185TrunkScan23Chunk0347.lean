import V185TrunkScan23Chunk0346

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2052555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_2052555 : Nat := 118140960795 + 2052555 * 2 ^ 59
def prefixEnd_2052555 : Nat := 4983230072969 + 3 ^ 40 * 2052555 * 2
def baseEnd_2052555 : Nat := 1053947284789322102822977

theorem tailTrace_2052555 : CollatzResearch.WordTrace tailWord_2052555 prefixEnd_2052555 1053947284789322102822977 := by
  unfold tailWord_2052555
  simp only [CollatzResearch.WordTrace]
  refine ⟨74862831078951258330519119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49908554052634172220346079 74862831078951258330519119)
  ·
    refine ⟨112294246618426887495778679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74862831078951258330519119 112294246618426887495778679)
    ·
      refine ⟨168441369927640331243668019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112294246618426887495778679 168441369927640331243668019)
      ·
        refine ⟨252662054891460496865502029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168441369927640331243668019 252662054891460496865502029)
        ·
          refine ⟨94748270584297686324563261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252662054891460496865502029 94748270584297686324563261)
          ·
            refine ⟨35530601469111632371711223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94748270584297686324563261 35530601469111632371711223)
            ·
              refine ⟨53295902203667448557566835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35530601469111632371711223 53295902203667448557566835)
              ·
                refine ⟨79943853305501172836350253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53295902203667448557566835 79943853305501172836350253)
                ·
                  refine ⟨29978944989562939813631345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79943853305501172836350253 29978944989562939813631345)
                  ·
                    refine ⟨22484208742172204860223509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29978944989562939813631345 22484208742172204860223509)
                    ·
                      refine ⟨1053947284789322102822977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22484208742172204860223509 1053947284789322102822977)
                      ·
                        rfl

theorem cell23_2052555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_2052555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052555 prefixEnd_2052555 := by exact prefixLift 2052555
  have htrace : WordTrace (prefixWord ++ tailWord_2052555) baseStart_2052555 baseEnd_2052555 := by
    simpa [prefixWord, tailWord_2052555, baseEnd_2052555] using wordTrace_append hprefix tailTrace_2052555
  have hstable : (prefixWord ++ tailWord_2052555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052555).length < 2 ^ (prefixWord ++ tailWord_2052555).sum := by decide
  have hdescent : baseEnd_2052555 < baseStart_2052555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052566 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2052566 : Nat := 118140960795 + 2052566 * 2 ^ 59
def prefixEnd_2052566 : Nat := 4983230072969 + 3 ^ 40 * 2052566 * 2
def baseEnd_2052566 : Nat := 1053952933076521559785427

theorem tailTrace_2052566 : CollatzResearch.WordTrace tailWord_2052566 prefixEnd_2052566 1053952933076521559785427 := by
  unfold tailWord_2052566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4678952017619462950573097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49908821521274271472779701 4678952017619462950573097)
  ·
    refine ⟨3509214013214597212929823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4678952017619462950573097 3509214013214597212929823)
    ·
      refine ⟨5263821019821895819394735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509214013214597212929823 5263821019821895819394735)
      ·
        refine ⟨7895731529732843729092103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263821019821895819394735 7895731529732843729092103)
        ·
          refine ⟨11843597294599265593638155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895731529732843729092103 11843597294599265593638155)
          ·
            refine ⟨17765395941898898390457233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843597294599265593638155 17765395941898898390457233)
            ·
              refine ⟨13324046956424173792842925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17765395941898898390457233 13324046956424173792842925)
              ·
                refine ⟨4996517608659065172316097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324046956424173792842925 4996517608659065172316097)
                ·
                  refine ⟨3747388206494298879237073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996517608659065172316097 3747388206494298879237073)
                  ·
                    refine ⟨2810541154870724159427805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3747388206494298879237073 2810541154870724159427805)
                    ·
                      refine ⟨1053952933076521559785427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810541154870724159427805 1053952933076521559785427)
                      ·
                        rfl

theorem cell23_2052566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2052566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052566 prefixEnd_2052566 := by exact prefixLift 2052566
  have htrace : WordTrace (prefixWord ++ tailWord_2052566) baseStart_2052566 baseEnd_2052566 := by
    simpa [prefixWord, tailWord_2052566, baseEnd_2052566] using wordTrace_append hprefix tailTrace_2052566
  have hstable : (prefixWord ++ tailWord_2052566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052566).length < 2 ^ (prefixWord ++ tailWord_2052566).sum := by decide
  have hdescent : baseEnd_2052566 < baseStart_2052566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052619 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4]
def baseStart_2052619 : Nat := 118140960795 + 2052619 * 2 ^ 59
def prefixEnd_2052619 : Nat := 4983230072969 + 3 ^ 40 * 2052619 * 2
def baseEnd_2052619 : Nat := 1053980147551209852422683

theorem tailTrace_2052619 : CollatzResearch.WordTrace tailWord_2052619 prefixEnd_2052619 1053980147551209852422683 := by
  unfold tailWord_2052619
  simp only [CollatzResearch.WordTrace]
  refine ⟨74865165350719397260848911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49910110233812931507232607 74865165350719397260848911)
  ·
    refine ⟨112297748026079095891273367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74865165350719397260848911 112297748026079095891273367)
    ·
      refine ⟨168446622039118643836910051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112297748026079095891273367 168446622039118643836910051)
      ·
        refine ⟨252669933058677965755365077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168446622039118643836910051 252669933058677965755365077)
        ·
          refine ⟨5921951556062764822391369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252669933058677965755365077 5921951556062764822391369)
          ·
            refine ⟨4441463667047073616793527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5921951556062764822391369 4441463667047073616793527)
            ·
              refine ⟨6662195500570610425190291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441463667047073616793527 6662195500570610425190291)
              ·
                refine ⟨9993293250855915637785437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662195500570610425190291 9993293250855915637785437)
                ·
                  refine ⟨3747484969070968364169539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9993293250855915637785437 3747484969070968364169539)
                  ·
                    refine ⟨5621227453606452546254309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3747484969070968364169539 5621227453606452546254309)
                    ·
                      refine ⟨1053980147551209852422683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5621227453606452546254309 1053980147551209852422683)
                      ·
                        rfl

theorem cell23_2052619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_2052619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052619 prefixEnd_2052619 := by exact prefixLift 2052619
  have htrace : WordTrace (prefixWord ++ tailWord_2052619) baseStart_2052619 baseEnd_2052619 := by
    simpa [prefixWord, tailWord_2052619, baseEnd_2052619] using wordTrace_append hprefix tailTrace_2052619
  have hstable : (prefixWord ++ tailWord_2052619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052619).length < 2 ^ (prefixWord ++ tailWord_2052619).sum := by decide
  have hdescent : baseEnd_2052619 < baseStart_2052619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052647 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2052647 : Nat := 118140960795 + 2052647 * 2 ^ 59
def prefixEnd_2052647 : Nat := 4983230072969 + 3 ^ 40 * 2052647 * 2
def baseEnd_2052647 : Nat := 1053994525009535742872555

theorem tailTrace_2052647 : CollatzResearch.WordTrace tailWord_2052647 prefixEnd_2052647 1053994525009535742872555 := by
  unfold tailWord_2052647
  simp only [CollatzResearch.WordTrace]
  refine ⟨74866186594617958042868195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49910791063078638695245463 74866186594617958042868195)
  ·
    refine ⟨112299279891926937064302293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74866186594617958042868195 112299279891926937064302293)
    ·
      refine ⟨2632014372467037587444585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 112299279891926937064302293 2632014372467037587444585)
      ·
        refine ⟨1974010779350278190583439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2632014372467037587444585 1974010779350278190583439)
        ·
          refine ⟨2961016169025417285875159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974010779350278190583439 2961016169025417285875159)
          ·
            refine ⟨4441524253538125928812739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961016169025417285875159 4441524253538125928812739)
            ·
              refine ⟨6662286380307188893219109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441524253538125928812739 6662286380307188893219109)
              ·
                refine ⟨1249178696307597917478583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6662286380307188893219109 1249178696307597917478583)
                ·
                  refine ⟨1873768044461396876217875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249178696307597917478583 1873768044461396876217875)
                  ·
                    refine ⟨2810652066692095314326813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1873768044461396876217875 2810652066692095314326813)
                    ·
                      refine ⟨1053994525009535742872555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810652066692095314326813 1053994525009535742872555)
                      ·
                        rfl

theorem cell23_2052647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2052647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052647 prefixEnd_2052647 := by exact prefixLift 2052647
  have htrace : WordTrace (prefixWord ++ tailWord_2052647) baseStart_2052647 baseEnd_2052647 := by
    simpa [prefixWord, tailWord_2052647, baseEnd_2052647] using wordTrace_append hprefix tailTrace_2052647
  have hstable : (prefixWord ++ tailWord_2052647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052647).length < 2 ^ (prefixWord ++ tailWord_2052647).sum := by decide
  have hdescent : baseEnd_2052647 < baseStart_2052647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052720 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3]
def baseStart_2052720 : Nat := 118140960795 + 2052720 * 2 ^ 59
def prefixEnd_2052720 : Nat := 4983230072969 + 3 ^ 40 * 2052720 * 2
def baseEnd_2052720 : Nat := 1054032009097313957259719

theorem tailTrace_2052720 : CollatzResearch.WordTrace tailWord_2052720 prefixEnd_2052720 1054032009097313957259719 := by
  unfold tailWord_2052720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37434424561676745755137807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49912566082235661006850409 37434424561676745755137807)
  ·
    refine ⟨56151636842515118632706711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37434424561676745755137807 56151636842515118632706711)
    ·
      refine ⟨84227455263772677949060067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56151636842515118632706711 84227455263772677949060067)
      ·
        refine ⟨126341182895659016923590101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84227455263772677949060067 126341182895659016923590101)
        ·
          refine ⟨2961121474117008209146643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 126341182895659016923590101 2961121474117008209146643)
          ·
            refine ⟨4441682211175512313719965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961121474117008209146643 4441682211175512313719965)
            ·
              refine ⟨1665630829190817117644987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4441682211175512313719965 1665630829190817117644987)
              ·
                refine ⟨2498446243786225676467481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1665630829190817117644987 2498446243786225676467481)
                ·
                  refine ⟨1873834682839669257350611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498446243786225676467481 1873834682839669257350611)
                  ·
                    refine ⟨2810752024259503886025917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1873834682839669257350611 2810752024259503886025917)
                    ·
                      refine ⟨1054032009097313957259719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810752024259503886025917 1054032009097313957259719)
                      ·
                        rfl

theorem cell23_2052720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 1, 3].length) (baseStart_2052720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052720 prefixEnd_2052720 := by exact prefixLift 2052720
  have htrace : WordTrace (prefixWord ++ tailWord_2052720) baseStart_2052720 baseEnd_2052720 := by
    simpa [prefixWord, tailWord_2052720, baseEnd_2052720] using wordTrace_append hprefix tailTrace_2052720
  have hstable : (prefixWord ++ tailWord_2052720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052720).length < 2 ^ (prefixWord ++ tailWord_2052720).sum := by decide
  have hdescent : baseEnd_2052720 < baseStart_2052720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052738 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2052738 : Nat := 118140960795 + 2052738 * 2 ^ 59
def prefixEnd_2052738 : Nat := 4983230072969 + 3 ^ 40 * 2052738 * 2
def baseEnd_2052738 : Nat := 1054041251749094886834637

theorem tailTrace_2052738 : CollatzResearch.WordTrace tailWord_2052738 prefixEnd_2052738 1054041251749094886834637 := by
  unfold tailWord_2052738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717376409322070146107717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49913003758192187056287245 18717376409322070146107717)
  ·
    refine ⟨3509508076747888152395197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18717376409322070146107717 3509508076747888152395197)
    ·
      refine ⟨1316065528780458057148199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3509508076747888152395197 1316065528780458057148199)
      ·
        refine ⟨1974098293170687085722299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316065528780458057148199 1974098293170687085722299)
        ·
          refine ⟨2961147439756030628583449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974098293170687085722299 2961147439756030628583449)
          ·
            refine ⟨2220860579817022971437587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961147439756030628583449 2220860579817022971437587)
            ·
              refine ⟨3331290869725534457156381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220860579817022971437587 3331290869725534457156381)
              ·
                refine ⟨1249234076147075421433643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331290869725534457156381 1249234076147075421433643)
                ·
                  refine ⟨1873851114220613132150465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249234076147075421433643 1873851114220613132150465)
                  ·
                    refine ⟨1405388335665459849112849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1873851114220613132150465 1405388335665459849112849)
                    ·
                      refine ⟨1054041251749094886834637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405388335665459849112849 1054041251749094886834637)
                      ·
                        rfl

theorem cell23_2052738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2052738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052738 prefixEnd_2052738 := by exact prefixLift 2052738
  have htrace : WordTrace (prefixWord ++ tailWord_2052738) baseStart_2052738 baseEnd_2052738 := by
    simpa [prefixWord, tailWord_2052738, baseEnd_2052738] using wordTrace_append hprefix tailTrace_2052738
  have hstable : (prefixWord ++ tailWord_2052738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052738).length < 2 ^ (prefixWord ++ tailWord_2052738).sum := by decide
  have hdescent : baseEnd_2052738 < baseStart_2052738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052746 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2052746 : Nat := 118140960795 + 2052746 * 2 ^ 59
def prefixEnd_2052746 : Nat := 4983230072969 + 3 ^ 40 * 2052746 * 2
def baseEnd_2052746 : Nat := 1054045359594330855534599

theorem tailTrace_2052746 : CollatzResearch.WordTrace tailWord_2052746 prefixEnd_2052746 1054045359594330855534599 := by
  unfold tailWord_2052746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717449355314824487680523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49913198280839531967148061 18717449355314824487680523)
  ·
    refine ⟨28076174032972236731520785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18717449355314824487680523 28076174032972236731520785)
    ·
      refine ⟨21057130524729177548640589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28076174032972236731520785 21057130524729177548640589)
      ·
        refine ⟨7896423946773441580740221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21057130524729177548640589 7896423946773441580740221)
        ·
          refine ⟨2961158980040040592777583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7896423946773441580740221 2961158980040040592777583)
          ·
            refine ⟨4441738470060060889166375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961158980040040592777583 4441738470060060889166375)
            ·
              refine ⟨6662607705090091333749563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441738470060060889166375 6662607705090091333749563)
              ·
                refine ⟨9993911557635137000624345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662607705090091333749563 9993911557635137000624345)
                ·
                  refine ⟨7495433668226352750468259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993911557635137000624345 7495433668226352750468259)
                  ·
                    refine ⟨11243150502339529125702389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495433668226352750468259 11243150502339529125702389)
                    ·
                      refine ⟨1054045359594330855534599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11243150502339529125702389 1054045359594330855534599)
                      ·
                        rfl

theorem cell23_2052746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2052746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052746 prefixEnd_2052746 := by exact prefixLift 2052746
  have htrace : WordTrace (prefixWord ++ tailWord_2052746) baseStart_2052746 baseEnd_2052746 := by
    simpa [prefixWord, tailWord_2052746, baseEnd_2052746] using wordTrace_append hprefix tailTrace_2052746
  have hstable : (prefixWord ++ tailWord_2052746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052746).length < 2 ^ (prefixWord ++ tailWord_2052746).sum := by decide
  have hdescent : baseEnd_2052746 < baseStart_2052746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052752 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_2052752 : Nat := 118140960795 + 2052752 * 2 ^ 59
def prefixEnd_2052752 : Nat := 4983230072969 + 3 ^ 40 * 2052752 * 2
def baseEnd_2052752 : Nat := 1054048440478257832059571

theorem tailTrace_2052752 : CollatzResearch.WordTrace tailWord_2052752 prefixEnd_2052752 1054048440478257832059571 := by
  unfold tailWord_2052752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37435008129618780487720255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49913344172825040650293673 37435008129618780487720255)
  ·
    refine ⟨56152512194428170731580383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37435008129618780487720255 56152512194428170731580383)
    ·
      refine ⟨84228768291642256097370575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56152512194428170731580383 84228768291642256097370575)
      ·
        refine ⟨126343152437463384146055863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84228768291642256097370575 126343152437463384146055863)
        ·
          refine ⟨189514728656195076219083795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126343152437463384146055863 189514728656195076219083795)
          ·
            refine ⟨284272092984292614328625693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189514728656195076219083795 284272092984292614328625693)
            ·
              refine ⟨106602034869109730373234635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284272092984292614328625693 106602034869109730373234635)
              ·
                refine ⟨159903052303664595559851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106602034869109730373234635 159903052303664595559851953)
                ·
                  refine ⟨119927289227748446669888965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159903052303664595559851953 119927289227748446669888965)
                  ·
                    refine ⟨22486366730202833750604181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119927289227748446669888965 22486366730202833750604181)
                    ·
                      refine ⟨1054048440478257832059571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22486366730202833750604181 1054048440478257832059571)
                      ·
                        rfl

theorem cell23_2052752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_2052752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052752 prefixEnd_2052752 := by exact prefixLift 2052752
  have htrace : WordTrace (prefixWord ++ tailWord_2052752) baseStart_2052752 baseEnd_2052752 := by
    simpa [prefixWord, tailWord_2052752, baseEnd_2052752] using wordTrace_append hprefix tailTrace_2052752
  have hstable : (prefixWord ++ tailWord_2052752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052752).length < 2 ^ (prefixWord ++ tailWord_2052752).sum := by decide
  have hdescent : baseEnd_2052752 < baseStart_2052752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052796 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_2052796 : Nat := 118140960795 + 2052796 * 2 ^ 59
def prefixEnd_2052796 : Nat := 4983230072969 + 3 ^ 40 * 2052796 * 2
def baseEnd_2052796 : Nat := 351357011209018553303123

theorem tailTrace_2052796 : CollatzResearch.WordTrace tailWord_2052796 prefixEnd_2052796 351357011209018553303123 := by
  unfold tailWord_2052796
  simp only [CollatzResearch.WordTrace]
  refine ⟨37435810535539078245021121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49914414047385437660028161 37435810535539078245021121)
  ·
    refine ⟨28076857901654308683765841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37435810535539078245021121 28076857901654308683765841)
    ·
      refine ⟨21057643426240731512824381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28076857901654308683765841 21057643426240731512824381)
      ·
        refine ⟨7896616284840274317309143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21057643426240731512824381 7896616284840274317309143)
        ·
          refine ⟨11844924427260411475963715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896616284840274317309143 11844924427260411475963715)
          ·
            refine ⟨17767386640890617213945573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844924427260411475963715 17767386640890617213945573)
            ·
              refine ⟨3331384995166990727614795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17767386640890617213945573 3331384995166990727614795)
              ·
                refine ⟨4997077492750486091422193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331384995166990727614795 4997077492750486091422193)
                ·
                  refine ⟨3747808119562864568566645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4997077492750486091422193 3747808119562864568566645)
                  ·
                    refine ⟨351357011209018553303123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3747808119562864568566645 351357011209018553303123)
                    ·
                      rfl

theorem cell23_2052796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_2052796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052796 prefixEnd_2052796 := by exact prefixLift 2052796
  have htrace : WordTrace (prefixWord ++ tailWord_2052796) baseStart_2052796 baseEnd_2052796 := by
    simpa [prefixWord, tailWord_2052796, baseEnd_2052796] using wordTrace_append hprefix tailTrace_2052796
  have hstable : (prefixWord ++ tailWord_2052796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052796).length < 2 ^ (prefixWord ++ tailWord_2052796).sum := by decide
  have hdescent : baseEnd_2052796 < baseStart_2052796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052826 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_2052826 : Nat := 118140960795 + 2052826 * 2 ^ 59
def prefixEnd_2052826 : Nat := 4983230072969 + 3 ^ 40 * 2052826 * 2
def baseEnd_2052826 : Nat := 351362146015563514178077

theorem tailTrace_2052826 : CollatzResearch.WordTrace tailWord_2052826 prefixEnd_2052826 351362146015563514178077 := by
  unfold tailWord_2052826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18718178815242367903408583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49915143507312981075756221 18718178815242367903408583)
  ·
    refine ⟨28077268222863551855112875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18718178815242367903408583 28077268222863551855112875)
    ·
      refine ⟨42115902334295327782669313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077268222863551855112875 42115902334295327782669313)
      ·
        refine ⟨31586926750721495837001985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42115902334295327782669313 31586926750721495837001985)
        ·
          refine ⟨23690195063041121877751489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31586926750721495837001985 23690195063041121877751489)
          ·
            refine ⟨17767646297280841408313617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23690195063041121877751489 17767646297280841408313617)
            ·
              refine ⟨13325734722960631056235213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17767646297280841408313617 13325734722960631056235213)
              ·
                refine ⟨4997150521110236646088205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13325734722960631056235213 4997150521110236646088205)
                ·
                  refine ⟨1873931445416338742283077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4997150521110236646088205 1873931445416338742283077)
                  ·
                    refine ⟨351362146015563514178077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873931445416338742283077 351362146015563514178077)
                    ·
                      rfl

theorem cell23_2052826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_2052826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052826 prefixEnd_2052826 := by exact prefixLift 2052826
  have htrace : WordTrace (prefixWord ++ tailWord_2052826) baseStart_2052826 baseEnd_2052826 := by
    simpa [prefixWord, tailWord_2052826, baseEnd_2052826] using wordTrace_append hprefix tailTrace_2052826
  have hstable : (prefixWord ++ tailWord_2052826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052826).length < 2 ^ (prefixWord ++ tailWord_2052826).sum := by decide
  have hdescent : baseEnd_2052826 < baseStart_2052826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052833 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_2052833 : Nat := 118140960795 + 2052833 * 2 ^ 59
def prefixEnd_2052833 : Nat := 4983230072969 + 3 ^ 40 * 2052833 * 2
def baseEnd_2052833 : Nat := 1054090032411272015146699

theorem tailTrace_2052833 : CollatzResearch.WordTrace tailWord_2052833 prefixEnd_2052833 1054090032411272015146699 := by
  unfold tailWord_2052833
  simp only [CollatzResearch.WordTrace]
  refine ⟨74872970571944111809139153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49915313714629407872759435 74872970571944111809139153)
  ·
    refine ⟨56154727928958083856854365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74872970571944111809139153 56154727928958083856854365)
    ·
      refine ⟨21058022973359281446320387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56154727928958083856854365 21058022973359281446320387)
      ·
        refine ⟨31587034460038922169480581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21058022973359281446320387 31587034460038922169480581)
        ·
          refine ⟨5922568961257297906777609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31587034460038922169480581 5922568961257297906777609)
          ·
            refine ⟨4441926720942973430083207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5922568961257297906777609 4441926720942973430083207)
            ·
              refine ⟨6662890081414460145124811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441926720942973430083207 6662890081414460145124811)
              ·
                refine ⟨9994335122121690217687217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662890081414460145124811 9994335122121690217687217)
                ·
                  refine ⟨7495751341591267663265413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994335122121690217687217 7495751341591267663265413)
                  ·
                    refine ⟨1405453376548362686862265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495751341591267663265413 1405453376548362686862265)
                    ·
                      refine ⟨1054090032411272015146699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405453376548362686862265 1054090032411272015146699)
                      ·
                        rfl

theorem cell23_2052833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_2052833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052833 prefixEnd_2052833 := by exact prefixLift 2052833
  have htrace : WordTrace (prefixWord ++ tailWord_2052833) baseStart_2052833 baseEnd_2052833 := by
    simpa [prefixWord, tailWord_2052833, baseEnd_2052833] using wordTrace_append hprefix tailTrace_2052833
  have hstable : (prefixWord ++ tailWord_2052833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052833).length < 2 ^ (prefixWord ++ tailWord_2052833).sum := by decide
  have hdescent : baseEnd_2052833 < baseStart_2052833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052860 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_2052860 : Nat := 118140960795 + 2052860 * 2 ^ 59
def prefixEnd_2052860 : Nat := 4983230072969 + 3 ^ 40 * 2052860 * 2
def baseEnd_2052860 : Nat := 351367965462981136503025

theorem tailTrace_2052860 : CollatzResearch.WordTrace tailWord_2052860 prefixEnd_2052860 351367965462981136503025 := by
  unfold tailWord_2052860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436977671423147710186017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49915970228564196946914689 37436977671423147710186017)
  ·
    refine ⟨28077733253567360782639513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37436977671423147710186017 28077733253567360782639513)
    ·
      refine ⟨21058299940175520586979635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28077733253567360782639513 21058299940175520586979635)
      ·
        refine ⟨31587449910263280880469453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21058299940175520586979635 31587449910263280880469453)
        ·
          refine ⟨11845293716348730330176045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31587449910263280880469453 11845293716348730330176045)
          ·
            refine ⟨4441985143630773873816017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11845293716348730330176045 4441985143630773873816017)
            ·
              refine ⟨3331488857723080405362013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441985143630773873816017 3331488857723080405362013)
              ·
                refine ⟨1249308321646155152010755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331488857723080405362013 1249308321646155152010755)
                ·
                  refine ⟨1873962482469232728016133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249308321646155152010755 1873962482469232728016133)
                  ·
                    refine ⟨351367965462981136503025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1873962482469232728016133 351367965462981136503025)
                    ·
                      rfl

theorem cell23_2052860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_2052860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052860 prefixEnd_2052860 := by exact prefixLift 2052860
  have htrace : WordTrace (prefixWord ++ tailWord_2052860) baseStart_2052860 baseEnd_2052860 := by
    simpa [prefixWord, tailWord_2052860, baseEnd_2052860] using wordTrace_append hprefix tailTrace_2052860
  have hstable : (prefixWord ++ tailWord_2052860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052860).length < 2 ^ (prefixWord ++ tailWord_2052860).sum := by decide
  have hdescent : baseEnd_2052860 < baseStart_2052860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052883 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 3]
def baseStart_2052883 : Nat := 118140960795 + 2052883 * 2 ^ 59
def prefixEnd_2052883 : Nat := 4983230072969 + 3 ^ 40 * 2052883 * 2
def baseEnd_2052883 : Nat := 1054115706443996819521469

theorem tailTrace_2052883 : CollatzResearch.WordTrace tailWord_2052883 prefixEnd_2052883 1054115706443996819521469 := by
  unfold tailWord_2052883
  simp only [CollatzResearch.WordTrace]
  refine ⟨74874794221762970348459303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49916529481175313565639535 74874794221762970348459303)
  ·
    refine ⟨112312191332644455522688955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74874794221762970348459303 112312191332644455522688955)
    ·
      refine ⟨168468286998966683284033433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112312191332644455522688955 168468286998966683284033433)
      ·
        refine ⟨126351215249225012463025075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168468286998966683284033433 126351215249225012463025075)
        ·
          refine ⟨189526822873837518694537613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126351215249225012463025075 189526822873837518694537613)
          ·
            refine ⟨71072558577689069510451605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189526822873837518694537613 71072558577689069510451605)
            ·
              refine ⟨3331526183329175133302419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71072558577689069510451605 3331526183329175133302419)
              ·
                refine ⟨4997289274993762699953629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331526183329175133302419 4997289274993762699953629)
                ·
                  refine ⟨1873983478122661012482611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4997289274993762699953629 1873983478122661012482611)
                  ·
                    refine ⟨2810975217183991518723917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1873983478122661012482611 2810975217183991518723917)
                    ·
                      refine ⟨1054115706443996819521469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2810975217183991518723917 1054115706443996819521469)
                      ·
                        rfl

theorem cell23_2052883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_2052883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052883 prefixEnd_2052883 := by exact prefixLift 2052883
  have htrace : WordTrace (prefixWord ++ tailWord_2052883) baseStart_2052883 baseEnd_2052883 := by
    simpa [prefixWord, tailWord_2052883, baseEnd_2052883] using wordTrace_append hprefix tailTrace_2052883
  have hstable : (prefixWord ++ tailWord_2052883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052883).length < 2 ^ (prefixWord ++ tailWord_2052883).sum := by decide
  have hdescent : baseEnd_2052883 < baseStart_2052883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052889 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_2052889 : Nat := 118140960795 + 2052889 * 2 ^ 59
def prefixEnd_2052889 : Nat := 4983230072969 + 3 ^ 40 * 2052889 * 2
def baseEnd_2052889 : Nat := 1054118787327923796046441

theorem tailTrace_2052889 : CollatzResearch.WordTrace tailWord_2052889 prefixEnd_2052889 1054118787327923796046441 := by
  unfold tailWord_2052889
  simp only [CollatzResearch.WordTrace]
  refine ⟨74875013059741233373177721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49916675373160822248785147 74875013059741233373177721)
  ·
    refine ⟨56156259794805925029883291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74875013059741233373177721 56156259794805925029883291)
    ·
      refine ⟨84234389692208887544824937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56156259794805925029883291 84234389692208887544824937)
      ·
        refine ⟨63175792269156665658618703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84234389692208887544824937 63175792269156665658618703)
        ·
          refine ⟨94763688403734998487928055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63175792269156665658618703 94763688403734998487928055)
          ·
            refine ⟨142145532605602497731892083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94763688403734998487928055 142145532605602497731892083)
            ·
              refine ⟨213218298908403746597838125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142145532605602497731892083 213218298908403746597838125)
              ·
                refine ⟨79956862090651404974189297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213218298908403746597838125 79956862090651404974189297)
                ·
                  refine ⟨59967646567988553730641973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79956862090651404974189297 59967646567988553730641973)
                  ·
                    refine ⟨5621966865748926912247685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59967646567988553730641973 5621966865748926912247685)
                    ·
                      refine ⟨1054118787327923796046441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5621966865748926912247685 1054118787327923796046441)
                      ·
                        rfl

theorem cell23_2052889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_2052889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052889 prefixEnd_2052889 := by exact prefixLift 2052889
  have htrace : WordTrace (prefixWord ++ tailWord_2052889) baseStart_2052889 baseEnd_2052889 := by
    simpa [prefixWord, tailWord_2052889, baseEnd_2052889] using wordTrace_append hprefix tailTrace_2052889
  have hstable : (prefixWord ++ tailWord_2052889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052889).length < 2 ^ (prefixWord ++ tailWord_2052889).sum := by decide
  have hdescent : baseEnd_2052889 < baseStart_2052889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052910 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2052910 : Nat := 118140960795 + 2052910 * 2 ^ 59
def prefixEnd_2052910 : Nat := 4983230072969 + 3 ^ 40 * 2052910 * 2
def baseEnd_2052910 : Nat := 1054129570421668213883845

theorem tailTrace_2052910 : CollatzResearch.WordTrace tailWord_2052910 prefixEnd_2052910 1054129570421668213883845 := by
  unfold tailWord_2052910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359472374083144244961523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49917185995110102639794789 9359472374083144244961523)
  ·
    refine ⟨14039208561124716367442285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9359472374083144244961523 14039208561124716367442285)
    ·
      refine ⟨5264703210421768637790857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14039208561124716367442285 5264703210421768637790857)
      ·
        refine ⟨3948527407816326478343143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5264703210421768637790857 3948527407816326478343143)
        ·
          refine ⟨5922791111724489717514715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948527407816326478343143 5922791111724489717514715)
          ·
            refine ⟨8884186667586734576272073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922791111724489717514715 8884186667586734576272073)
            ·
              refine ⟨6663140000690050932204055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884186667586734576272073 6663140000690050932204055)
              ·
                refine ⟨9994710001035076398306083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663140000690050932204055 9994710001035076398306083)
                ·
                  refine ⟨14992065001552614597459125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994710001035076398306083 14992065001552614597459125)
                  ·
                    refine ⟨1405506093895557618511793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14992065001552614597459125 1405506093895557618511793)
                    ·
                      refine ⟨1054129570421668213883845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405506093895557618511793 1054129570421668213883845)
                      ·
                        rfl

theorem cell23_2052910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2052910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052910 prefixEnd_2052910 := by exact prefixLift 2052910
  have htrace : WordTrace (prefixWord ++ tailWord_2052910) baseStart_2052910 baseEnd_2052910 := by
    simpa [prefixWord, tailWord_2052910, baseEnd_2052910] using wordTrace_append hprefix tailTrace_2052910
  have hstable : (prefixWord ++ tailWord_2052910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052910).length < 2 ^ (prefixWord ++ tailWord_2052910).sum := by decide
  have hdescent : baseEnd_2052910 < baseStart_2052910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052917 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_2052917 : Nat := 118140960795 + 2052917 * 2 ^ 59
def prefixEnd_2052917 : Nat := 4983230072969 + 3 ^ 40 * 2052917 * 2
def baseEnd_2052917 : Nat := 1054133164786249686496313

theorem tailTrace_2052917 : CollatzResearch.WordTrace tailWord_2052917 prefixEnd_2052917 1054133164786249686496313 := by
  unfold tailWord_2052917
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876034303639794155197005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49917356202426529436798003 74876034303639794155197005)
  ·
    refine ⟨28078512863864922808198877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74876034303639794155197005 28078512863864922808198877)
    ·
      refine ⟨10529442323949346053074579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28078512863864922808198877 10529442323949346053074579)
      ·
        refine ⟨15794163485924019079611869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529442323949346053074579 15794163485924019079611869)
        ·
          refine ⟨5922811307221507154854451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15794163485924019079611869 5922811307221507154854451)
          ·
            refine ⟨8884216960832260732281677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922811307221507154854451 8884216960832260732281677)
            ·
              refine ⟨3331581360312097774605629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8884216960832260732281677 3331581360312097774605629)
              ·
                refine ⟨1249343010117036665477111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331581360312097774605629 1249343010117036665477111)
                ·
                  refine ⟨1874014515175554998215667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249343010117036665477111 1874014515175554998215667)
                  ·
                    refine ⟨2811021772763332497323501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874014515175554998215667 2811021772763332497323501)
                    ·
                      refine ⟨1054133164786249686496313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811021772763332497323501 1054133164786249686496313)
                      ·
                        rfl

theorem cell23_2052917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_2052917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052917 prefixEnd_2052917 := by exact prefixLift 2052917
  have htrace : WordTrace (prefixWord ++ tailWord_2052917) baseStart_2052917 baseEnd_2052917 := by
    simpa [prefixWord, tailWord_2052917, baseEnd_2052917] using wordTrace_append hprefix tailTrace_2052917
  have hstable : (prefixWord ++ tailWord_2052917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052917).length < 2 ^ (prefixWord ++ tailWord_2052917).sum := by decide
  have hdescent : baseEnd_2052917 < baseStart_2052917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052946 : List Nat := [3, 2, 2, 1, 1, 2, 4, 8]
def baseStart_2052946 : Nat := 118140960795 + 2052946 * 2 ^ 59
def prefixEnd_2052946 : Nat := 4983230072969 + 3 ^ 40 * 2052946 * 2
def baseEnd_2052946 : Nat := 39042520582415928630877

theorem tailTrace_2052946 : CollatzResearch.WordTrace tailWord_2052946 prefixEnd_2052946 39042520582415928630877 := by
  unfold tailWord_2052946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719273005133683027000673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49918061347023154738668461 18719273005133683027000673)
  ·
    refine ⟨14039454753850262270250505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18719273005133683027000673 14039454753850262270250505)
    ·
      refine ⟨10529591065387696702687879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14039454753850262270250505 10529591065387696702687879)
      ·
        refine ⟨15794386598081545054031819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529591065387696702687879 15794386598081545054031819)
        ·
          refine ⟨23691579897122317581047729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794386598081545054031819 23691579897122317581047729)
          ·
            refine ⟨17768684922841738185785797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23691579897122317581047729 17768684922841738185785797)
            ·
              refine ⟨3331628423032825909834837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17768684922841738185785797 3331628423032825909834837)
              ·
                refine ⟨39042520582415928630877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3331628423032825909834837 39042520582415928630877)
                ·
                  rfl

theorem cell23_2052946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_2052946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2052946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2052946 prefixEnd_2052946 := by exact prefixLift 2052946
  have htrace : WordTrace (prefixWord ++ tailWord_2052946) baseStart_2052946 baseEnd_2052946 := by
    simpa [prefixWord, tailWord_2052946, baseEnd_2052946] using wordTrace_append hprefix tailTrace_2052946
  have hstable : (prefixWord ++ tailWord_2052946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052946).length < 2 ^ (prefixWord ++ tailWord_2052946).sum := by decide
  have hdescent : baseEnd_2052946 < baseStart_2052946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053000 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_2053000 : Nat := 118140960795 + 2053000 * 2 ^ 59
def prefixEnd_2053000 : Nat := 4983230072969 + 3 ^ 40 * 2053000 * 2
def baseEnd_2053000 : Nat := 1054175783680572861758431

theorem tailTrace_2053000 : CollatzResearch.WordTrace tailWord_2053000 prefixEnd_2053000 1054175783680572861758431 := by
  unfold tailWord_2053000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37439530781169549665234227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49919374374892732886978969 37439530781169549665234227)
  ·
    refine ⟨56159296171754324497851341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37439530781169549665234227 56159296171754324497851341)
    ·
      refine ⟨21059736064407871686694253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56159296171754324497851341 21059736064407871686694253)
      ·
        refine ⟨7897401024152951882510345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21059736064407871686694253 7897401024152951882510345)
        ·
          refine ⟨5923050768114713911882759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897401024152951882510345 5923050768114713911882759)
          ·
            refine ⟨8884576152172070867824139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923050768114713911882759 8884576152172070867824139)
            ·
              refine ⟨13326864228258106301736209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884576152172070867824139 13326864228258106301736209)
              ·
                refine ⟨9995148171193579726302157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13326864228258106301736209 9995148171193579726302157)
                ·
                  refine ⟨3748180564197592397363309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9995148171193579726302157 3748180564197592397363309)
                  ·
                    refine ⟨1405567711574097149011241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748180564197592397363309 1405567711574097149011241)
                    ·
                      refine ⟨1054175783680572861758431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405567711574097149011241 1054175783680572861758431)
                      ·
                        rfl

theorem cell23_2053000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_2053000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053000 prefixEnd_2053000 := by exact prefixLift 2053000
  have htrace : WordTrace (prefixWord ++ tailWord_2053000) baseStart_2053000 baseEnd_2053000 := by
    simpa [prefixWord, tailWord_2053000, baseEnd_2053000] using wordTrace_append hprefix tailTrace_2053000
  have hstable : (prefixWord ++ tailWord_2053000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053000).length < 2 ^ (prefixWord ++ tailWord_2053000).sum := by decide
  have hdescent : baseEnd_2053000 < baseStart_2053000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053047 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_2053047 : Nat := 118140960795 + 2053047 * 2 ^ 59
def prefixEnd_2053047 : Nat := 4983230072969 + 3 ^ 40 * 2053047 * 2
def baseEnd_2053047 : Nat := 1054199917271334177870715

theorem tailTrace_2053047 : CollatzResearch.WordTrace tailWord_2053047 prefixEnd_2053047 1054199917271334177870715 := by
  unfold tailWord_2053047
  simp only [CollatzResearch.WordTrace]
  refine ⟨74880775793168826357429395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49920517195445884238286263 74880775793168826357429395)
  ·
    refine ⟨112321163689753239536144093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74880775793168826357429395 112321163689753239536144093)
    ·
      refine ⟨42120436383657464826054035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112321163689753239536144093 42120436383657464826054035)
      ·
        refine ⟨63180654575486197239081053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42120436383657464826054035 63180654575486197239081053)
        ·
          refine ⟨23692745465807323964655395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63180654575486197239081053 23692745465807323964655395)
          ·
            refine ⟨35539118198710985946983093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23692745465807323964655395 35539118198710985946983093)
            ·
              refine ⟨3331792331129154932529665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35539118198710985946983093 3331792331129154932529665)
              ·
                refine ⟨2498844248346866199397249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331792331129154932529665 2498844248346866199397249)
                ·
                  refine ⟨1874133186260149649547937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2498844248346866199397249 1874133186260149649547937)
                  ·
                    refine ⟨1405599889695112237160953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874133186260149649547937 1405599889695112237160953)
                    ·
                      refine ⟨1054199917271334177870715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405599889695112237160953 1054199917271334177870715)
                      ·
                        rfl

theorem cell23_2053047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_2053047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053047 prefixEnd_2053047 := by exact prefixLift 2053047
  have htrace : WordTrace (prefixWord ++ tailWord_2053047) baseStart_2053047 baseEnd_2053047 := by
    simpa [prefixWord, tailWord_2053047, baseEnd_2053047] using wordTrace_append hprefix tailTrace_2053047
  have hstable : (prefixWord ++ tailWord_2053047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053047).length < 2 ^ (prefixWord ++ tailWord_2053047).sum := by decide
  have hdescent : baseEnd_2053047 < baseStart_2053047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053063 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_2053063 : Nat := 118140960795 + 2053063 * 2 ^ 59
def prefixEnd_2053063 : Nat := 4983230072969 + 3 ^ 40 * 2053063 * 2
def baseEnd_2053063 : Nat := 1054208132961806115270641

theorem tailTrace_2053063 : CollatzResearch.WordTrace tailWord_2053063 prefixEnd_2053063 1054208132961806115270641 := by
  unfold tailWord_2053063
  simp only [CollatzResearch.WordTrace]
  refine ⟨74881359361110861090011843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49920906240740574060007895 74881359361110861090011843)
  ·
    refine ⟨112322039041666291635017765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74881359361110861090011843 112322039041666291635017765)
    ·
      refine ⟨21060382320312429681565831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112322039041666291635017765 21060382320312429681565831)
      ·
        refine ⟨31590573480468644522348747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21060382320312429681565831 31590573480468644522348747)
        ·
          refine ⟨47385860220702966783523121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31590573480468644522348747 47385860220702966783523121)
          ·
            refine ⟨35539395165527225087642341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47385860220702966783523121 35539395165527225087642341)
            ·
              refine ⟨6663636593536354703932939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35539395165527225087642341 6663636593536354703932939)
              ·
                refine ⟨9995454890304532055899409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663636593536354703932939 9995454890304532055899409)
                ·
                  refine ⟨7496591167728399041924557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995454890304532055899409 7496591167728399041924557)
                  ·
                    refine ⟨2811221687898149640721709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7496591167728399041924557 2811221687898149640721709)
                    ·
                      refine ⟨1054208132961806115270641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811221687898149640721709 1054208132961806115270641)
                      ·
                        rfl

theorem cell23_2053063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_2053063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053063 prefixEnd_2053063 := by exact prefixLift 2053063
  have htrace : WordTrace (prefixWord ++ tailWord_2053063) baseStart_2053063 baseEnd_2053063 := by
    simpa [prefixWord, tailWord_2053063, baseEnd_2053063] using wordTrace_append hprefix tailTrace_2053063
  have hstable : (prefixWord ++ tailWord_2053063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053063).length < 2 ^ (prefixWord ++ tailWord_2053063).sum := by decide
  have hdescent : baseEnd_2053063 < baseStart_2053063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053064 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_2053064 : Nat := 118140960795 + 2053064 * 2 ^ 59
def prefixEnd_2053064 : Nat := 4983230072969 + 3 ^ 40 * 2053064 * 2
def baseEnd_2053064 : Nat := 1054208646442460611358137

theorem tailTrace_2053064 : CollatzResearch.WordTrace tailWord_2053064 prefixEnd_2053064 1054208646442460611358137 := by
  unfold tailWord_2053064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440697917053619130399123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49920930556071492173865497 37440697917053619130399123)
  ·
    refine ⟨56161046875580428695598685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440697917053619130399123 56161046875580428695598685)
    ·
      refine ⟨21060392578342660760849507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56161046875580428695598685 21060392578342660760849507)
      ·
        refine ⟨31590588867513991141274261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21060392578342660760849507 31590588867513991141274261)
        ·
          refine ⟨1480808853164718334747231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31590588867513991141274261 1480808853164718334747231)
          ·
            refine ⟨2221213279747077502120847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480808853164718334747231 2221213279747077502120847)
            ·
              refine ⟨3331819919620616253181271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221213279747077502120847 3331819919620616253181271)
              ·
                refine ⟨4997729879430924379771907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331819919620616253181271 4997729879430924379771907)
                ·
                  refine ⟨7496594819146386569657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997729879430924379771907 7496594819146386569657861)
                  ·
                    refine ⟨1405611528589947481810849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496594819146386569657861 1405611528589947481810849)
                    ·
                      refine ⟨1054208646442460611358137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405611528589947481810849 1054208646442460611358137)
                      ·
                        rfl

theorem cell23_2053064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_2053064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053064 prefixEnd_2053064 := by exact prefixLift 2053064
  have htrace : WordTrace (prefixWord ++ tailWord_2053064) baseStart_2053064 baseEnd_2053064 := by
    simpa [prefixWord, tailWord_2053064, baseEnd_2053064] using wordTrace_append hprefix tailTrace_2053064
  have hstable : (prefixWord ++ tailWord_2053064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053064).length < 2 ^ (prefixWord ++ tailWord_2053064).sum := by decide
  have hdescent : baseEnd_2053064 < baseStart_2053064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053087 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 5]
def baseStart_2053087 : Nat := 118140960795 + 2053087 * 2 ^ 59
def prefixEnd_2053087 : Nat := 4983230072969 + 3 ^ 40 * 2053087 * 2
def baseEnd_2053087 : Nat := 117135606277501557930059

theorem tailTrace_2053087 : CollatzResearch.WordTrace tailWord_2053087 prefixEnd_2053087 117135606277501557930059 := by
  unfold tailWord_2053087
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882234713023913188885515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49921489808682608792590343 74882234713023913188885515)
  ·
    refine ⟨112323352069535869783328273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74882234713023913188885515 112323352069535869783328273)
    ·
      refine ⟨84242514052151902337496205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112323352069535869783328273 84242514052151902337496205)
      ·
        refine ⟨31590942769556963376561077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84242514052151902337496205 31590942769556963376561077)
        ·
          refine ⟨2961650884645965316552601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31590942769556963376561077 2961650884645965316552601)
          ·
            refine ⟨2221238163484473987414451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961650884645965316552601 2221238163484473987414451)
            ·
              refine ⟨3331857245226710981121677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221238163484473987414451 3331857245226710981121677)
              ·
                refine ⟨1249446466960016617920629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3331857245226710981121677 1249446466960016617920629)
                ·
                  refine ⟨117135606277501557930059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249446466960016617920629 117135606277501557930059)
                  ·
                    rfl

theorem cell23_2053087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 5].length) (baseStart_2053087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053087 prefixEnd_2053087 := by exact prefixLift 2053087
  have htrace : WordTrace (prefixWord ++ tailWord_2053087) baseStart_2053087 baseEnd_2053087 := by
    simpa [prefixWord, tailWord_2053087, baseEnd_2053087] using wordTrace_append hprefix tailTrace_2053087
  have hstable : (prefixWord ++ tailWord_2053087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053087).length < 2 ^ (prefixWord ++ tailWord_2053087).sum := by decide
  have hdescent : baseEnd_2053087 < baseStart_2053087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053103 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_2053103 : Nat := 118140960795 + 2053103 * 2 ^ 59
def prefixEnd_2053103 : Nat := 4983230072969 + 3 ^ 40 * 2053103 * 2
def baseEnd_2053103 : Nat := 1054228672187985958770457

theorem tailTrace_2053103 : CollatzResearch.WordTrace tailWord_2053103 prefixEnd_2053103 1054228672187985958770457 := by
  unfold tailWord_2053103
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882818280965947921467963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49921878853977298614311975 74882818280965947921467963)
  ·
    refine ⟨112324227421448921882201945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74882818280965947921467963 112324227421448921882201945)
    ·
      refine ⟨84243170566086691411651459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112324227421448921882201945 84243170566086691411651459)
      ·
        refine ⟨126364755849130037117477189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84243170566086691411651459 126364755849130037117477189)
        ·
          refine ⟨23693391721711881959526973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126364755849130037117477189 23693391721711881959526973)
          ·
            refine ⟨8885021895641955734822615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23693391721711881959526973 8885021895641955734822615)
            ·
              refine ⟨13327532843462933602233923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885021895641955734822615 13327532843462933602233923)
              ·
                refine ⟨19991299265194400403350885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13327532843462933602233923 19991299265194400403350885)
                ·
                  refine ⟨3748368612223950075628291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19991299265194400403350885 3748368612223950075628291)
                  ·
                    refine ⟨5622552918335925113442437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3748368612223950075628291 5622552918335925113442437)
                    ·
                      refine ⟨1054228672187985958770457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5622552918335925113442437 1054228672187985958770457)
                      ·
                        rfl

theorem cell23_2053103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_2053103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053103 prefixEnd_2053103 := by exact prefixLift 2053103
  have htrace : WordTrace (prefixWord ++ tailWord_2053103) baseStart_2053103 baseEnd_2053103 := by
    simpa [prefixWord, tailWord_2053103, baseEnd_2053103] using wordTrace_append hprefix tailTrace_2053103
  have hstable : (prefixWord ++ tailWord_2053103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053103).length < 2 ^ (prefixWord ++ tailWord_2053103).sum := by decide
  have hdescent : baseEnd_2053103 < baseStart_2053103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053110 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2053110 : Nat := 118140960795 + 2053110 * 2 ^ 59
def prefixEnd_2053110 : Nat := 4983230072969 + 3 ^ 40 * 2053110 * 2
def baseEnd_2053110 : Nat := 1054232266552567431382925

theorem tailTrace_2053110 : CollatzResearch.WordTrace tailWord_2053110 prefixEnd_2053110 1054232266552567431382925 := by
  unfold tailWord_2053110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680192099496286757310799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49922049061293725411315189 4680192099496286757310799)
  ·
    refine ⟨7020288149244430135966199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680192099496286757310799 7020288149244430135966199)
    ·
      refine ⟨10530432223866645203949299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7020288149244430135966199 10530432223866645203949299)
      ·
        refine ⟨15795648335799967805923949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530432223866645203949299 15795648335799967805923949)
        ·
          refine ⟨5923368125924987927221481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15795648335799967805923949 5923368125924987927221481)
          ·
            refine ⟨4442526094443740945416111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5923368125924987927221481 4442526094443740945416111)
            ·
              refine ⟨6663789141665611418124167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442526094443740945416111 6663789141665611418124167)
              ·
                refine ⟨9995683712498417127186251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663789141665611418124167 9995683712498417127186251)
                ·
                  refine ⟨14993525568747625690779377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995683712498417127186251 14993525568747625690779377)
                  ·
                    refine ⟨11245144176560719268084533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14993525568747625690779377 11245144176560719268084533)
                    ·
                      refine ⟨1054232266552567431382925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11245144176560719268084533 1054232266552567431382925)
                      ·
                        rfl

theorem cell23_2053110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2053110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053110 prefixEnd_2053110 := by exact prefixLift 2053110
  have htrace : WordTrace (prefixWord ++ tailWord_2053110) baseStart_2053110 baseEnd_2053110 := by
    simpa [prefixWord, tailWord_2053110, baseEnd_2053110] using wordTrace_append hprefix tailTrace_2053110
  have hstable : (prefixWord ++ tailWord_2053110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053110).length < 2 ^ (prefixWord ++ tailWord_2053110).sum := by decide
  have hdescent : baseEnd_2053110 < baseStart_2053110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053136 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_2053136 : Nat := 118140960795 + 2053136 * 2 ^ 59
def prefixEnd_2053136 : Nat := 4983230072969 + 3 ^ 40 * 2053136 * 2
def baseEnd_2053136 : Nat := 1054245617049584329657805

theorem tailTrace_2053136 : CollatzResearch.WordTrace tailWord_2053136 prefixEnd_2053136 1054245617049584329657805 := by
  unfold tailWord_2053136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37442010944923197278709631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49922681259897596371612841 37442010944923197278709631)
  ·
    refine ⟨56163016417384795918064447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37442010944923197278709631 56163016417384795918064447)
    ·
      refine ⟨84244524626077193877096671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56163016417384795918064447 84244524626077193877096671)
      ·
        refine ⟨126366786939115790815645007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84244524626077193877096671 126366786939115790815645007)
        ·
          refine ⟨189550180408673686223467511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126366786939115790815645007 189550180408673686223467511)
          ·
            refine ⟨284325270613010529335201267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189550180408673686223467511 284325270613010529335201267)
            ·
              refine ⟨426487905919515794002801901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284325270613010529335201267 426487905919515794002801901)
              ·
                refine ⟨159932964719818422751050713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426487905919515794002801901 159932964719818422751050713)
                ·
                  refine ⟨119949723539863817063288035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159932964719818422751050713 119949723539863817063288035)
                  ·
                    refine ⟨179924585309795725594932053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119949723539863817063288035 179924585309795725594932053)
                    ·
                      refine ⟨1054245617049584329657805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 179924585309795725594932053 1054245617049584329657805)
                      ·
                        rfl

theorem cell23_2053136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_2053136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053136 prefixEnd_2053136 := by exact prefixLift 2053136
  have htrace : WordTrace (prefixWord ++ tailWord_2053136) baseStart_2053136 baseEnd_2053136 := by
    simpa [prefixWord, tailWord_2053136, baseEnd_2053136] using wordTrace_append hprefix tailTrace_2053136
  have hstable : (prefixWord ++ tailWord_2053136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053136).length < 2 ^ (prefixWord ++ tailWord_2053136).sum := by decide
  have hdescent : baseEnd_2053136 < baseStart_2053136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053204 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_2053204 : Nat := 118140960795 + 2053204 * 2 ^ 59
def prefixEnd_2053204 : Nat := 4983230072969 + 3 ^ 40 * 2053204 * 2
def baseEnd_2053204 : Nat := 1054280533734090063607493

theorem tailTrace_2053204 : CollatzResearch.WordTrace tailWord_2053204 prefixEnd_2053204 1054280533734090063607493 := by
  unfold tailWord_2053204
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443251026800021085447333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49924334702400028113929777 37443251026800021085447333)
  ·
    refine ⟨7020609567525003953521375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37443251026800021085447333 7020609567525003953521375)
    ·
      refine ⟨10530914351287505930282063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7020609567525003953521375 10530914351287505930282063)
      ·
        refine ⟨15796371526931258895423095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530914351287505930282063 15796371526931258895423095)
        ·
          refine ⟨23694557290396888343134643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796371526931258895423095 23694557290396888343134643)
          ·
            refine ⟨35541835935595332514701965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23694557290396888343134643 35541835935595332514701965)
            ·
              refine ⟨13328188475848249693013237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35541835935595332514701965 13328188475848249693013237)
              ·
                refine ⟨1249517669610773408719991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13328188475848249693013237 1249517669610773408719991)
                ·
                  refine ⟨1874276504416160113079987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249517669610773408719991 1874276504416160113079987)
                  ·
                    refine ⟨2811414756624240169619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874276504416160113079987 2811414756624240169619981)
                    ·
                      refine ⟨1054280533734090063607493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811414756624240169619981 1054280533734090063607493)
                      ·
                        rfl

theorem cell23_2053204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_2053204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053204 prefixEnd_2053204 := by exact prefixLift 2053204
  have htrace : WordTrace (prefixWord ++ tailWord_2053204) baseStart_2053204 baseEnd_2053204 := by
    simpa [prefixWord, tailWord_2053204, baseEnd_2053204] using wordTrace_append hprefix tailTrace_2053204
  have hstable : (prefixWord ++ tailWord_2053204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053204).length < 2 ^ (prefixWord ++ tailWord_2053204).sum := by decide
  have hdescent : baseEnd_2053204 < baseStart_2053204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053230 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2053230 : Nat := 118140960795 + 2053230 * 2 ^ 59
def prefixEnd_2053230 : Nat := 4983230072969 + 3 ^ 40 * 2053230 * 2
def baseEnd_2053230 : Nat := 1054293884231106961882373

theorem tailTrace_2053230 : CollatzResearch.WordTrace tailWord_2053230 prefixEnd_2053230 1054293884231106961882373 := by
  unfold tailWord_2053230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360931293938231076417643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49924966901003899074227429 9360931293938231076417643)
  ·
    refine ⟨14041396940907346614626465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360931293938231076417643 14041396940907346614626465)
    ·
      refine ⟨10531047705680509960969849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14041396940907346614626465 10531047705680509960969849)
      ·
        refine ⟨7898285779260382470727387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10531047705680509960969849 7898285779260382470727387)
        ·
          refine ⟨11847428668890573706091081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898285779260382470727387 11847428668890573706091081)
          ·
            refine ⟨8885571501667930279568311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11847428668890573706091081 8885571501667930279568311)
            ·
              refine ⟨13328357252501895419352467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885571501667930279568311 13328357252501895419352467)
              ·
                refine ⟨19992535878752843129028701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328357252501895419352467 19992535878752843129028701)
                ·
                  refine ⟨7497200954532316173385763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19992535878752843129028701 7497200954532316173385763)
                  ·
                    refine ⟨11245801431798474260078645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497200954532316173385763 11245801431798474260078645)
                    ·
                      refine ⟨1054293884231106961882373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11245801431798474260078645 1054293884231106961882373)
                      ·
                        rfl

theorem cell23_2053230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2053230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053230 prefixEnd_2053230 := by exact prefixLift 2053230
  have htrace : WordTrace (prefixWord ++ tailWord_2053230) baseStart_2053230 baseEnd_2053230 := by
    simpa [prefixWord, tailWord_2053230, baseEnd_2053230] using wordTrace_append hprefix tailTrace_2053230
  have hstable : (prefixWord ++ tailWord_2053230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053230).length < 2 ^ (prefixWord ++ tailWord_2053230).sum := by decide
  have hdescent : baseEnd_2053230 < baseStart_2053230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053240 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_2053240 : Nat := 118140960795 + 2053240 * 2 ^ 59
def prefixEnd_2053240 : Nat := 4983230072969 + 3 ^ 40 * 2053240 * 2
def baseEnd_2053240 : Nat := 1054299019037651922757327

theorem tailTrace_2053240 : CollatzResearch.WordTrace tailWord_2053240 prefixEnd_2053240 1054299019037651922757327 := by
  unfold tailWord_2053240
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443907540734810159602587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49925210054313080212803449 37443907540734810159602587)
  ·
    refine ⟨56165861311102215239403881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37443907540734810159602587 56165861311102215239403881)
    ·
      refine ⟨42124395983326661429552911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56165861311102215239403881 42124395983326661429552911)
      ·
        refine ⟨63186593974989992144329367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42124395983326661429552911 63186593974989992144329367)
        ·
          refine ⟨94779890962484988216494051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63186593974989992144329367 94779890962484988216494051)
          ·
            refine ⟨142169836443727482324741077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94779890962484988216494051 142169836443727482324741077)
            ·
              refine ⟨3332105541649862866986119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142169836443727482324741077 3332105541649862866986119)
              ·
                refine ⟨4998158312474794300479179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332105541649862866986119 4998158312474794300479179)
                ·
                  refine ⟨7497237468712191450718769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998158312474794300479179 7497237468712191450718769)
                  ·
                    refine ⟨5622928101534143588039077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7497237468712191450718769 5622928101534143588039077)
                    ·
                      refine ⟨1054299019037651922757327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5622928101534143588039077 1054299019037651922757327)
                      ·
                        rfl

theorem cell23_2053240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_2053240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053240 prefixEnd_2053240 := by exact prefixLift 2053240
  have htrace : WordTrace (prefixWord ++ tailWord_2053240) baseStart_2053240 baseEnd_2053240 := by
    simpa [prefixWord, tailWord_2053240, baseEnd_2053240] using wordTrace_append hprefix tailTrace_2053240
  have hstable : (prefixWord ++ tailWord_2053240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053240).length < 2 ^ (prefixWord ++ tailWord_2053240).sum := by decide
  have hdescent : baseEnd_2053240 < baseStart_2053240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053260 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2053260 : Nat := 118140960795 + 2053260 * 2 ^ 59
def prefixEnd_2053260 : Nat := 4983230072969 + 3 ^ 40 * 2053260 * 2
def baseEnd_2053260 : Nat := 1054309288650741844507235

theorem tailTrace_2053260 : CollatzResearch.WordTrace tailWord_2053260 prefixEnd_2053260 1054309288650741844507235 := by
  unfold tailWord_2053260
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444272270698581867466617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49925696360931442489955489 37444272270698581867466617)
  ·
    refine ⟨28083204203023936400599963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37444272270698581867466617 28083204203023936400599963)
    ·
      refine ⟨42124806304535904600899945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28083204203023936400599963 42124806304535904600899945)
      ·
        refine ⟨31593604728401928450674959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42124806304535904600899945 31593604728401928450674959)
        ·
          refine ⟨47390407092602892676012439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31593604728401928450674959 47390407092602892676012439)
          ·
            refine ⟨71085610638904339014018659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47390407092602892676012439 71085610638904339014018659)
            ·
              refine ⟨106628415958356508521027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71085610638904339014018659 106628415958356508521027989)
              ·
                refine ⟨4998206998047961336923187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106628415958356508521027989 4998206998047961336923187)
                ·
                  refine ⟨7497310497071942005384781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998206998047961336923187 7497310497071942005384781)
                  ·
                    refine ⟨2811491436401978252019293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7497310497071942005384781 2811491436401978252019293)
                    ·
                      refine ⟨1054309288650741844507235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811491436401978252019293 1054309288650741844507235)
                      ·
                        rfl

theorem cell23_2053260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2053260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053260 prefixEnd_2053260 := by exact prefixLift 2053260
  have htrace : WordTrace (prefixWord ++ tailWord_2053260) baseStart_2053260 baseEnd_2053260 := by
    simpa [prefixWord, tailWord_2053260, baseEnd_2053260] using wordTrace_append hprefix tailTrace_2053260
  have hstable : (prefixWord ++ tailWord_2053260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053260).length < 2 ^ (prefixWord ++ tailWord_2053260).sum := by decide
  have hdescent : baseEnd_2053260 < baseStart_2053260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053277 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2053277 : Nat := 118140960795 + 2053277 * 2 ^ 59
def prefixEnd_2053277 : Nat := 4983230072969 + 3 ^ 40 * 2053277 * 2
def baseEnd_2053277 : Nat := 1054318017821868277994657

theorem tailTrace_2053277 : CollatzResearch.WordTrace tailWord_2053277 prefixEnd_2053277 1054318017821868277994657 := by
  unfold tailWord_2053277
  simp only [CollatzResearch.WordTrace]
  refine ⟨74889164582335575638302085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49926109721557050425534723 74889164582335575638302085)
  ·
    refine ⟨14041718359187920432181641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74889164582335575638302085 14041718359187920432181641)
    ·
      refine ⟨10531288769390940324136231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14041718359187920432181641 10531288769390940324136231)
      ·
        refine ⟨15796933154086410486204347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10531288769390940324136231 15796933154086410486204347)
        ·
          refine ⟨23695399731129615729306521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796933154086410486204347 23695399731129615729306521)
          ·
            refine ⟨17771549798347211796979891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23695399731129615729306521 17771549798347211796979891)
            ·
              refine ⟨26657324697520817695469837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771549798347211796979891 26657324697520817695469837)
              ·
                refine ⟨9996496761570306635801189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26657324697520817695469837 9996496761570306635801189)
                ·
                  refine ⟨1874343142794432494212723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9996496761570306635801189 1874343142794432494212723)
                  ·
                    refine ⟨2811514714191648741319085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874343142794432494212723 2811514714191648741319085)
                    ·
                      refine ⟨1054318017821868277994657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811514714191648741319085 1054318017821868277994657)
                      ·
                        rfl

theorem cell23_2053277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2053277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053277 prefixEnd_2053277 := by exact prefixLift 2053277
  have htrace : WordTrace (prefixWord ++ tailWord_2053277) baseStart_2053277 baseEnd_2053277 := by
    simpa [prefixWord, tailWord_2053277, baseEnd_2053277] using wordTrace_append hprefix tailTrace_2053277
  have hstable : (prefixWord ++ tailWord_2053277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053277).length < 2 ^ (prefixWord ++ tailWord_2053277).sum := by decide
  have hdescent : baseEnd_2053277 < baseStart_2053277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053278 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_2053278 : Nat := 118140960795 + 2053278 * 2 ^ 59
def prefixEnd_2053278 : Nat := 4983230072969 + 3 ^ 40 * 2053278 * 2
def baseEnd_2053278 : Nat := 1054318531302522774082153

theorem tailTrace_2053278 : CollatzResearch.WordTrace tailWord_2053278 prefixEnd_2053278 1054318531302522774082153 := by
  unfold tailWord_2053278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361150131916494101136061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49926134036887968539392325 9361150131916494101136061)
  ·
    refine ⟨3510431299468685287926023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9361150131916494101136061 3510431299468685287926023)
    ·
      refine ⟨5265646949203027931889035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510431299468685287926023 5265646949203027931889035)
      ·
        refine ⟨7898470423804541897833553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265646949203027931889035 7898470423804541897833553)
        ·
          refine ⟨5923852817853406423375165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898470423804541897833553 5923852817853406423375165)
          ·
            refine ⟨2221444806695027408765687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5923852817853406423375165 2221444806695027408765687)
            ·
              refine ⟨3332167210042541113148531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221444806695027408765687 3332167210042541113148531)
              ·
                refine ⟨4998250815063811669722797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332167210042541113148531 4998250815063811669722797)
                ·
                  refine ⟨1874344055648929376146049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4998250815063811669722797 1874344055648929376146049)
                  ·
                    refine ⟨1405758041736697032109537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874344055648929376146049 1405758041736697032109537)
                    ·
                      refine ⟨1054318531302522774082153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405758041736697032109537 1054318531302522774082153)
                      ·
                        rfl

theorem cell23_2053278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_2053278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053278 prefixEnd_2053278 := by exact prefixLift 2053278
  have htrace : WordTrace (prefixWord ++ tailWord_2053278) baseStart_2053278 baseEnd_2053278 := by
    simpa [prefixWord, tailWord_2053278, baseEnd_2053278] using wordTrace_append hprefix tailTrace_2053278
  have hstable : (prefixWord ++ tailWord_2053278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053278).length < 2 ^ (prefixWord ++ tailWord_2053278).sum := by decide
  have hdescent : baseEnd_2053278 < baseStart_2053278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053320 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2053320 : Nat := 118140960795 + 2053320 * 2 ^ 59
def prefixEnd_2053320 : Nat := 4983230072969 + 3 ^ 40 * 2053320 * 2
def baseEnd_2053320 : Nat := 1054340097490011609756959

theorem tailTrace_2053320 : CollatzResearch.WordTrace tailWord_2053320 prefixEnd_2053320 1054340097490011609756959 := by
  unfold tailWord_2053320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37445366460589896991058707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49927155280786529321411609 37445366460589896991058707)
  ·
    refine ⟨56168049690884845486588061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37445366460589896991058707 56168049690884845486588061)
    ·
      refine ⟨21063018634081817057470523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56168049690884845486588061 21063018634081817057470523)
      ·
        refine ⟨31594527951122725586205785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063018634081817057470523 31594527951122725586205785)
        ·
          refine ⟨23695895963342044189654339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31594527951122725586205785 23695895963342044189654339)
          ·
            refine ⟨35543843945013066284481509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23695895963342044189654339 35543843945013066284481509)
            ·
              refine ⟨6664470739689949928340283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35543843945013066284481509 6664470739689949928340283)
              ·
                refine ⟨9996706109534924892510425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664470739689949928340283 9996706109534924892510425)
                ·
                  refine ⟨7497529582151193669382819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9996706109534924892510425 7497529582151193669382819)
                  ·
                    refine ⟨11246294373226790504074229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497529582151193669382819 11246294373226790504074229)
                    ·
                      refine ⟨1054340097490011609756959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11246294373226790504074229 1054340097490011609756959)
                      ·
                        rfl

theorem cell23_2053320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2053320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053320 prefixEnd_2053320 := by exact prefixLift 2053320
  have htrace : WordTrace (prefixWord ++ tailWord_2053320) baseStart_2053320 baseEnd_2053320 := by
    simpa [prefixWord, tailWord_2053320, baseEnd_2053320] using wordTrace_append hprefix tailTrace_2053320
  have hstable : (prefixWord ++ tailWord_2053320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053320).length < 2 ^ (prefixWord ++ tailWord_2053320).sum := by decide
  have hdescent : baseEnd_2053320 < baseStart_2053320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053323 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 11]
def baseStart_2053323 : Nat := 118140960795 + 2053323 * 2 ^ 59
def prefixEnd_2053323 : Nat := 4983230072969 + 3 ^ 40 * 2053323 * 2
def baseEnd_2053323 : Nat := 117149070881330566446605

theorem tailTrace_2053323 : CollatzResearch.WordTrace tailWord_2053323 prefixEnd_2053323 117149070881330566446605 := by
  unfold tailWord_2053323
  simp only [CollatzResearch.WordTrace]
  refine ⟨74890842340168925494476623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49927228226779283662984415 74890842340168925494476623)
  ·
    refine ⟨112336263510253388241714935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74890842340168925494476623 112336263510253388241714935)
    ·
      refine ⟨168504395265380082362572403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112336263510253388241714935 168504395265380082362572403)
      ·
        refine ⟨252756592898070123543858605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168504395265380082362572403 252756592898070123543858605)
        ·
          refine ⟨94783722336776296328946977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252756592898070123543858605 94783722336776296328946977)
          ·
            refine ⟨71087791752582222246710233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94783722336776296328946977 71087791752582222246710233)
            ·
              refine ⟨53315843814436666685032675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71087791752582222246710233 53315843814436666685032675)
              ·
                refine ⟨79973765721655000027549013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53315843814436666685032675 79973765721655000027549013)
                ·
                  refine ⟨117149070881330566446605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 79973765721655000027549013 117149070881330566446605)
                  ·
                    rfl

theorem cell23_2053323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_2053323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053323 prefixEnd_2053323 := by exact prefixLift 2053323
  have htrace : WordTrace (prefixWord ++ tailWord_2053323) baseStart_2053323 baseEnd_2053323 := by
    simpa [prefixWord, tailWord_2053323, baseEnd_2053323] using wordTrace_append hprefix tailTrace_2053323
  have hstable : (prefixWord ++ tailWord_2053323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053323).length < 2 ^ (prefixWord ++ tailWord_2053323).sum := by decide
  have hdescent : baseEnd_2053323 < baseStart_2053323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053351 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2053351 : Nat := 118140960795 + 2053351 * 2 ^ 59
def prefixEnd_2053351 : Nat := 4983230072969 + 3 ^ 40 * 2053351 * 2
def baseEnd_2053351 : Nat := 1054356015390300988469317

theorem tailTrace_2053351 : CollatzResearch.WordTrace tailWord_2053351 prefixEnd_2053351 1054356015390300988469317 := by
  unfold tailWord_2053351
  simp only [CollatzResearch.WordTrace]
  refine ⟨74891863584067486276495907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49927909056044990850997271 74891863584067486276495907)
  ·
    refine ⟨112337795376101229414743861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74891863584067486276495907 112337795376101229414743861)
    ·
      refine ⟨10531668316509490257632237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112337795376101229414743861 10531668316509490257632237)
      ·
        refine ⟨3949375618691058846612089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10531668316509490257632237 3949375618691058846612089)
        ·
          refine ⟨2962031714018294134959067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949375618691058846612089 2962031714018294134959067)
          ·
            refine ⟨4443047571027441202438601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962031714018294134959067 4443047571027441202438601)
            ·
              refine ⟨3332285678270580901828951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443047571027441202438601 3332285678270580901828951)
              ·
                refine ⟨4998428517405871352743427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332285678270580901828951 4998428517405871352743427)
                ·
                  refine ⟨7497642776108807029115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998428517405871352743427 7497642776108807029115141)
                  ·
                    refine ⟨1405808020520401317959089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497642776108807029115141 1405808020520401317959089)
                    ·
                      refine ⟨1054356015390300988469317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405808020520401317959089 1054356015390300988469317)
                      ·
                        rfl

theorem cell23_2053351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2053351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053351 prefixEnd_2053351 := by exact prefixLift 2053351
  have htrace : WordTrace (prefixWord ++ tailWord_2053351) baseStart_2053351 baseEnd_2053351 := by
    simpa [prefixWord, tailWord_2053351, baseEnd_2053351] using wordTrace_append hprefix tailTrace_2053351
  have hstable : (prefixWord ++ tailWord_2053351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053351).length < 2 ^ (prefixWord ++ tailWord_2053351).sum := by decide
  have hdescent : baseEnd_2053351 < baseStart_2053351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053357 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2053357 : Nat := 118140960795 + 2053357 * 2 ^ 59
def prefixEnd_2053357 : Nat := 4983230072969 + 3 ^ 40 * 2053357 * 2
def baseEnd_2053357 : Nat := 117151010697136440554921

theorem tailTrace_2053357 : CollatzResearch.WordTrace tailWord_2053357 prefixEnd_2053357 117151010697136440554921 := by
  unfold tailWord_2053357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74892082422045749301214325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49928054948030499534142883 74892082422045749301214325)
  ·
    refine ⟨7021132727066788996988843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74892082422045749301214325 7021132727066788996988843)
    ·
      refine ⟨10531699090600183495483265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021132727066788996988843 10531699090600183495483265)
      ·
        refine ⟨7898774317950137621612449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10531699090600183495483265 7898774317950137621612449)
        ·
          refine ⟨5924080738462603216209337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898774317950137621612449 5924080738462603216209337)
          ·
            refine ⟨4443060553846952412157003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924080738462603216209337 4443060553846952412157003)
            ·
              refine ⟨6664590830770428618235505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443060553846952412157003 6664590830770428618235505)
              ·
                refine ⟨4998443123077821463676629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6664590830770428618235505 4998443123077821463676629)
                ·
                  refine ⟨117151010697136440554921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4998443123077821463676629 117151010697136440554921)
                  ·
                    rfl

theorem cell23_2053357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2053357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053357 prefixEnd_2053357 := by exact prefixLift 2053357
  have htrace : WordTrace (prefixWord ++ tailWord_2053357) baseStart_2053357 baseEnd_2053357 := by
    simpa [prefixWord, tailWord_2053357, baseEnd_2053357] using wordTrace_append hprefix tailTrace_2053357
  have hstable : (prefixWord ++ tailWord_2053357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053357).length < 2 ^ (prefixWord ++ tailWord_2053357).sum := by decide
  have hdescent : baseEnd_2053357 < baseStart_2053357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053370 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_2053370 : Nat := 118140960795 + 2053370 * 2 ^ 59
def prefixEnd_2053370 : Nat := 4983230072969 + 3 ^ 40 * 2053370 * 2
def baseEnd_2053370 : Nat := 351455257174245471377243

theorem tailTrace_2053370 : CollatzResearch.WordTrace tailWord_2053370 prefixEnd_2053370 351455257174245471377243 := by
  unfold tailWord_2053370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723139142749663130359391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49928371047332435014291709 18723139142749663130359391)
  ·
    refine ⟨28084708714124494695539087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18723139142749663130359391 28084708714124494695539087)
    ·
      refine ⟨42127063071186742043308631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28084708714124494695539087 42127063071186742043308631)
      ·
        refine ⟨63190594606780113064962947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42127063071186742043308631 63190594606780113064962947)
        ·
          refine ⟨94785891910170169597444421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63190594606780113064962947 94785891910170169597444421)
          ·
            refine ⟨17772354733156906799520829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94785891910170169597444421 17772354733156906799520829)
            ·
              refine ⟨6664633024933840049820311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17772354733156906799520829 6664633024933840049820311)
              ·
                refine ⟨9996949537400760074730467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664633024933840049820311 9996949537400760074730467)
                ·
                  refine ⟨14995424306101140112095701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9996949537400760074730467 14995424306101140112095701)
                  ·
                    refine ⟨351455257174245471377243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14995424306101140112095701 351455257174245471377243)
                    ·
                      rfl

theorem cell23_2053370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_2053370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053370 prefixEnd_2053370 := by exact prefixLift 2053370
  have htrace : WordTrace (prefixWord ++ tailWord_2053370) baseStart_2053370 baseEnd_2053370 := by
    simpa [prefixWord, tailWord_2053370, baseEnd_2053370] using wordTrace_append hprefix tailTrace_2053370
  have hstable : (prefixWord ++ tailWord_2053370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053370).length < 2 ^ (prefixWord ++ tailWord_2053370).sum := by decide
  have hdescent : baseEnd_2053370 < baseStart_2053370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053374 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_2053374 : Nat := 118140960795 + 2053374 * 2 ^ 59
def prefixEnd_2053374 : Nat := 4983230072969 + 3 ^ 40 * 2053374 * 2
def baseEnd_2053374 : Nat := 117151980605039377609079

theorem tailTrace_2053374 : CollatzResearch.WordTrace tailWord_2053374 prefixEnd_2053374 117151980605039377609079 := by
  unfold tailWord_2053374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361587807873020150572897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49928468308656107469722117 9361587807873020150572897)
  ·
    refine ⟨7021190855904765112929673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9361587807873020150572897 7021190855904765112929673)
    ·
      refine ⟨5265893141928573834697255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7021190855904765112929673 5265893141928573834697255)
      ·
        refine ⟨7898839712892860752045883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265893141928573834697255 7898839712892860752045883)
        ·
          refine ⟨11848259569339291128068825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898839712892860752045883 11848259569339291128068825)
          ·
            refine ⟨8886194677004468346051619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11848259569339291128068825 8886194677004468346051619)
            ·
              refine ⟨13329292015506702519077429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886194677004468346051619 13329292015506702519077429)
              ·
                refine ⟨1249621126453753361163509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13329292015506702519077429 1249621126453753361163509)
                ·
                  refine ⟨117151980605039377609079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249621126453753361163509 117151980605039377609079)
                  ·
                    rfl

theorem cell23_2053374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_2053374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053374 prefixEnd_2053374 := by exact prefixLift 2053374
  have htrace : WordTrace (prefixWord ++ tailWord_2053374) baseStart_2053374 baseEnd_2053374 := by
    simpa [prefixWord, tailWord_2053374, baseEnd_2053374] using wordTrace_append hprefix tailTrace_2053374
  have hstable : (prefixWord ++ tailWord_2053374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053374).length < 2 ^ (prefixWord ++ tailWord_2053374).sum := by decide
  have hdescent : baseEnd_2053374 < baseStart_2053374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053420 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_2053420 : Nat := 118140960795 + 2053420 * 2 ^ 59
def prefixEnd_2053420 : Nat := 4983230072969 + 3 ^ 40 * 2053420 * 2
def baseEnd_2053420 : Nat := 1054391445555461218506499

theorem tailTrace_2053420 : CollatzResearch.WordTrace tailWord_2053420 prefixEnd_2053420 1054391445555461218506499 := by
  unfold tailWord_2053420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37447190110408755530378857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49929586813878340707171809 37447190110408755530378857)
  ·
    refine ⟨28085392582806566647784143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37447190110408755530378857 28085392582806566647784143)
    ·
      refine ⟨42128088874209849971676215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28085392582806566647784143 42128088874209849971676215)
      ·
        refine ⟨63192133311314774957514323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42128088874209849971676215 63192133311314774957514323)
        ·
          refine ⟨94788199966972162436271485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63192133311314774957514323 94788199966972162436271485)
          ·
            refine ⟨35545574987614560913601807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94788199966972162436271485 35545574987614560913601807)
            ·
              refine ⟨53318362481421841370402711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35545574987614560913601807 53318362481421841370402711)
              ·
                refine ⟨79977543722132762055604067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53318362481421841370402711 79977543722132762055604067)
                ·
                  refine ⟨119966315583199143083406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79977543722132762055604067 119966315583199143083406101)
                  ·
                    refine ⟨5623421042962459832034661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119966315583199143083406101 5623421042962459832034661)
                    ·
                      refine ⟨1054391445555461218506499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5623421042962459832034661 1054391445555461218506499)
                      ·
                        rfl

theorem cell23_2053420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_2053420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053420 prefixEnd_2053420 := by exact prefixLift 2053420
  have htrace : WordTrace (prefixWord ++ tailWord_2053420) baseStart_2053420 baseEnd_2053420 := by
    simpa [prefixWord, tailWord_2053420, baseEnd_2053420] using wordTrace_append hprefix tailTrace_2053420
  have hstable : (prefixWord ++ tailWord_2053420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053420).length < 2 ^ (prefixWord ++ tailWord_2053420).sum := by decide
  have hdescent : baseEnd_2053420 < baseStart_2053420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053427 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3]
def baseStart_2053427 : Nat := 118140960795 + 2053427 * 2 ^ 59
def prefixEnd_2053427 : Nat := 4983230072969 + 3 ^ 40 * 2053427 * 2
def baseEnd_2053427 : Nat := 1054395039920042691118967

theorem tailTrace_2053427 : CollatzResearch.WordTrace tailWord_2053427 prefixEnd_2053427 1054395039920042691118967 := by
  unfold tailWord_2053427
  simp only [CollatzResearch.WordTrace]
  refine ⟨74894635531792151256262535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49929757021194767504175023 74894635531792151256262535)
  ·
    refine ⟨112341953297688226884393803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74894635531792151256262535 112341953297688226884393803)
    ·
      refine ⟨168512929946532340326590705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112341953297688226884393803 168512929946532340326590705)
      ·
        refine ⟨126384697459899255244943029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168512929946532340326590705 126384697459899255244943029)
        ·
          refine ⟨11848565386865555179213409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126384697459899255244943029 11848565386865555179213409)
          ·
            refine ⟨8886424040149166384410057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11848565386865555179213409 8886424040149166384410057)
            ·
              refine ⟨6664818030111874788307543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8886424040149166384410057 6664818030111874788307543)
              ·
                refine ⟨9997227045167812182461315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664818030111874788307543 9997227045167812182461315)
                ·
                  refine ⟨14995840567751718273691973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997227045167812182461315 14995840567751718273691973)
                  ·
                    refine ⟨2811720106453447176317245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14995840567751718273691973 2811720106453447176317245)
                    ·
                      refine ⟨1054395039920042691118967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811720106453447176317245 1054395039920042691118967)
                      ·
                        rfl

theorem cell23_2053427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_2053427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053427 prefixEnd_2053427 := by exact prefixLift 2053427
  have htrace : WordTrace (prefixWord ++ tailWord_2053427) baseStart_2053427 baseEnd_2053427 := by
    simpa [prefixWord, tailWord_2053427, baseEnd_2053427] using wordTrace_append hprefix tailTrace_2053427
  have hstable : (prefixWord ++ tailWord_2053427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053427).length < 2 ^ (prefixWord ++ tailWord_2053427).sum := by decide
  have hdescent : baseEnd_2053427 < baseStart_2053427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053450 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2053450 : Nat := 118140960795 + 2053450 * 2 ^ 59
def prefixEnd_2053450 : Nat := 4983230072969 + 3 ^ 40 * 2053450 * 2
def baseEnd_2053450 : Nat := 1054406849975096101131361

theorem tailTrace_2053450 : CollatzResearch.WordTrace tailWord_2053450 prefixEnd_2053450 1054406849975096101131361 := by
  unfold tailWord_2053450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723868602677206546087451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49930316273805884122899869 18723868602677206546087451)
  ·
    refine ⟨28085802904015809819131177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18723868602677206546087451 28085802904015809819131177)
    ·
      refine ⟨21064352178011857364348383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28085802904015809819131177 21064352178011857364348383)
      ·
        refine ⟨31596528267017786046522575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21064352178011857364348383 31596528267017786046522575)
        ·
          refine ⟨47394792400526679069783863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31596528267017786046522575 47394792400526679069783863)
          ·
            refine ⟨71092188600790018604675795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47394792400526679069783863 71092188600790018604675795)
            ·
              refine ⟨106638282901185027907013693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71092188600790018604675795 106638282901185027907013693)
              ·
                refine ⟨39989356087944385465130135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106638282901185027907013693 39989356087944385465130135)
                ·
                  refine ⟨59984034131916578197695203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39989356087944385465130135 59984034131916578197695203)
                  ·
                    refine ⟨89976051197874867296542805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59984034131916578197695203 89976051197874867296542805)
                    ·
                      refine ⟨1054406849975096101131361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 89976051197874867296542805 1054406849975096101131361)
                      ·
                        rfl

theorem cell23_2053450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2053450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053450 prefixEnd_2053450 := by exact prefixLift 2053450
  have htrace : WordTrace (prefixWord ++ tailWord_2053450) baseStart_2053450 baseEnd_2053450 := by
    simpa [prefixWord, tailWord_2053450, baseEnd_2053450] using wordTrace_append hprefix tailTrace_2053450
  have hstable : (prefixWord ++ tailWord_2053450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053450).length < 2 ^ (prefixWord ++ tailWord_2053450).sum := by decide
  have hdescent : baseEnd_2053450 < baseStart_2053450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053477 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_2053477 : Nat := 118140960795 + 2053477 * 2 ^ 59
def prefixEnd_2053477 : Nat := 4983230072969 + 3 ^ 40 * 2053477 * 2
def baseEnd_2053477 : Nat := 351473571317589165164579

theorem tailTrace_2053477 : CollatzResearch.WordTrace tailWord_2053477 prefixEnd_2053477 351473571317589165164579 := by
  unfold tailWord_2053477
  simp only [CollatzResearch.WordTrace]
  refine ⟨74896459181611009795582685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49930972787740673197055123 74896459181611009795582685)
  ·
    refine ⟨28086172193104128673343507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74896459181611009795582685 28086172193104128673343507)
    ·
      refine ⟨42129258289656193010015261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28086172193104128673343507 42129258289656193010015261)
      ·
        refine ⟨15798471858621072378755723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42129258289656193010015261 15798471858621072378755723)
        ·
          refine ⟨23697707787931608568133585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15798471858621072378755723 23697707787931608568133585)
          ·
            refine ⟨17773280840948706426100189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23697707787931608568133585 17773280840948706426100189)
            ·
              refine ⟨6664980315355764909787571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17773280840948706426100189 6664980315355764909787571)
              ·
                refine ⟨9997470473033647364681357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664980315355764909787571 9997470473033647364681357)
                ·
                  refine ⟨3749051427387617761755509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9997470473033647364681357 3749051427387617761755509)
                  ·
                    refine ⟨351473571317589165164579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3749051427387617761755509 351473571317589165164579)
                    ·
                      rfl

theorem cell23_2053477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_2053477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053477 prefixEnd_2053477 := by exact prefixLift 2053477
  have htrace : WordTrace (prefixWord ++ tailWord_2053477) baseStart_2053477 baseEnd_2053477 := by
    simpa [prefixWord, tailWord_2053477, baseEnd_2053477] using wordTrace_append hprefix tailTrace_2053477
  have hstable : (prefixWord ++ tailWord_2053477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053477).length < 2 ^ (prefixWord ++ tailWord_2053477).sum := by decide
  have hdescent : baseEnd_2053477 < baseStart_2053477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053508 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_2053508 : Nat := 118140960795 + 2053508 * 2 ^ 59
def prefixEnd_2053508 : Nat := 4983230072969 + 3 ^ 40 * 2053508 * 2
def baseEnd_2053508 : Nat := 1054436631853056874206095

theorem tailTrace_2053508 : CollatzResearch.WordTrace tailWord_2053508 prefixEnd_2053508 1054436631853056874206095 := by
  unfold tailWord_2053508
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448794922249351044980589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49931726562999134726640785 37448794922249351044980589)
  ·
    refine ⟨14043298095843506641867721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37448794922249351044980589 14043298095843506641867721)
    ·
      refine ⟨10532473571882629981400791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14043298095843506641867721 10532473571882629981400791)
      ·
        refine ⟨15798710357823944972101187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532473571882629981400791 15798710357823944972101187)
        ·
          refine ⟨23698065536735917458151781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15798710357823944972101187 23698065536735917458151781)
          ·
            refine ⟨4443387288137984523403459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23698065536735917458151781 4443387288137984523403459)
            ·
              refine ⟨6665080932206976785105189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443387288137984523403459 6665080932206976785105189)
              ·
                refine ⟨1249702674788808147207223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6665080932206976785105189 1249702674788808147207223)
                ·
                  refine ⟨1874554012183212220810835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249702674788808147207223 1874554012183212220810835)
                  ·
                    refine ⟨2811831018274818331216253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874554012183212220810835 2811831018274818331216253)
                    ·
                      refine ⟨1054436631853056874206095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811831018274818331216253 1054436631853056874206095)
                      ·
                        rfl

theorem cell23_2053508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_2053508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053508 prefixEnd_2053508 := by exact prefixLift 2053508
  have htrace : WordTrace (prefixWord ++ tailWord_2053508) baseStart_2053508 baseEnd_2053508 := by
    simpa [prefixWord, tailWord_2053508, baseEnd_2053508] using wordTrace_append hprefix tailTrace_2053508
  have hstable : (prefixWord ++ tailWord_2053508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053508).length < 2 ^ (prefixWord ++ tailWord_2053508).sum := by decide
  have hdescent : baseEnd_2053508 < baseStart_2053508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053524 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2053524 : Nat := 118140960795 + 2053524 * 2 ^ 59
def prefixEnd_2053524 : Nat := 4983230072969 + 3 ^ 40 * 2053524 * 2
def baseEnd_2053524 : Nat := 351481615847842937202007

theorem tailTrace_2053524 : CollatzResearch.WordTrace tailWord_2053524 prefixEnd_2053524 351481615847842937202007 := by
  unfold tailWord_2053524
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449086706220368411271813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49932115608293824548362417 37449086706220368411271813)
  ·
    refine ⟨7021703757416319077113465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37449086706220368411271813 7021703757416319077113465)
    ·
      refine ⟨5266277818062239307835099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7021703757416319077113465 5266277818062239307835099)
      ·
        refine ⟨7899416727093358961752649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266277818062239307835099 7899416727093358961752649)
        ·
          refine ⟨5924562545320019221314487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899416727093358961752649 5924562545320019221314487)
          ·
            refine ⟨8886843817980028831971731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924562545320019221314487 8886843817980028831971731)
            ·
              refine ⟨13330265726970043247957597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886843817980028831971731 13330265726970043247957597)
              ·
                refine ⟨4998849647613766217984099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13330265726970043247957597 4998849647613766217984099)
                ·
                  refine ⟨7498274471420649326976149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998849647613766217984099 7498274471420649326976149)
                  ·
                    refine ⟨351481615847842937202007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7498274471420649326976149 351481615847842937202007)
                    ·
                      rfl

theorem cell23_2053524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2053524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053524 prefixEnd_2053524 := by exact prefixLift 2053524
  have htrace : WordTrace (prefixWord ++ tailWord_2053524) baseStart_2053524 baseEnd_2053524 := by
    simpa [prefixWord, tailWord_2053524, baseEnd_2053524] using wordTrace_append hprefix tailTrace_2053524
  have hstable : (prefixWord ++ tailWord_2053524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053524).length < 2 ^ (prefixWord ++ tailWord_2053524).sum := by decide
  have hdescent : baseEnd_2053524 < baseStart_2053524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053547 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3]
def baseStart_2053547 : Nat := 118140960795 + 2053547 * 2 ^ 59
def prefixEnd_2053547 : Nat := 4983230072969 + 3 ^ 40 * 2053547 * 2
def baseEnd_2053547 : Nat := 1054456657598582221618415

theorem tailTrace_2053547 : CollatzResearch.WordTrace tailWord_2053547 prefixEnd_2053547 1054456657598582221618415 := by
  unfold tailWord_2053547
  simp only [CollatzResearch.WordTrace]
  refine ⟨74899012291357411750630895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49932674860904941167087263 74899012291357411750630895)
  ·
    refine ⟨112348518437036117625946343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74899012291357411750630895 112348518437036117625946343)
    ·
      refine ⟨168522777655554176438919515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112348518437036117625946343 168522777655554176438919515)
      ·
        refine ⟨252784166483331264658379273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168522777655554176438919515 252784166483331264658379273)
        ·
          refine ⟨189588124862498448493784455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252784166483331264658379273 189588124862498448493784455)
          ·
            refine ⟨284382187293747672740676683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189588124862498448493784455 284382187293747672740676683)
            ·
              refine ⟨426573280940621509111015025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284382187293747672740676683 426573280940621509111015025)
              ·
                refine ⟨319929960705466131833261269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426573280940621509111015025 319929960705466131833261269)
                ·
                  refine ⟨7498358454034362464842061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319929960705466131833261269 7498358454034362464842061)
                  ·
                    refine ⟨2811884420262885924315773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7498358454034362464842061 2811884420262885924315773)
                    ·
                      refine ⟨1054456657598582221618415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2811884420262885924315773 1054456657598582221618415)
                      ·
                        rfl

theorem cell23_2053547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].length) (baseStart_2053547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053547 prefixEnd_2053547 := by exact prefixLift 2053547
  have htrace : WordTrace (prefixWord ++ tailWord_2053547) baseStart_2053547 baseEnd_2053547 := by
    simpa [prefixWord, tailWord_2053547, baseEnd_2053547] using wordTrace_append hprefix tailTrace_2053547
  have hstable : (prefixWord ++ tailWord_2053547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053547).length < 2 ^ (prefixWord ++ tailWord_2053547).sum := by decide
  have hdescent : baseEnd_2053547 < baseStart_2053547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053548 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_2053548 : Nat := 118140960795 + 2053548 * 2 ^ 59
def prefixEnd_2053548 : Nat := 4983230072969 + 3 ^ 40 * 2053548 * 2
def baseEnd_2053548 : Nat := 1054457171079236717705911

theorem tailTrace_2053548 : CollatzResearch.WordTrace tailWord_2053548 prefixEnd_2053548 1054457171079236717705911 := by
  unfold tailWord_2053548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449524382176894460708649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49932699176235859280944865 37449524382176894460708649)
  ·
    refine ⟨28087143286632670845531487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37449524382176894460708649 28087143286632670845531487)
    ·
      refine ⟨42130714929949006268297231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28087143286632670845531487 42130714929949006268297231)
      ·
        refine ⟨63196072394923509402445847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42130714929949006268297231 63196072394923509402445847)
        ·
          refine ⟨94794108592385264103668771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63196072394923509402445847 94794108592385264103668771)
          ·
            refine ⟨142191162888577896155503157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94794108592385264103668771 142191162888577896155503157)
            ·
              refine ⟨13330421520804177764578421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142191162888577896155503157 13330421520804177764578421)
              ·
                refine ⟨1249727017575391665429227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13330421520804177764578421 1249727017575391665429227)
                ·
                  refine ⟨1874590526363087498143841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249727017575391665429227 1874590526363087498143841)
                  ·
                    refine ⟨1405942894772315623607881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874590526363087498143841 1405942894772315623607881)
                    ·
                      refine ⟨1054457171079236717705911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1405942894772315623607881 1054457171079236717705911)
                      ·
                        rfl

theorem cell23_2053548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_2053548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053548 prefixEnd_2053548 := by exact prefixLift 2053548
  have htrace : WordTrace (prefixWord ++ tailWord_2053548) baseStart_2053548 baseEnd_2053548 := by
    simpa [prefixWord, tailWord_2053548, baseEnd_2053548] using wordTrace_append hprefix tailTrace_2053548
  have hstable : (prefixWord ++ tailWord_2053548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053548).length < 2 ^ (prefixWord ++ tailWord_2053548).sum := by decide
  have hdescent : baseEnd_2053548 < baseStart_2053548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053588 : List Nat := [2, 4, 1, 2, 4, 1, 2, 7]
def baseStart_2053588 : Nat := 118140960795 + 2053588 * 2 ^ 59
def prefixEnd_2053588 : Nat := 4983230072969 + 3 ^ 40 * 2053588 * 2
def baseEnd_2053588 : Nat := 39054730011311724489101

theorem tailTrace_2053588 : CollatzResearch.WordTrace tailWord_2053588 prefixEnd_2053588 39054730011311724489101 := by
  unfold tailWord_2053588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37450253842104437876436709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49933671789472583835248945 37450253842104437876436709)
  ·
    refine ⟨7021922595394582101831883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37450253842104437876436709 7021922595394582101831883)
    ·
      refine ⟨10532883893091873152747825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7021922595394582101831883 10532883893091873152747825)
      ·
        refine ⟨7899662919818904864560869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10532883893091873152747825 7899662919818904864560869)
        ·
          refine ⟨1481186797466044662105163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7899662919818904864560869 1481186797466044662105163)
          ·
            refine ⟨2221780196199066993157745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481186797466044662105163 2221780196199066993157745)
            ·
              refine ⟨1666335147149300244868309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221780196199066993157745 1666335147149300244868309)
              ·
                refine ⟨39054730011311724489101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1666335147149300244868309 39054730011311724489101)
                ·
                  rfl

theorem cell23_2053588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 7].length) (baseStart_2053588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053588 prefixEnd_2053588 := by exact prefixLift 2053588
  have htrace : WordTrace (prefixWord ++ tailWord_2053588) baseStart_2053588 baseEnd_2053588 := by
    simpa [prefixWord, tailWord_2053588, baseEnd_2053588] using wordTrace_append hprefix tailTrace_2053588
  have hstable : (prefixWord ++ tailWord_2053588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053588).length < 2 ^ (prefixWord ++ tailWord_2053588).sum := by decide
  have hdescent : baseEnd_2053588 < baseStart_2053588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053661 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 5]
def baseStart_2053661 : Nat := 118140960795 + 2053661 * 2 ^ 59
def prefixEnd_2053661 : Nat := 4983230072969 + 3 ^ 40 * 2053661 * 2
def baseEnd_2053661 : Nat := 117168354932577197288099

theorem tailTrace_2053661 : CollatzResearch.WordTrace tailWord_2053661 prefixEnd_2053661 117168354932577197288099 := by
  unfold tailWord_2053661
  simp only [CollatzResearch.WordTrace]
  refine ⟨74903170212944409220280837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49935446808629606146853891 74903170212944409220280837)
  ·
    refine ⟨14044344414927076728802657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74903170212944409220280837 14044344414927076728802657)
    ·
      refine ⟨10533258311195307546601993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14044344414927076728802657 10533258311195307546601993)
      ·
        refine ⟨7899943733396480659951495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10533258311195307546601993 7899943733396480659951495)
        ·
          refine ⟨11849915600094720989927243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899943733396480659951495 11849915600094720989927243)
          ·
            refine ⟨17774873400142081484890865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849915600094720989927243 17774873400142081484890865)
            ·
              refine ⟨13331155050106561113668149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774873400142081484890865 13331155050106561113668149)
              ·
                refine ⟨1249795785947490104406389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13331155050106561113668149 1249795785947490104406389)
                ·
                  refine ⟨117168354932577197288099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249795785947490104406389 117168354932577197288099)
                  ·
                    rfl

theorem cell23_2053661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_2053661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053661 prefixEnd_2053661 := by exact prefixLift 2053661
  have htrace : WordTrace (prefixWord ++ tailWord_2053661) baseStart_2053661 baseEnd_2053661 := by
    simpa [prefixWord, tailWord_2053661, baseEnd_2053661] using wordTrace_append hprefix tailTrace_2053661
  have hstable : (prefixWord ++ tailWord_2053661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053661).length < 2 ^ (prefixWord ++ tailWord_2053661).sum := by decide
  have hdescent : baseEnd_2053661 < baseStart_2053661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053672 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2053672 : Nat := 118140960795 + 2053672 * 2 ^ 59
def prefixEnd_2053672 : Nat := 4983230072969 + 3 ^ 40 * 2053672 * 2
def baseEnd_2053672 : Nat := 1054520842680394232555341

theorem tailTrace_2053672 : CollatzResearch.WordTrace tailWord_2053672 prefixEnd_2053672 1054520842680394232555341 := by
  unfold tailWord_2053672
  simp only [CollatzResearch.WordTrace]
  refine ⟨37451785707952279049465635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49935714277269705399287513 37451785707952279049465635)
  ·
    refine ⟨56177678561928418574198453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37451785707952279049465635 56177678561928418574198453)
    ·
      refine ⟨5266657365180789241331105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56177678561928418574198453 5266657365180789241331105)
      ·
        refine ⟨3949993023885591930998329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5266657365180789241331105 3949993023885591930998329)
        ·
          refine ⟨2962494767914193948248747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3949993023885591930998329 2962494767914193948248747)
          ·
            refine ⟨4443742151871290922373121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962494767914193948248747 4443742151871290922373121)
            ·
              refine ⟨3332806613903468191779841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443742151871290922373121 3332806613903468191779841)
              ·
                refine ⟨2499604960427601143834881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332806613903468191779841 2499604960427601143834881)
                ·
                  refine ⟨1874703720320700857876161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2499604960427601143834881 1874703720320700857876161)
                  ·
                    refine ⟨1406027790240525643407121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874703720320700857876161 1406027790240525643407121)
                    ·
                      refine ⟨1054520842680394232555341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406027790240525643407121 1054520842680394232555341)
                      ·
                        rfl

theorem cell23_2053672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2053672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053672 prefixEnd_2053672 := by exact prefixLift 2053672
  have htrace : WordTrace (prefixWord ++ tailWord_2053672) baseStart_2053672 baseEnd_2053672 := by
    simpa [prefixWord, tailWord_2053672, baseEnd_2053672] using wordTrace_append hprefix tailTrace_2053672
  have hstable : (prefixWord ++ tailWord_2053672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053672).length < 2 ^ (prefixWord ++ tailWord_2053672).sum := by decide
  have hdescent : baseEnd_2053672 < baseStart_2053672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053678 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_2053678 : Nat := 118140960795 + 2053678 * 2 ^ 59
def prefixEnd_2053678 : Nat := 4983230072969 + 3 ^ 40 * 2053678 * 2
def baseEnd_2053678 : Nat := 117169324840480134342257

theorem tailTrace_2053678 : CollatzResearch.WordTrace tailWord_2053678 prefixEnd_2053678 117169324840480134342257 := by
  unfold tailWord_2053678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362973781735352640456211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49935860169255214082433125 9362973781735352640456211)
  ·
    refine ⟨14044460672603028960684317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362973781735352640456211 14044460672603028960684317)
    ·
      refine ⟨5266672752226135860256619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14044460672603028960684317 5266672752226135860256619)
      ·
        refine ⟨7900009128339203790384929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266672752226135860256619 7900009128339203790384929)
        ·
          refine ⟨5925006846254402842788697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7900009128339203790384929 5925006846254402842788697)
          ·
            refine ⟨4443755134690802132091523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5925006846254402842788697 4443755134690802132091523)
            ·
              refine ⟨6665632702036203198137285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443755134690802132091523 6665632702036203198137285)
              ·
                refine ⟨1249806131631788099650741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6665632702036203198137285 1249806131631788099650741)
                ·
                  refine ⟨117169324840480134342257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1249806131631788099650741 117169324840480134342257)
                  ·
                    rfl

theorem cell23_2053678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_2053678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053678 prefixEnd_2053678 := by exact prefixLift 2053678
  have htrace : WordTrace (prefixWord ++ tailWord_2053678) baseStart_2053678 baseEnd_2053678 := by
    simpa [prefixWord, tailWord_2053678, baseEnd_2053678] using wordTrace_append hprefix tailTrace_2053678
  have hstable : (prefixWord ++ tailWord_2053678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053678).length < 2 ^ (prefixWord ++ tailWord_2053678).sum := by decide
  have hdescent : baseEnd_2053678 < baseStart_2053678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053738 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2053738 : Nat := 118140960795 + 2053738 * 2 ^ 59
def prefixEnd_2053738 : Nat := 4983230072969 + 3 ^ 40 * 2053738 * 2
def baseEnd_2053738 : Nat := 351518244134530324776679

theorem tailTrace_2053738 : CollatzResearch.WordTrace tailWord_2053738 prefixEnd_2053738 351518244134530324776679 := by
  unfold tailWord_2053738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726494658416362842708467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49937319089110300913889245 18726494658416362842708467)
  ·
    refine ⟨28089741987624544264062701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726494658416362842708467 28089741987624544264062701)
    ·
      refine ⟨10533653245359204099023513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28089741987624544264062701 10533653245359204099023513)
      ·
        refine ⟨7900239934019403074267635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10533653245359204099023513 7900239934019403074267635)
        ·
          refine ⟨11850359901029104611401453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7900239934019403074267635 11850359901029104611401453)
          ·
            refine ⟨4443884962885914229275545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11850359901029104611401453 4443884962885914229275545)
            ·
              refine ⟨3332913722164435671956659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443884962885914229275545 3332913722164435671956659)
              ·
                refine ⟨4999370583246653507934989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332913722164435671956659 4999370583246653507934989)
                ·
                  refine ⟨1874763968717495065475621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4999370583246653507934989 1874763968717495065475621)
                  ·
                    refine ⟨351518244134530324776679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1874763968717495065475621 351518244134530324776679)
                    ·
                      rfl

theorem cell23_2053738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2053738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053738 prefixEnd_2053738 := by exact prefixLift 2053738
  have htrace : WordTrace (prefixWord ++ tailWord_2053738) baseStart_2053738 baseEnd_2053738 := by
    simpa [prefixWord, tailWord_2053738, baseEnd_2053738] using wordTrace_append hprefix tailTrace_2053738
  have hstable : (prefixWord ++ tailWord_2053738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053738).length < 2 ^ (prefixWord ++ tailWord_2053738).sum := by decide
  have hdescent : baseEnd_2053738 < baseStart_2053738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053771 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 5, 2]
def baseStart_2053771 : Nat := 118140960795 + 2053771 * 2 ^ 59
def prefixEnd_2053771 : Nat := 4983230072969 + 3 ^ 40 * 2053771 * 2
def baseEnd_2053771 : Nat := 1054571677265189345217385

theorem tailTrace_2053771 : CollatzResearch.WordTrace tailWord_2053771 prefixEnd_2053771 1054571677265189345217385 := by
  unfold tailWord_2053771
  simp only [CollatzResearch.WordTrace]
  refine ⟨74907182242545898006785167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49938121495030598671190111 74907182242545898006785167)
  ·
    refine ⟨112360773363818847010177751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74907182242545898006785167 112360773363818847010177751)
    ·
      refine ⟨168541160045728270515266627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112360773363818847010177751 168541160045728270515266627)
      ·
        refine ⟨252811740068592405772899941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168541160045728270515266627 252811740068592405772899941)
        ·
          refine ⟨47402201262861076082418739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252811740068592405772899941 47402201262861076082418739)
          ·
            refine ⟨71103301894291614123628109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47402201262861076082418739 71103301894291614123628109)
            ·
              refine ⟨26663738210359355296360541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71103301894291614123628109 26663738210359355296360541)
              ·
                refine ⟨9998901828884758236135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26663738210359355296360541 9998901828884758236135203)
                ·
                  refine ⟨14998352743327137354202805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998901828884758236135203 14998352743327137354202805)
                  ·
                    refine ⟨1406095569686919126956513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14998352743327137354202805 1406095569686919126956513)
                    ·
                      refine ⟨1054571677265189345217385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406095569686919126956513 1054571677265189345217385)
                      ·
                        rfl

theorem cell23_2053771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 5, 2].length) (baseStart_2053771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053771 prefixEnd_2053771 := by exact prefixLift 2053771
  have htrace : WordTrace (prefixWord ++ tailWord_2053771) baseStart_2053771 baseEnd_2053771 := by
    simpa [prefixWord, tailWord_2053771, baseEnd_2053771] using wordTrace_append hprefix tailTrace_2053771
  have hstable : (prefixWord ++ tailWord_2053771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053771).length < 2 ^ (prefixWord ++ tailWord_2053771).sum := by decide
  have hdescent : baseEnd_2053771 < baseStart_2053771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053818 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_2053818 : Nat := 118140960795 + 2053818 * 2 ^ 59
def prefixEnd_2053818 : Nat := 4983230072969 + 3 ^ 40 * 2053818 * 2
def baseEnd_2053818 : Nat := 1054595810855950661329669

theorem tailTrace_2053818 : CollatzResearch.WordTrace tailWord_2053818 prefixEnd_2053818 1054595810855950661329669 := by
  unfold tailWord_2053818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18727224118343906258436527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49939264315583750022497405 18727224118343906258436527)
  ·
    refine ⟨28090836177515859387654791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18727224118343906258436527 28090836177515859387654791)
    ·
      refine ⟨42136254266273789081482187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090836177515859387654791 42136254266273789081482187)
      ·
        refine ⟨63204381399410683622223281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42136254266273789081482187 63204381399410683622223281)
        ·
          refine ⟨47403286049558012716667461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63204381399410683622223281 47403286049558012716667461)
          ·
            refine ⟨8888116134292127384375149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47403286049558012716667461 8888116134292127384375149)
            ·
              refine ⟨3333043550359547769140681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8888116134292127384375149 3333043550359547769140681)
              ·
                refine ⟨2499782662769660826855511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333043550359547769140681 2499782662769660826855511)
                ·
                  refine ⟨3749673994154491240283267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499782662769660826855511 3749673994154491240283267)
                  ·
                    refine ⟨5624510991231736860424901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3749673994154491240283267 5624510991231736860424901)
                    ·
                      refine ⟨1054595810855950661329669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5624510991231736860424901 1054595810855950661329669)
                      ·
                        rfl

theorem cell23_2053818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_2053818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053818 prefixEnd_2053818 := by exact prefixLift 2053818
  have htrace : WordTrace (prefixWord ++ tailWord_2053818) baseStart_2053818 baseEnd_2053818 := by
    simpa [prefixWord, tailWord_2053818, baseEnd_2053818] using wordTrace_append hprefix tailTrace_2053818
  have hstable : (prefixWord ++ tailWord_2053818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053818).length < 2 ^ (prefixWord ++ tailWord_2053818).sum := by decide
  have hdescent : baseEnd_2053818 < baseStart_2053818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053824 : List Nat := [2, 1, 1, 2, 4, 1, 1, 11]
def baseStart_2053824 : Nat := 118140960795 + 2053824 * 2 ^ 59
def prefixEnd_2053824 : Nat := 4983230072969 + 3 ^ 40 * 2053824 * 2
def baseEnd_2053824 : Nat := 39059218212588060661283

theorem tailTrace_2053824 : CollatzResearch.WordTrace tailWord_2053824 prefixEnd_2053824 39059218212588060661283 := by
  unfold tailWord_2053824
  simp only [CollatzResearch.WordTrace]
  refine ⟨37454557655676944029232263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49939410207569258705643017 37454557655676944029232263)
  ·
    refine ⟨56181836483515416043848395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37454557655676944029232263 56181836483515416043848395)
    ·
      refine ⟨84272754725273124065772593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56181836483515416043848395 84272754725273124065772593)
      ·
        refine ⟨63204566043954843049329445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84272754725273124065772593 63204566043954843049329445)
        ·
          refine ⟨11850856133241533071749271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63204566043954843049329445 11850856133241533071749271)
          ·
            refine ⟨17776284199862299607623907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11850856133241533071749271 17776284199862299607623907)
            ·
              refine ⟨26664426299793449411435861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17776284199862299607623907 26664426299793449411435861)
              ·
                refine ⟨39059218212588060661283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26664426299793449411435861 39059218212588060661283)
                ·
                  rfl

theorem cell23_2053824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_2053824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053824 prefixEnd_2053824 := by exact prefixLift 2053824
  have htrace : WordTrace (prefixWord ++ tailWord_2053824) baseStart_2053824 baseEnd_2053824 := by
    simpa [prefixWord, tailWord_2053824, baseEnd_2053824] using wordTrace_append hprefix tailTrace_2053824
  have hstable : (prefixWord ++ tailWord_2053824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053824).length < 2 ^ (prefixWord ++ tailWord_2053824).sum := by decide
  have hdescent : baseEnd_2053824 < baseStart_2053824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053831 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2053831 : Nat := 118140960795 + 2053831 * 2 ^ 59
def prefixEnd_2053831 : Nat := 4983230072969 + 3 ^ 40 * 2053831 * 2
def baseEnd_2053831 : Nat := 1054602486104459110467109

theorem tailTrace_2053831 : CollatzResearch.WordTrace tailWord_2053831 prefixEnd_2053831 1054602486104459110467109 := by
  unfold tailWord_2053831
  simp only [CollatzResearch.WordTrace]
  refine ⟨74909370622328528253969347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49939580414885685502646231 74909370622328528253969347)
  ·
    refine ⟨112364055933492792380954021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74909370622328528253969347 112364055933492792380954021)
    ·
      refine ⟨21068260487529898571428879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112364055933492792380954021 21068260487529898571428879)
      ·
        refine ⟨31602390731294847857143319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21068260487529898571428879 31602390731294847857143319)
        ·
          refine ⟨47403586096942271785714979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31602390731294847857143319 47403586096942271785714979)
          ·
            refine ⟨71105379145413407678572469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47403586096942271785714979 71105379145413407678572469)
            ·
              refine ⟨6666129294882506969866169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71105379145413407678572469 6666129294882506969866169)
              ·
                refine ⟨4999596971161880227399627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6666129294882506969866169 4999596971161880227399627)
                ·
                  refine ⟨7499395456742820341099441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999596971161880227399627 7499395456742820341099441)
                  ·
                    refine ⟨5624546592557115255824581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7499395456742820341099441 5624546592557115255824581)
                    ·
                      refine ⟨1054602486104459110467109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5624546592557115255824581 1054602486104459110467109)
                      ·
                        rfl

theorem cell23_2053831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2053831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053831 prefixEnd_2053831 := by exact prefixLift 2053831
  have htrace : WordTrace (prefixWord ++ tailWord_2053831) baseStart_2053831 baseEnd_2053831 := by
    simpa [prefixWord, tailWord_2053831, baseEnd_2053831] using wordTrace_append hprefix tailTrace_2053831
  have hstable : (prefixWord ++ tailWord_2053831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053831).length < 2 ^ (prefixWord ++ tailWord_2053831).sum := by decide
  have hdescent : baseEnd_2053831 < baseStart_2053831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053846 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2053846 : Nat := 118140960795 + 2053846 * 2 ^ 59
def prefixEnd_2053846 : Nat := 4983230072969 + 3 ^ 40 * 2053846 * 2
def baseEnd_2053846 : Nat := 1054610188314276551779541

theorem tailTrace_2053846 : CollatzResearch.WordTrace tailWord_2053846 prefixEnd_2053846 1054610188314276551779541 := by
  unfold tailWord_2053846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4681869857329636613485337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49939945144849457210510261 4681869857329636613485337)
  ·
    refine ⟨3511402392997227460114003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4681869857329636613485337 3511402392997227460114003)
    ·
      refine ⟨5267103589495841190171005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511402392997227460114003 5267103589495841190171005)
      ·
        refine ⟨1975163846060940446314127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5267103589495841190171005 1975163846060940446314127)
        ·
          refine ⟨2962745769091410669471191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975163846060940446314127 2962745769091410669471191)
          ·
            refine ⟨4444118653637116004206787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962745769091410669471191 4444118653637116004206787)
            ·
              refine ⟨6666177980455674006310181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444118653637116004206787 6666177980455674006310181)
              ·
                refine ⟨1249908371335438876183159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6666177980455674006310181 1249908371335438876183159)
                ·
                  refine ⟨1874862557003158314274739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249908371335438876183159 1874862557003158314274739)
                  ·
                    refine ⟨2812293835504737471412109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1874862557003158314274739 2812293835504737471412109)
                    ·
                      refine ⟨1054610188314276551779541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812293835504737471412109 1054610188314276551779541)
                      ·
                        rfl

theorem cell23_2053846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2053846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053846 prefixEnd_2053846 := by exact prefixLift 2053846
  have htrace : WordTrace (prefixWord ++ tailWord_2053846) baseStart_2053846 baseEnd_2053846 := by
    simpa [prefixWord, tailWord_2053846, baseEnd_2053846] using wordTrace_append hprefix tailTrace_2053846
  have hstable : (prefixWord ++ tailWord_2053846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053846).length < 2 ^ (prefixWord ++ tailWord_2053846).sum := by decide
  have hdescent : baseEnd_2053846 < baseStart_2053846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053886 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_2053886 : Nat := 118140960795 + 2053886 * 2 ^ 59
def prefixEnd_2053886 : Nat := 4983230072969 + 3 ^ 40 * 2053886 * 2
def baseEnd_2053886 : Nat := 1054630727540456395279357

theorem tailTrace_2053886 : CollatzResearch.WordTrace tailWord_2053886 prefixEnd_2053886 1054630727540456395279357 := by
  unfold tailWord_2053886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9363922079641159080902689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49940917758086181764814341 9363922079641159080902689)
  ·
    refine ⟨7022941559730869310677017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9363922079641159080902689 7022941559730869310677017)
    ·
      refine ⟨5267206169798151983007763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7022941559730869310677017 5267206169798151983007763)
      ·
        refine ⟨7900809254697227974511645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267206169798151983007763 7900809254697227974511645)
        ·
          refine ⟨2962803470511460490441867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7900809254697227974511645 2962803470511460490441867)
          ·
            refine ⟨4444205205767190735662801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962803470511460490441867 4444205205767190735662801)
            ·
              refine ⟨3333153904325393051747101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444205205767190735662801 3333153904325393051747101)
              ·
                refine ⟨1249932714122022394405163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333153904325393051747101 1249932714122022394405163)
                ·
                  refine ⟨1874899071183033591607745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249932714122022394405163 1874899071183033591607745)
                  ·
                    refine ⟨1406174303387275193705809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1874899071183033591607745 1406174303387275193705809)
                    ·
                      refine ⟨1054630727540456395279357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406174303387275193705809 1054630727540456395279357)
                      ·
                        rfl

theorem cell23_2053886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_2053886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053886 prefixEnd_2053886 := by exact prefixLift 2053886
  have htrace : WordTrace (prefixWord ++ tailWord_2053886) baseStart_2053886 baseEnd_2053886 := by
    simpa [prefixWord, tailWord_2053886, baseEnd_2053886] using wordTrace_append hprefix tailTrace_2053886
  have hstable : (prefixWord ++ tailWord_2053886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053886).length < 2 ^ (prefixWord ++ tailWord_2053886).sum := by decide
  have hdescent : baseEnd_2053886 < baseStart_2053886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053925 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_2053925 : Nat := 118140960795 + 2053925 * 2 ^ 59
def prefixEnd_2053925 : Nat := 4983230072969 + 3 ^ 40 * 2053925 * 2
def baseEnd_2053925 : Nat := 1054650753285981742691677

theorem tailTrace_2053925 : CollatzResearch.WordTrace tailWord_2053925 prefixEnd_2053925 1054650753285981742691677 := by
  unfold tailWord_2053925
  simp only [CollatzResearch.WordTrace]
  refine ⟨74912799083987982307891229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49941866055991988205260819 74912799083987982307891229)
  ·
    refine ⟨28092299656495493365459211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74912799083987982307891229 28092299656495493365459211)
    ·
      refine ⟨42138449484743240048188817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28092299656495493365459211 42138449484743240048188817)
      ·
        refine ⟨31603837113557430036141613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42138449484743240048188817 31603837113557430036141613)
        ·
          refine ⟨11851438917584036263553105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31603837113557430036141613 11851438917584036263553105)
          ·
            refine ⟨8888579188188027197664829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11851438917584036263553105 8888579188188027197664829)
            ·
              refine ⟨3333217195570510199124311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8888579188188027197664829 3333217195570510199124311)
              ·
                refine ⟨4999825793355765298686467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333217195570510199124311 4999825793355765298686467)
                ·
                  refine ⟨7499738690033647948029701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999825793355765298686467 7499738690033647948029701)
                  ·
                    refine ⟨1406201004381308990255569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499738690033647948029701 1406201004381308990255569)
                    ·
                      refine ⟨1054650753285981742691677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406201004381308990255569 1054650753285981742691677)
                      ·
                        rfl

theorem cell23_2053925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_2053925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053925 prefixEnd_2053925 := by exact prefixLift 2053925
  have htrace : WordTrace (prefixWord ++ tailWord_2053925) baseStart_2053925 baseEnd_2053925 := by
    simpa [prefixWord, tailWord_2053925, baseEnd_2053925] using wordTrace_append hprefix tailTrace_2053925
  have hstable : (prefixWord ++ tailWord_2053925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053925).length < 2 ^ (prefixWord ++ tailWord_2053925).sum := by decide
  have hdescent : baseEnd_2053925 < baseStart_2053925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053945 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2053945 : Nat := 118140960795 + 2053945 * 2 ^ 59
def prefixEnd_2053945 : Nat := 4983230072969 + 3 ^ 40 * 2053945 * 2
def baseEnd_2053945 : Nat := 1054661022899071664441585

theorem tailTrace_2053945 : CollatzResearch.WordTrace tailWord_2053945 prefixEnd_2053945 1054661022899071664441585 := by
  unfold tailWord_2053945
  simp only [CollatzResearch.WordTrace]
  refine ⟨74913528543915525723619289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49942352362610350482412859 74913528543915525723619289)
  ·
    refine ⟨56185146407936644292714467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74913528543915525723619289 56185146407936644292714467)
    ·
      refine ⟨84277719611904966439071701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56185146407936644292714467 84277719611904966439071701)
      ·
        refine ⟨1975259053404022650915743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84277719611904966439071701 1975259053404022650915743)
        ·
          refine ⟨2962888580106033976373615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975259053404022650915743 2962888580106033976373615)
          ·
            refine ⟨4444332870159050964560423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962888580106033976373615 4444332870159050964560423)
            ·
              refine ⟨6666499305238576446840635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444332870159050964560423 6666499305238576446840635)
              ·
                refine ⟨9999748957857864670260953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666499305238576446840635 9999748957857864670260953)
                ·
                  refine ⟨7499811718393398502695715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999748957857864670260953 7499811718393398502695715)
                  ·
                    refine ⟨11249717577590097754043573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499811718393398502695715 11249717577590097754043573)
                    ·
                      refine ⟨1054661022899071664441585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11249717577590097754043573 1054661022899071664441585)
                      ·
                        rfl

theorem cell23_2053945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2053945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053945 prefixEnd_2053945 := by exact prefixLift 2053945
  have htrace : WordTrace (prefixWord ++ tailWord_2053945) baseStart_2053945 baseEnd_2053945 := by
    simpa [prefixWord, tailWord_2053945, baseEnd_2053945] using wordTrace_append hprefix tailTrace_2053945
  have hstable : (prefixWord ++ tailWord_2053945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053945).length < 2 ^ (prefixWord ++ tailWord_2053945).sum := by decide
  have hdescent : baseEnd_2053945 < baseStart_2053945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053965 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2053965 : Nat := 118140960795 + 2053965 * 2 ^ 59
def prefixEnd_2053965 : Nat := 4983230072969 + 3 ^ 40 * 2053965 * 2
def baseEnd_2053965 : Nat := 117185699168017954021277

theorem tailTrace_2053965 : CollatzResearch.WordTrace tailWord_2053965 prefixEnd_2053965 117185699168017954021277 := by
  unfold tailWord_2053965
  simp only [CollatzResearch.WordTrace]
  refine ⟨74914258003843069139347349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49942838669228712759564899 74914258003843069139347349)
  ·
    refine ⟨3511605843930143865906907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74914258003843069139347349 3511605843930143865906907)
    ·
      refine ⟨5267408765895215798860361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511605843930143865906907 5267408765895215798860361)
      ·
        refine ⟨3950556574421411849145271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267408765895215798860361 3950556574421411849145271)
        ·
          refine ⟨5925834861632117773717907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950556574421411849145271 5925834861632117773717907)
          ·
            refine ⟨8888752292448176660576861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925834861632117773717907 8888752292448176660576861)
            ·
              refine ⟨3333282109668066247716323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8888752292448176660576861 3333282109668066247716323)
              ·
                refine ⟨4999923164502099371574485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333282109668066247716323 4999923164502099371574485)
                ·
                  refine ⟨117185699168017954021277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4999923164502099371574485 117185699168017954021277)
                  ·
                    rfl

theorem cell23_2053965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2053965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053965 prefixEnd_2053965 := by exact prefixLift 2053965
  have htrace : WordTrace (prefixWord ++ tailWord_2053965) baseStart_2053965 baseEnd_2053965 := by
    simpa [prefixWord, tailWord_2053965, baseEnd_2053965] using wordTrace_append hprefix tailTrace_2053965
  have hstable : (prefixWord ++ tailWord_2053965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053965).length < 2 ^ (prefixWord ++ tailWord_2053965).sum := by decide
  have hdescent : baseEnd_2053965 < baseStart_2053965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053968 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2]
def baseStart_2053968 : Nat := 118140960795 + 2053968 * 2 ^ 59
def prefixEnd_2053968 : Nat := 4983230072969 + 3 ^ 40 * 2053968 * 2
def baseEnd_2053968 : Nat := 1054672832954125074453979

theorem tailTrace_2053968 : CollatzResearch.WordTrace tailWord_2053968 prefixEnd_2053968 1054672832954125074453979 := by
  unfold tailWord_2053968
  simp only [CollatzResearch.WordTrace]
  refine ⟨37457183711416100325853279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49942911615221467101137705 37457183711416100325853279)
  ·
    refine ⟨56185775567124150488779919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37457183711416100325853279 56185775567124150488779919)
    ·
      refine ⟨84278663350686225733169879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56185775567124150488779919 84278663350686225733169879)
      ·
        refine ⟨126417995026029338599754819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84278663350686225733169879 126417995026029338599754819)
        ·
          refine ⟨189626992539044007899632229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126417995026029338599754819 189626992539044007899632229)
          ·
            refine ⟨35555061101070751481181043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189626992539044007899632229 35555061101070751481181043)
            ·
              refine ⟨53332591651606127221771565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35555061101070751481181043 53332591651606127221771565)
              ·
                refine ⟨19999721869352297708164337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53332591651606127221771565 19999721869352297708164337)
                ·
                  refine ⟨14999791402014223281123253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19999721869352297708164337 14999791402014223281123253)
                  ·
                    refine ⟨1406230443938833432605305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14999791402014223281123253 1406230443938833432605305)
                    ·
                      refine ⟨1054672832954125074453979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406230443938833432605305 1054672832954125074453979)
                      ·
                        rfl

theorem cell23_2053968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2].length) (baseStart_2053968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2053968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2053968 prefixEnd_2053968 := by exact prefixLift 2053968
  have htrace : WordTrace (prefixWord ++ tailWord_2053968) baseStart_2053968 baseEnd_2053968 := by
    simpa [prefixWord, tailWord_2053968, baseEnd_2053968] using wordTrace_append hprefix tailTrace_2053968
  have hstable : (prefixWord ++ tailWord_2053968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053968).length < 2 ^ (prefixWord ++ tailWord_2053968).sum := by decide
  have hdescent : baseEnd_2053968 < baseStart_2053968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054011 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_2054011 : Nat := 118140960795 + 2054011 * 2 ^ 59
def prefixEnd_2054011 : Nat := 4983230072969 + 3 ^ 40 * 2054011 * 2
def baseEnd_2054011 : Nat := 1054694912622268406216281

theorem tailTrace_2054011 : CollatzResearch.WordTrace tailWord_2054011 prefixEnd_2054011 1054694912622268406216281 := by
  unfold tailWord_2054011
  simp only [CollatzResearch.WordTrace]
  refine ⟨74915935761676418995521887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49943957174450945997014591 74915935761676418995521887)
  ·
    refine ⟨112373903642514628493282831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74915935761676418995521887 112373903642514628493282831)
    ·
      refine ⟨168560855463771942739924247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112373903642514628493282831 168560855463771942739924247)
      ·
        refine ⟨252841283195657914109886371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168560855463771942739924247 252841283195657914109886371)
        ·
          refine ⟨379261924793486871164829557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252841283195657914109886371 379261924793486871164829557)
          ·
            refine ⟨35555805449389394171702771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379261924793486871164829557 35555805449389394171702771)
            ·
              refine ⟨53333708174084091257554157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35555805449389394171702771 53333708174084091257554157)
              ·
                refine ⟨20000140565281534221582809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53333708174084091257554157 20000140565281534221582809)
                ·
                  refine ⟨15000105423961150666187107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20000140565281534221582809 15000105423961150666187107)
                  ·
                    refine ⟨22500158135941725999280661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15000105423961150666187107 22500158135941725999280661)
                    ·
                      refine ⟨1054694912622268406216281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22500158135941725999280661 1054694912622268406216281)
                      ·
                        rfl

theorem cell23_2054011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_2054011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054011 prefixEnd_2054011 := by exact prefixLift 2054011
  have htrace : WordTrace (prefixWord ++ tailWord_2054011) baseStart_2054011 baseEnd_2054011 := by
    simpa [prefixWord, tailWord_2054011, baseEnd_2054011] using wordTrace_append hprefix tailTrace_2054011
  have hstable : (prefixWord ++ tailWord_2054011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054011).length < 2 ^ (prefixWord ++ tailWord_2054011).sum := by decide
  have hdescent : baseEnd_2054011 < baseStart_2054011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054046 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2054046 : Nat := 118140960795 + 2054046 * 2 ^ 59
def prefixEnd_2054046 : Nat := 4983230072969 + 3 ^ 40 * 2054046 * 2
def baseEnd_2054046 : Nat := 351570961481725256426207

theorem tailTrace_2054046 : CollatzResearch.WordTrace tailWord_2054046 prefixEnd_2054046 351570961481725256426207 := by
  unfold tailWord_2054046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9364651539568702496630749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49944808211033079982030661 9364651539568702496630749)
  ·
    refine ⟨3511744327338263436236531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9364651539568702496630749 3511744327338263436236531)
    ·
      refine ⟨5267616491007395154354797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511744327338263436236531 5267616491007395154354797)
      ·
        refine ⟨1975356184127773182883049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5267616491007395154354797 1975356184127773182883049)
        ·
          refine ⟨1481517138095829887162287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975356184127773182883049 1481517138095829887162287)
          ·
            refine ⟨2222275707143744830743431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481517138095829887162287 2222275707143744830743431)
            ·
              refine ⟨3333413560715617246115147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222275707143744830743431 3333413560715617246115147)
              ·
                refine ⟨5000120341073425869172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333413560715617246115147 5000120341073425869172721)
                ·
                  refine ⟨3750090255805069401879541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000120341073425869172721 3750090255805069401879541)
                  ·
                    refine ⟨351570961481725256426207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3750090255805069401879541 351570961481725256426207)
                    ·
                      rfl

theorem cell23_2054046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2054046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054046 prefixEnd_2054046 := by exact prefixLift 2054046
  have htrace : WordTrace (prefixWord ++ tailWord_2054046) baseStart_2054046 baseEnd_2054046 := by
    simpa [prefixWord, tailWord_2054046, baseEnd_2054046] using wordTrace_append hprefix tailTrace_2054046
  have hstable : (prefixWord ++ tailWord_2054046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054046).length < 2 ^ (prefixWord ++ tailWord_2054046).sum := by decide
  have hdescent : baseEnd_2054046 < baseStart_2054046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054049 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2054049 : Nat := 118140960795 + 2054049 * 2 ^ 59
def prefixEnd_2054049 : Nat := 4983230072969 + 3 ^ 40 * 2054049 * 2
def baseEnd_2054049 : Nat := 1054714424887139257541107

theorem tailTrace_2054049 : CollatzResearch.WordTrace tailWord_2054049 prefixEnd_2054049 1054714424887139257541107 := by
  unfold tailWord_2054049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74917321735538751485405201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49944881157025834323603467 74917321735538751485405201)
  ·
    refine ⟨56187991301654063614053901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74917321735538751485405201 56187991301654063614053901)
    ·
      refine ⟨21070496738120273855270213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56187991301654063614053901 21070496738120273855270213)
      ·
        refine ⟨3950718138397551347863165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21070496738120273855270213 3950718138397551347863165)
        ·
          refine ⟨1481519301899081755448687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3950718138397551347863165 1481519301899081755448687)
          ·
            refine ⟨2222278952848622633173031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481519301899081755448687 2222278952848622633173031)
            ·
              refine ⟨3333418429272933949759547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222278952848622633173031 3333418429272933949759547)
              ·
                refine ⟨5000127643909400924639321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333418429272933949759547 5000127643909400924639321)
                ·
                  refine ⟨3750095732932050693479491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000127643909400924639321 3750095732932050693479491)
                  ·
                    refine ⟨5625143599398076040219237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750095732932050693479491 5625143599398076040219237)
                    ·
                      refine ⟨1054714424887139257541107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5625143599398076040219237 1054714424887139257541107)
                      ·
                        rfl

theorem cell23_2054049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2054049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054049 prefixEnd_2054049 := by exact prefixLift 2054049
  have htrace : WordTrace (prefixWord ++ tailWord_2054049) baseStart_2054049 baseEnd_2054049 := by
    simpa [prefixWord, tailWord_2054049, baseEnd_2054049] using wordTrace_append hprefix tailTrace_2054049
  have hstable : (prefixWord ++ tailWord_2054049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054049).length < 2 ^ (prefixWord ++ tailWord_2054049).sum := by decide
  have hdescent : baseEnd_2054049 < baseStart_2054049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054052 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_2054052 : Nat := 118140960795 + 2054052 * 2 ^ 59
def prefixEnd_2054052 : Nat := 4983230072969 + 3 ^ 40 * 2054052 * 2
def baseEnd_2054052 : Nat := 1054715965329102745803593

theorem tailTrace_2054052 : CollatzResearch.WordTrace tailWord_2054052 prefixEnd_2054052 1054715965329102745803593 := by
  unfold tailWord_2054052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37458715577263941498882205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49944954103018588665176273 37458715577263941498882205)
  ·
    refine ⟨14047018341473978062080827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37458715577263941498882205 14047018341473978062080827)
    ·
      refine ⟨21070527512210967093121241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14047018341473978062080827 21070527512210967093121241)
      ·
        refine ⟨15802895634158225319840931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21070527512210967093121241 15802895634158225319840931)
        ·
          refine ⟨23704343451237337979761397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15802895634158225319840931 23704343451237337979761397)
          ·
            refine ⟨2222282198553500435602631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23704343451237337979761397 2222282198553500435602631)
            ·
              refine ⟨3333423297830250653403947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222282198553500435602631 3333423297830250653403947)
              ·
                refine ⟨5000134946745375980105921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333423297830250653403947 5000134946745375980105921)
                ·
                  refine ⟨3750101210059031985079441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000134946745375980105921 3750101210059031985079441)
                  ·
                    refine ⟨2812575907544273988809581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750101210059031985079441 2812575907544273988809581)
                    ·
                      refine ⟨1054715965329102745803593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812575907544273988809581 1054715965329102745803593)
                      ·
                        rfl

theorem cell23_2054052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_2054052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054052 prefixEnd_2054052 := by exact prefixLift 2054052
  have htrace : WordTrace (prefixWord ++ tailWord_2054052) baseStart_2054052 baseEnd_2054052 := by
    simpa [prefixWord, tailWord_2054052, baseEnd_2054052] using wordTrace_append hprefix tailTrace_2054052
  have hstable : (prefixWord ++ tailWord_2054052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054052).length < 2 ^ (prefixWord ++ tailWord_2054052).sum := by decide
  have hdescent : baseEnd_2054052 < baseStart_2054052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054115 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 4, 4]
def baseStart_2054115 : Nat := 118140960795 + 2054115 * 2 ^ 59
def prefixEnd_2054115 : Nat := 4983230072969 + 3 ^ 40 * 2054115 * 2
def baseEnd_2054115 : Nat := 351582771536778666438601

theorem tailTrace_2054115 : CollatzResearch.WordTrace tailWord_2054115 prefixEnd_2054115 351582771536778666438601 := by
  unfold tailWord_2054115
  simp only [CollatzResearch.WordTrace]
  refine ⟨74919728953299644757307799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49946485968866429838205199 74919728953299644757307799)
  ·
    refine ⟨112379593429949467135961699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74919728953299644757307799 112379593429949467135961699)
    ·
      refine ⟨168569390144924200703942549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112379593429949467135961699 168569390144924200703942549)
      ·
        refine ⟨7901690163043321907997307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168569390144924200703942549 7901690163043321907997307)
        ·
          refine ⟨11852535244564982861995961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901690163043321907997307 11852535244564982861995961)
          ·
            refine ⟨8889401433423737146496971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11852535244564982861995961 8889401433423737146496971)
            ·
              refine ⟨13334102150135605719745457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889401433423737146496971 13334102150135605719745457)
              ·
                refine ⟨10000576612601704289809093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13334102150135605719745457 10000576612601704289809093)
                ·
                  refine ⟨1875108114862819554339205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10000576612601704289809093 1875108114862819554339205)
                  ·
                    refine ⟨351582771536778666438601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875108114862819554339205 351582771536778666438601)
                    ·
                      rfl

theorem cell23_2054115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 4].length) (baseStart_2054115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054115 prefixEnd_2054115 := by exact prefixLift 2054115
  have htrace : WordTrace (prefixWord ++ tailWord_2054115) baseStart_2054115 baseEnd_2054115 := by
    simpa [prefixWord, tailWord_2054115, baseEnd_2054115] using wordTrace_append hprefix tailTrace_2054115
  have hstable : (prefixWord ++ tailWord_2054115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054115).length < 2 ^ (prefixWord ++ tailWord_2054115).sum := by decide
  have hdescent : baseEnd_2054115 < baseStart_2054115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054139 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 1, 2, 2]
def baseStart_2054139 : Nat := 118140960795 + 2054139 * 2 ^ 59
def prefixEnd_2054139 : Nat := 4983230072969 + 3 ^ 40 * 2054139 * 2
def baseEnd_2054139 : Nat := 1054760638146043905415693

theorem tailTrace_2054139 : CollatzResearch.WordTrace tailWord_2054139 prefixEnd_2054139 1054760638146043905415693 := by
  unfold tailWord_2054139
  simp only [CollatzResearch.WordTrace]
  refine ⟨74920604305212696856181471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49947069536808464570787647 74920604305212696856181471)
  ·
    refine ⟨112380906457819045284272207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74920604305212696856181471 112380906457819045284272207)
    ·
      refine ⟨168571359686728567926408311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112380906457819045284272207 168571359686728567926408311)
      ·
        refine ⟨252857039530092851889612467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168571359686728567926408311 252857039530092851889612467)
        ·
          refine ⟨379285559295139277834418701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252857039530092851889612467 379285559295139277834418701)
          ·
            refine ⟨142232084735677229187907013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379285559295139277834418701 142232084735677229187907013)
            ·
              refine ⟨26668515887939480472732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142232084735677229187907013 26668515887939480472732565)
              ·
                refine ⟨1250086682247163147159339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26668515887939480472732565 1250086682247163147159339)
                ·
                  refine ⟨1875130023370744720739009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250086682247163147159339 1875130023370744720739009)
                  ·
                    refine ⟨1406347517528058540554257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875130023370744720739009 1406347517528058540554257)
                    ·
                      refine ⟨1054760638146043905415693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406347517528058540554257 1054760638146043905415693)
                      ·
                        rfl

theorem cell23_2054139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 2, 2].length) (baseStart_2054139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054139 prefixEnd_2054139 := by exact prefixLift 2054139
  have htrace : WordTrace (prefixWord ++ tailWord_2054139) baseStart_2054139 baseEnd_2054139 := by
    simpa [prefixWord, tailWord_2054139, baseEnd_2054139] using wordTrace_append hprefix tailTrace_2054139
  have hstable : (prefixWord ++ tailWord_2054139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054139).length < 2 ^ (prefixWord ++ tailWord_2054139).sum := by decide
  have hdescent : baseEnd_2054139 < baseStart_2054139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054142 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2054142 : Nat := 118140960795 + 2054142 * 2 ^ 59
def prefixEnd_2054142 : Nat := 4983230072969 + 3 ^ 40 * 2054142 * 2
def baseEnd_2054142 : Nat := 1054762178588007393678179

theorem tailTrace_2054142 : CollatzResearch.WordTrace tailWord_2054142 prefixEnd_2054142 1054762178588007393678179 := by
  unfold tailWord_2054142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365089215525228546067585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49947142482801218912360453 9365089215525228546067585)
  ·
    refine ⟨7023816911643921409550689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9365089215525228546067585 7023816911643921409550689)
    ·
      refine ⟨5267862683732941057163017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7023816911643921409550689 5267862683732941057163017)
      ·
        refine ⟨3950897012799705792872263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267862683732941057163017 3950897012799705792872263)
        ·
          refine ⟨5926345519199558689308395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950897012799705792872263 5926345519199558689308395)
          ·
            refine ⟨8889518278799338033962593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926345519199558689308395 8889518278799338033962593)
            ·
              refine ⟨6667138709099503525471945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889518278799338033962593 6667138709099503525471945)
              ·
                refine ⟨5000354031824627644103959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667138709099503525471945 5000354031824627644103959)
                ·
                  refine ⟨7500531047736941466155939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000354031824627644103959 7500531047736941466155939)
                  ·
                    refine ⟨11250796571605412199233909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7500531047736941466155939 11250796571605412199233909)
                    ·
                      refine ⟨1054762178588007393678179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11250796571605412199233909 1054762178588007393678179)
                      ·
                        rfl

theorem cell23_2054142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2054142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054142 prefixEnd_2054142 := by exact prefixLift 2054142
  have htrace : WordTrace (prefixWord ++ tailWord_2054142) baseStart_2054142 baseEnd_2054142 := by
    simpa [prefixWord, tailWord_2054142, baseEnd_2054142] using wordTrace_append hprefix tailTrace_2054142
  have hstable : (prefixWord ++ tailWord_2054142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054142).length < 2 ^ (prefixWord ++ tailWord_2054142).sum := by decide
  have hdescent : baseEnd_2054142 < baseStart_2054142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054149 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_2054149 : Nat := 118140960795 + 2054149 * 2 ^ 59
def prefixEnd_2054149 : Nat := 4983230072969 + 3 ^ 40 * 2054149 * 2
def baseEnd_2054149 : Nat := 351588590984196288763549

theorem tailTrace_2054149 : CollatzResearch.WordTrace tailWord_2054149 prefixEnd_2054149 351588590984196288763549 := by
  unfold tailWord_2054149
  simp only [CollatzResearch.WordTrace]
  refine ⟨74920969035176468564045501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49947312690117645709363667 74920969035176468564045501)
  ·
    refine ⟨28095363388191175711517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74920969035176468564045501 28095363388191175711517063)
    ·
      refine ⟨42143045082286763567275595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28095363388191175711517063 42143045082286763567275595)
      ·
        refine ⟨63214567623430145350913393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42143045082286763567275595 63214567623430145350913393)
        ·
          refine ⟨47410925717572609013185045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63214567623430145350913393 47410925717572609013185045)
          ·
            refine ⟨2222387143011216047493049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47410925717572609013185045 2222387143011216047493049)
            ·
              refine ⟨1666790357258412035619787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222387143011216047493049 1666790357258412035619787)
              ·
                refine ⟨2500185535887618053429681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666790357258412035619787 2500185535887618053429681)
                ·
                  refine ⟨1875139151915713540072261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500185535887618053429681 1875139151915713540072261)
                  ·
                    refine ⟨351588590984196288763549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875139151915713540072261 351588590984196288763549)
                    ·
                      rfl

theorem cell23_2054149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_2054149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054149 prefixEnd_2054149 := by exact prefixLift 2054149
  have htrace : WordTrace (prefixWord ++ tailWord_2054149) baseStart_2054149 baseEnd_2054149 := by
    simpa [prefixWord, tailWord_2054149, baseEnd_2054149] using wordTrace_append hprefix tailTrace_2054149
  have hstable : (prefixWord ++ tailWord_2054149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054149).length < 2 ^ (prefixWord ++ tailWord_2054149).sum := by decide
  have hdescent : baseEnd_2054149 < baseStart_2054149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054155 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3]
def baseStart_2054155 : Nat := 118140960795 + 2054155 * 2 ^ 59
def prefixEnd_2054155 : Nat := 4983230072969 + 3 ^ 40 * 2054155 * 2
def baseEnd_2054155 : Nat := 1054768853836515842815619

theorem tailTrace_2054155 : CollatzResearch.WordTrace tailWord_2054155 prefixEnd_2054155 1054768853836515842815619 := by
  unfold tailWord_2054155
  simp only [CollatzResearch.WordTrace]
  refine ⟨74921187873154731588763919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49947458582103154392509279 74921187873154731588763919)
  ·
    refine ⟨112381781809732097383145879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74921187873154731588763919 112381781809732097383145879)
    ·
      refine ⟨168572672714598146074718819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112381781809732097383145879 168572672714598146074718819)
      ·
        refine ⟨252859009071897219112078229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168572672714598146074718819 252859009071897219112078229)
        ·
          refine ⟨11852766050245182145878667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252859009071897219112078229 11852766050245182145878667)
          ·
            refine ⟨17779149075367773218818001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11852766050245182145878667 17779149075367773218818001)
            ·
              refine ⟨13334361806525829914113501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17779149075367773218818001 13334361806525829914113501)
              ·
                refine ⟨5000385677447186217792563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13334361806525829914113501 5000385677447186217792563)
                ·
                  refine ⟨7500578516170779326688845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000385677447186217792563 7500578516170779326688845)
                  ·
                    refine ⟨2812716943564042247508317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7500578516170779326688845 2812716943564042247508317)
                    ·
                      refine ⟨1054768853836515842815619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812716943564042247508317 1054768853836515842815619)
                      ·
                        rfl

theorem cell23_2054155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].length) (baseStart_2054155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054155 prefixEnd_2054155 := by exact prefixLift 2054155
  have htrace : WordTrace (prefixWord ++ tailWord_2054155) baseStart_2054155 baseEnd_2054155 := by
    simpa [prefixWord, tailWord_2054155, baseEnd_2054155] using wordTrace_append hprefix tailTrace_2054155
  have hstable : (prefixWord ++ tailWord_2054155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054155).length < 2 ^ (prefixWord ++ tailWord_2054155).sum := by decide
  have hdescent : baseEnd_2054155 < baseStart_2054155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054172 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2054172 : Nat := 118140960795 + 2054172 * 2 ^ 59
def prefixEnd_2054172 : Nat := 4983230072969 + 3 ^ 40 * 2054172 * 2
def baseEnd_2054172 : Nat := 1054777583007642276303041

theorem tailTrace_2054172 : CollatzResearch.WordTrace tailWord_2054172 prefixEnd_2054172 1054777583007642276303041 := by
  unfold tailWord_2054172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37460903957046571746066385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49947871942728762328088513 37460903957046571746066385)
  ·
    refine ⟨28095677967784928809549789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37460903957046571746066385 28095677967784928809549789)
    ·
      refine ⟨10535879237919348303581171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28095677967784928809549789 10535879237919348303581171)
      ·
        refine ⟨15803818856879022455371757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535879237919348303581171 15803818856879022455371757)
        ·
          refine ⟨5926432071329633420764409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15803818856879022455371757 5926432071329633420764409)
          ·
            refine ⟨4444824053497225065573307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5926432071329633420764409 4444824053497225065573307)
            ·
              refine ⟨6667236080245837598359961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4444824053497225065573307 6667236080245837598359961)
              ·
                refine ⟨5000427060184378198769971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667236080245837598359961 5000427060184378198769971)
                ·
                  refine ⟨7500640590276567298154957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5000427060184378198769971 7500640590276567298154957)
                  ·
                    refine ⟨2812740221353712736808109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7500640590276567298154957 2812740221353712736808109)
                    ·
                      refine ⟨1054777583007642276303041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812740221353712736808109 1054777583007642276303041)
                      ·
                        rfl

theorem cell23_2054172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2054172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054172 prefixEnd_2054172 := by exact prefixLift 2054172
  have htrace : WordTrace (prefixWord ++ tailWord_2054172) baseStart_2054172 baseEnd_2054172 := by
    simpa [prefixWord, tailWord_2054172, baseEnd_2054172] using wordTrace_append hprefix tailTrace_2054172
  have hstable : (prefixWord ++ tailWord_2054172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054172).length < 2 ^ (prefixWord ++ tailWord_2054172).sum := by decide
  have hdescent : baseEnd_2054172 < baseStart_2054172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054190 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2054190 : Nat := 118140960795 + 2054190 * 2 ^ 59
def prefixEnd_2054190 : Nat := 4983230072969 + 3 ^ 40 * 2054190 * 2
def baseEnd_2054190 : Nat := 1054786825659423205877959

theorem tailTrace_2054190 : CollatzResearch.WordTrace tailWord_2054190 prefixEnd_2054190 1054786825659423205877959 := by
  unfold tailWord_2054190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365308053503491570786003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49948309618685288377525349 9365308053503491570786003)
  ·
    refine ⟨14047962080255237356179005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9365308053503491570786003 14047962080255237356179005)
    ·
      refine ⟨5267985780095714008567127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14047962080255237356179005 5267985780095714008567127)
      ·
        refine ⟨7901978670143571012850691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5267985780095714008567127 7901978670143571012850691)
        ·
          refine ⟨11852968005215356519276037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7901978670143571012850691 11852968005215356519276037)
          ·
            refine ⟨2222431500977879347364257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11852968005215356519276037 2222431500977879347364257)
            ·
              refine ⟨1666823625733409510523193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222431500977879347364257 1666823625733409510523193)
              ·
                refine ⟨1250117719300057132892395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666823625733409510523193 1250117719300057132892395)
                ·
                  refine ⟨1875176578950085699338593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250117719300057132892395 1875176578950085699338593)
                  ·
                    refine ⟨1406382434212564274503945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875176578950085699338593 1406382434212564274503945)
                    ·
                      refine ⟨1054786825659423205877959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406382434212564274503945 1054786825659423205877959)
                      ·
                        rfl

theorem cell23_2054190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2054190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054190 prefixEnd_2054190 := by exact prefixLift 2054190
  have htrace : WordTrace (prefixWord ++ tailWord_2054190) baseStart_2054190 baseEnd_2054190 := by
    simpa [prefixWord, tailWord_2054190, baseEnd_2054190] using wordTrace_append hprefix tailTrace_2054190
  have hstable : (prefixWord ++ tailWord_2054190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054190).length < 2 ^ (prefixWord ++ tailWord_2054190).sum := by decide
  have hdescent : baseEnd_2054190 < baseStart_2054190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054205 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2054205 : Nat := 118140960795 + 2054205 * 2 ^ 59
def prefixEnd_2054205 : Nat := 4983230072969 + 3 ^ 40 * 2054205 * 2
def baseEnd_2054205 : Nat := 351598175956413549063463

theorem tailTrace_2054205 : CollatzResearch.WordTrace tailWord_2054205 prefixEnd_2054205 351598175956413549063463 := by
  unfold tailWord_2054205
  simp only [CollatzResearch.WordTrace]
  refine ⟨74923011522973590128084069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49948674348649060085389379 74923011522973590128084069)
  ·
    refine ⟨14048064660557548149015763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74923011522973590128084069 14048064660557548149015763)
    ·
      refine ⟨21072096990836322223523645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14048064660557548149015763 21072096990836322223523645)
      ·
        refine ⟨7902036371563620833821367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21072096990836322223523645 7902036371563620833821367)
        ·
          refine ⟨11853054557345431250732051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902036371563620833821367 11853054557345431250732051)
          ·
            refine ⟨17779581836018146876098077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853054557345431250732051 17779581836018146876098077)
            ·
              refine ⟨6667343188506805078536779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17779581836018146876098077 6667343188506805078536779)
              ·
                refine ⟨10001014782760207617805169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667343188506805078536779 10001014782760207617805169)
                ·
                  refine ⟨7500761087070155713353877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001014782760207617805169 7500761087070155713353877)
                  ·
                    refine ⟨351598175956413549063463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7500761087070155713353877 351598175956413549063463)
                    ·
                      rfl

theorem cell23_2054205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2054205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054205 prefixEnd_2054205 := by exact prefixLift 2054205
  have htrace : WordTrace (prefixWord ++ tailWord_2054205) baseStart_2054205 baseEnd_2054205 := by
    simpa [prefixWord, tailWord_2054205, baseEnd_2054205] using wordTrace_append hprefix tailTrace_2054205
  have hstable : (prefixWord ++ tailWord_2054205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054205).length < 2 ^ (prefixWord ++ tailWord_2054205).sum := by decide
  have hdescent : baseEnd_2054205 < baseStart_2054205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054215 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_2054215 : Nat := 118140960795 + 2054215 * 2 ^ 59
def prefixEnd_2054215 : Nat := 4983230072969 + 3 ^ 40 * 2054215 * 2
def baseEnd_2054215 : Nat := 1054799662675785608065343

theorem tailTrace_2054215 : CollatzResearch.WordTrace tailWord_2054215 prefixEnd_2054215 1054799662675785608065343 := by
  unfold tailWord_2054215
  simp only [CollatzResearch.WordTrace]
  refine ⟨74923376252937361835948099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49948917501958241223965399 74923376252937361835948099)
  ·
    refine ⟨112385064379406042753922149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74923376252937361835948099 112385064379406042753922149)
    ·
      refine ⟨21072199571138633016360403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112385064379406042753922149 21072199571138633016360403)
      ·
        refine ⟨31608299356707949524540605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21072199571138633016360403 31608299356707949524540605)
        ·
          refine ⟨11853112258765481071702727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31608299356707949524540605 11853112258765481071702727)
          ·
            refine ⟨17779668388148221607554091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11853112258765481071702727 17779668388148221607554091)
            ·
              refine ⟨26669502582222332411331137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17779668388148221607554091 26669502582222332411331137)
              ·
                refine ⟨20002126936666749308498353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26669502582222332411331137 20002126936666749308498353)
                ·
                  refine ⟨15001595202500061981373765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20002126936666749308498353 15001595202500061981373765)
                  ·
                    refine ⟨2812799100468761621507581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15001595202500061981373765 2812799100468761621507581)
                    ·
                      refine ⟨1054799662675785608065343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812799100468761621507581 1054799662675785608065343)
                      ·
                        rfl

theorem cell23_2054215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_2054215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054215 prefixEnd_2054215 := by exact prefixLift 2054215
  have htrace : WordTrace (prefixWord ++ tailWord_2054215) baseStart_2054215 baseEnd_2054215 := by
    simpa [prefixWord, tailWord_2054215, baseEnd_2054215] using wordTrace_append hprefix tailTrace_2054215
  have hstable : (prefixWord ++ tailWord_2054215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054215).length < 2 ^ (prefixWord ++ tailWord_2054215).sum := by decide
  have hdescent : baseEnd_2054215 < baseStart_2054215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054252 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 5]
def baseStart_2054252 : Nat := 118140960795 + 2054252 * 2 ^ 59
def prefixEnd_2054252 : Nat := 4983230072969 + 3 ^ 40 * 2054252 * 2
def baseEnd_2054252 : Nat := 117202073495555773700297

theorem tailTrace_2054252 : CollatzResearch.WordTrace tailWord_2054252 prefixEnd_2054252 117202073495555773700297 := by
  unfold tailWord_2054252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37462362876901658577522505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49949817169202211436696673 37462362876901658577522505)
  ·
    refine ⟨28096772157676243933141879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37462362876901658577522505 28096772157676243933141879)
    ·
      refine ⟨42145158236514365899712819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096772157676243933141879 42145158236514365899712819)
      ·
        refine ⟨63217737354771548849569229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42145158236514365899712819 63217737354771548849569229)
        ·
          refine ⟨23706651508039330818588461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63217737354771548849569229 23706651508039330818588461)
          ·
            refine ⟨8889994315514749056970673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23706651508039330818588461 8889994315514749056970673)
            ·
              refine ⟨6667495736636061792728005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889994315514749056970673 6667495736636061792728005)
              ·
                refine ⟨1250155450619261586136501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6667495736636061792728005 1250155450619261586136501)
                ·
                  refine ⟨117202073495555773700297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250155450619261586136501 117202073495555773700297)
                  ·
                    rfl

theorem cell23_2054252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_2054252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054252 prefixEnd_2054252 := by exact prefixLift 2054252
  have htrace : WordTrace (prefixWord ++ tailWord_2054252) baseStart_2054252 baseEnd_2054252 := by
    simpa [prefixWord, tailWord_2054252, baseEnd_2054252] using wordTrace_append hprefix tailTrace_2054252
  have hstable : (prefixWord ++ tailWord_2054252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054252).length < 2 ^ (prefixWord ++ tailWord_2054252).sum := by decide
  have hdescent : baseEnd_2054252 < baseStart_2054252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054265 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_2054265 : Nat := 118140960795 + 2054265 * 2 ^ 59
def prefixEnd_2054265 : Nat := 4983230072969 + 3 ^ 40 * 2054265 * 2
def baseEnd_2054265 : Nat := 351608445569503470813371

theorem tailTrace_2054265 : CollatzResearch.WordTrace tailWord_2054265 prefixEnd_2054265 351608445569503470813371 := by
  unfold tailWord_2054265
  simp only [CollatzResearch.WordTrace]
  refine ⟨74925199902756220375268249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49950133268504146916845499 74925199902756220375268249)
  ·
    refine ⟨56193899927067165281451187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74925199902756220375268249 56193899927067165281451187)
    ·
      refine ⟨84290849890600747922176781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56193899927067165281451187 84290849890600747922176781)
      ·
        refine ⟨31609068708975280470816293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84290849890600747922176781 31609068708975280470816293)
        ·
          refine ⟨5926700382932865088278055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31609068708975280470816293 5926700382932865088278055)
          ·
            refine ⟨8890050574399297632417083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926700382932865088278055 8890050574399297632417083)
            ·
              refine ⟨13335075861598946448625625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8890050574399297632417083 13335075861598946448625625)
              ·
                refine ⟨10001306896199209836469219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13335075861598946448625625 10001306896199209836469219)
                ·
                  refine ⟨15001960344298814754703829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10001306896199209836469219 15001960344298814754703829)
                  ·
                    refine ⟨351608445569503470813371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15001960344298814754703829 351608445569503470813371)
                    ·
                      rfl

theorem cell23_2054265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_2054265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054265 prefixEnd_2054265 := by exact prefixLift 2054265
  have htrace : WordTrace (prefixWord ++ tailWord_2054265) baseStart_2054265 baseEnd_2054265 := by
    simpa [prefixWord, tailWord_2054265, baseEnd_2054265] using wordTrace_append hprefix tailTrace_2054265
  have hstable : (prefixWord ++ tailWord_2054265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054265).length < 2 ^ (prefixWord ++ tailWord_2054265).sum := by decide
  have hdescent : baseEnd_2054265 < baseStart_2054265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054286 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_2054286 : Nat := 118140960795 + 2054286 * 2 ^ 59
def prefixEnd_2054286 : Nat := 4983230072969 + 3 ^ 40 * 2054286 * 2
def baseEnd_2054286 : Nat := 117204013311361647808613

theorem tailTrace_2054286 : CollatzResearch.WordTrace tailWord_2054286 prefixEnd_2054286 117204013311361647808613 := by
  unfold tailWord_2054286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9365745729460017620222839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49950643890453427307855141 9365745729460017620222839)
  ·
    refine ⟨14048618594190026430334259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9365745729460017620222839 14048618594190026430334259)
    ·
      refine ⟨21072927891285039645501389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14048618594190026430334259 21072927891285039645501389)
      ·
        refine ⟨7902347959231889867063021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21072927891285039645501389 7902347959231889867063021)
        ·
          refine ⟨2963380484711958700148633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7902347959231889867063021 2963380484711958700148633)
          ·
            refine ⟨2222535363533969025111475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963380484711958700148633 2222535363533969025111475)
            ·
              refine ⟨3333803045300953537667213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222535363533969025111475 3333803045300953537667213)
              ·
                refine ⟨1250176141987857576625205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3333803045300953537667213 1250176141987857576625205)
                ·
                  refine ⟨117204013311361647808613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250176141987857576625205 117204013311361647808613)
                  ·
                    rfl

theorem cell23_2054286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_2054286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054286 prefixEnd_2054286 := by exact prefixLift 2054286
  have htrace : WordTrace (prefixWord ++ tailWord_2054286) baseStart_2054286 baseEnd_2054286 := by
    simpa [prefixWord, tailWord_2054286, baseEnd_2054286] using wordTrace_append hprefix tailTrace_2054286
  have hstable : (prefixWord ++ tailWord_2054286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054286).length < 2 ^ (prefixWord ++ tailWord_2054286).sum := by decide
  have hdescent : baseEnd_2054286 < baseStart_2054286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054322 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2054322 : Nat := 118140960795 + 2054322 * 2 ^ 59
def prefixEnd_2054322 : Nat := 4983230072969 + 3 ^ 40 * 2054322 * 2
def baseEnd_2054322 : Nat := 1054854605105816689427351

theorem tailTrace_2054322 : CollatzResearch.WordTrace tailWord_2054322 prefixEnd_2054322 1054854605105816689427351 := by
  unfold tailWord_2054322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18731819715887429777523305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49951519242366479406728813 18731819715887429777523305)
  ·
    refine ⟨14048864786915572333142479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18731819715887429777523305 14048864786915572333142479)
    ·
      refine ⟨21073297180373358499713719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14048864786915572333142479 21073297180373358499713719)
      ·
        refine ⟨31609945770560037749570579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21073297180373358499713719 31609945770560037749570579)
        ·
          refine ⟨47414918655840056624355869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31609945770560037749570579 47414918655840056624355869)
          ·
            refine ⟨17780594495940021234133451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47414918655840056624355869 17780594495940021234133451)
            ·
              refine ⟨26670891743910031851200177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17780594495940021234133451 26670891743910031851200177)
              ·
                refine ⟨20003168807932523888400133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26670891743910031851200177 20003168807932523888400133)
                ·
                  refine ⟨3750594151487348229075025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20003168807932523888400133 3750594151487348229075025)
                  ·
                    refine ⟨2812945613615511171806269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3750594151487348229075025 2812945613615511171806269)
                    ·
                      refine ⟨1054854605105816689427351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2812945613615511171806269 1054854605105816689427351)
                      ·
                        rfl

theorem cell23_2054322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2054322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054322 prefixEnd_2054322 := by exact prefixLift 2054322
  have htrace : WordTrace (prefixWord ++ tailWord_2054322) baseStart_2054322 baseEnd_2054322 := by
    simpa [prefixWord, tailWord_2054322, baseEnd_2054322] using wordTrace_append hprefix tailTrace_2054322
  have hstable : (prefixWord ++ tailWord_2054322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054322).length < 2 ^ (prefixWord ++ tailWord_2054322).sum := by decide
  have hdescent : baseEnd_2054322 < baseStart_2054322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 7, 5]
def baseStart_2054355 : Nat := 118140960795 + 2054355 * 2 ^ 59
def prefixEnd_2054355 : Nat := 4983230072969 + 3 ^ 40 * 2054355 * 2
def baseEnd_2054355 : Nat := 351623849989138353438233

theorem tailTrace_2054355 : CollatzResearch.WordTrace tailWord_2054355 prefixEnd_2054355 351623849989138353438233 := by
  unfold tailWord_2054355
  simp only [CollatzResearch.WordTrace]
  refine ⟨74928482472430165746044519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49952321648286777164029679 74928482472430165746044519)
  ·
    refine ⟨112392723708645248619066779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74928482472430165746044519 112392723708645248619066779)
    ·
      refine ⟨168589085562967872928600169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112392723708645248619066779 168589085562967872928600169)
      ·
        refine ⟨126441814172225904696450127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168589085562967872928600169 126441814172225904696450127)
        ·
          refine ⟨189662721258338857044675191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126441814172225904696450127 189662721258338857044675191)
          ·
            refine ⟨284494081887508285567012787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189662721258338857044675191 284494081887508285567012787)
            ·
              refine ⟨426741122831262428350519181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284494081887508285567012787 426741122831262428350519181)
              ·
                refine ⟨160027921061723410631444693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426741122831262428350519181 160027921061723410631444693)
                ·
                  refine ⟨3750654399884142436674485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160027921061723410631444693 3750654399884142436674485)
                  ·
                    refine ⟨351623849989138353438233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3750654399884142436674485 351623849989138353438233)
                    ·
                      rfl

theorem cell23_2054355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].length) (baseStart_2054355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054355 prefixEnd_2054355 := by exact prefixLift 2054355
  have htrace : WordTrace (prefixWord ++ tailWord_2054355) baseStart_2054355 baseEnd_2054355 := by
    simpa [prefixWord, tailWord_2054355, baseEnd_2054355] using wordTrace_append hprefix tailTrace_2054355
  have hstable : (prefixWord ++ tailWord_2054355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054355).length < 2 ^ (prefixWord ++ tailWord_2054355).sum := by decide
  have hdescent : baseEnd_2054355 < baseStart_2054355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054369 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_2054369 : Nat := 118140960795 + 2054369 * 2 ^ 59
def prefixEnd_2054369 : Nat := 4983230072969 + 3 ^ 40 * 2054369 * 2
def baseEnd_2054369 : Nat := 1054878738696578005539635

theorem tailTrace_2054369 : CollatzResearch.WordTrace tailWord_2054369 prefixEnd_2054369 1054878738696578005539635 := by
  unfold tailWord_2054369
  simp only [CollatzResearch.WordTrace]
  refine ⟨74928993094379446137054161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49952662062919630758036107 74928993094379446137054161)
  ·
    refine ⟨56196744820784584602790621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74928993094379446137054161 56196744820784584602790621)
    ·
      refine ⟨21073779307794219226046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56196744820784584602790621 21073779307794219226046483)
      ·
        refine ⟨31610668961691328839069725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21073779307794219226046483 31610668961691328839069725)
        ·
          refine ⟨11854000860634248314651147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31610668961691328839069725 11854000860634248314651147)
          ·
            refine ⟨17781001290951372471976721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854000860634248314651147 17781001290951372471976721)
            ·
              refine ⟨13335750968213529353982541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781001290951372471976721 13335750968213529353982541)
              ·
                refine ⟨5000906613080073507743453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13335750968213529353982541 5000906613080073507743453)
                ·
                  refine ⟨1875339979905027565403795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5000906613080073507743453 1875339979905027565403795)
                  ·
                    refine ⟨2813009969857541348105693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875339979905027565403795 2813009969857541348105693)
                    ·
                      refine ⟨1054878738696578005539635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813009969857541348105693 1054878738696578005539635)
                      ·
                        rfl

theorem cell23_2054369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_2054369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054369 prefixEnd_2054369 := by exact prefixLift 2054369
  have htrace : WordTrace (prefixWord ++ tailWord_2054369) baseStart_2054369 baseEnd_2054369 := by
    simpa [prefixWord, tailWord_2054369, baseEnd_2054369] using wordTrace_append hprefix tailTrace_2054369
  have hstable : (prefixWord ++ tailWord_2054369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054369).length < 2 ^ (prefixWord ++ tailWord_2054369).sum := by decide
  have hdescent : baseEnd_2054369 < baseStart_2054369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054370 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2054370 : Nat := 118140960795 + 2054370 * 2 ^ 59
def prefixEnd_2054370 : Nat := 4983230072969 + 3 ^ 40 * 2054370 * 2
def baseEnd_2054370 : Nat := 1054879252177232501627131

theorem tailTrace_2054370 : CollatzResearch.WordTrace tailWord_2054370 prefixEnd_2054370 1054879252177232501627131 := by
  unfold tailWord_2054370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732257391843955826960141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49952686378250548871893709 18732257391843955826960141)
  ·
    refine ⟨7024596521941483435110053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18732257391843955826960141 7024596521941483435110053)
    ·
      refine ⟨1317111847864028144083135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7024596521941483435110053 1317111847864028144083135)
      ·
        refine ⟨1975667771796042216124703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317111847864028144083135 1975667771796042216124703)
        ·
          refine ⟨2963501657694063324187055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975667771796042216124703 2963501657694063324187055)
          ·
            refine ⟨4445252486541094986280583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963501657694063324187055 4445252486541094986280583)
            ·
              refine ⟨6667878729811642479420875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445252486541094986280583 6667878729811642479420875)
              ·
                refine ⟨10001818094717463719131313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667878729811642479420875 10001818094717463719131313)
                ·
                  refine ⟨7501363571038097789348485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10001818094717463719131313 7501363571038097789348485)
                  ·
                    refine ⟨1406505669569643335502841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7501363571038097789348485 1406505669569643335502841)
                    ·
                      refine ⟨1054879252177232501627131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406505669569643335502841 1054879252177232501627131)
                      ·
                        rfl

theorem cell23_2054370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2054370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054370 prefixEnd_2054370 := by exact prefixLift 2054370
  have htrace : WordTrace (prefixWord ++ tailWord_2054370) baseStart_2054370 baseEnd_2054370 := by
    simpa [prefixWord, tailWord_2054370, baseEnd_2054370] using wordTrace_append hprefix tailTrace_2054370
  have hstable : (prefixWord ++ tailWord_2054370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054370).length < 2 ^ (prefixWord ++ tailWord_2054370).sum := by decide
  have hdescent : baseEnd_2054370 < baseStart_2054370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054386 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2054386 : Nat := 118140960795 + 2054386 * 2 ^ 59
def prefixEnd_2054386 : Nat := 4983230072969 + 3 ^ 40 * 2054386 * 2
def baseEnd_2054386 : Nat := 1054887467867704439027057

theorem tailTrace_2054386 : CollatzResearch.WordTrace tailWord_2054386 prefixEnd_2054386 1054887467867704439027057 := by
  unfold tailWord_2054386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18732403283829464510105753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49953075423545238693615341 18732403283829464510105753)
  ·
    refine ⟨14049302462872098382579315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18732403283829464510105753 14049302462872098382579315)
    ·
      refine ⟨21073953694308147573868973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14049302462872098382579315 21073953694308147573868973)
      ·
        refine ⟨7902732635365555340200865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21073953694308147573868973 7902732635365555340200865)
        ·
          refine ⟨5927049476524166505150649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7902732635365555340200865 5927049476524166505150649)
          ·
            refine ⟨4445287107393124878862987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927049476524166505150649 4445287107393124878862987)
            ·
              refine ⟨6667930661089687318294481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445287107393124878862987 6667930661089687318294481)
              ·
                refine ⟨5000947995817265488720861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6667930661089687318294481 5000947995817265488720861)
                ·
                  refine ⟨1875355498431474558270323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5000947995817265488720861 1875355498431474558270323)
                  ·
                    refine ⟨2813033247647211837405485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875355498431474558270323 2813033247647211837405485)
                    ·
                      refine ⟨1054887467867704439027057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813033247647211837405485 1054887467867704439027057)
                      ·
                        rfl

theorem cell23_2054386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2054386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054386 prefixEnd_2054386 := by exact prefixLift 2054386
  have htrace : WordTrace (prefixWord ++ tailWord_2054386) baseStart_2054386 baseEnd_2054386 := by
    simpa [prefixWord, tailWord_2054386, baseEnd_2054386] using wordTrace_append hprefix tailTrace_2054386
  have hstable : (prefixWord ++ tailWord_2054386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054386).length < 2 ^ (prefixWord ++ tailWord_2054386).sum := by decide
  have hdescent : baseEnd_2054386 < baseStart_2054386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054396 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_2054396 : Nat := 118140960795 + 2054396 * 2 ^ 59
def prefixEnd_2054396 : Nat := 4983230072969 + 3 ^ 40 * 2054396 * 2
def baseEnd_2054396 : Nat := 1054892602674249399902011

theorem tailTrace_2054396 : CollatzResearch.WordTrace tailWord_2054396 prefixEnd_2054396 1054892602674249399902011 := by
  unfold tailWord_2054396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37464988932640814874143521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49953318576854419832191361 37464988932640814874143521)
  ·
    refine ⟨28098741699480611155607641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37464988932640814874143521 28098741699480611155607641)
    ·
      refine ⟨21074056274610458366705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28098741699480611155607641 21074056274610458366705731)
      ·
        refine ⟨31611084411915687550058597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21074056274610458366705731 31611084411915687550058597)
        ·
          refine ⟨5927078327234191415635987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31611084411915687550058597 5927078327234191415635987)
          ·
            refine ⟨8890617490851287123453981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927078327234191415635987 8890617490851287123453981)
            ·
              refine ⟨3333981559069232671295243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8890617490851287123453981 3333981559069232671295243)
              ·
                refine ⟨5000972338603849006942865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333981559069232671295243 5000972338603849006942865)
                ·
                  refine ⟨3750729253952886755207149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5000972338603849006942865 3750729253952886755207149)
                  ·
                    refine ⟨1406523470232332533202681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750729253952886755207149 1406523470232332533202681)
                    ·
                      refine ⟨1054892602674249399902011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406523470232332533202681 1054892602674249399902011)
                      ·
                        rfl

theorem cell23_2054396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_2054396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054396 prefixEnd_2054396 := by exact prefixLift 2054396
  have htrace : WordTrace (prefixWord ++ tailWord_2054396) baseStart_2054396 baseEnd_2054396 := by
    simpa [prefixWord, tailWord_2054396, baseEnd_2054396] using wordTrace_append hprefix tailTrace_2054396
  have hstable : (prefixWord ++ tailWord_2054396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054396).length < 2 ^ (prefixWord ++ tailWord_2054396).sum := by decide
  have hdescent : baseEnd_2054396 < baseStart_2054396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054409 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_2054409 : Nat := 118140960795 + 2054409 * 2 ^ 59
def prefixEnd_2054409 : Nat := 4983230072969 + 3 ^ 40 * 2054409 * 2
def baseEnd_2054409 : Nat := 1054899277922757849039451

theorem tailTrace_2054409 : CollatzResearch.WordTrace tailWord_2054409 prefixEnd_2054409 1054899277922757849039451 := by
  unfold tailWord_2054409
  simp only [CollatzResearch.WordTrace]
  refine ⟨74930452014234532968510281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49953634676156355312340187 74930452014234532968510281)
  ·
    refine ⟨56197839010675899726382711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74930452014234532968510281 56197839010675899726382711)
    ·
      refine ⟨84296758516013849589574067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56197839010675899726382711 84296758516013849589574067)
      ·
        refine ⟨126445137774020774384361101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84296758516013849589574067 126445137774020774384361101)
        ·
          refine ⟨47416926665257790394135413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126445137774020774384361101 47416926665257790394135413)
          ·
            refine ⟨4445336874867917849450195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47416926665257790394135413 4445336874867917849450195)
            ·
              refine ⟨6668005312301876774175293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445336874867917849450195 6668005312301876774175293)
              ·
                refine ⟨2500501992113203790315735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6668005312301876774175293 2500501992113203790315735)
                ·
                  refine ⟨3750752988169805685473603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500501992113203790315735 3750752988169805685473603)
                  ·
                    refine ⟨5626129482254708528210405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750752988169805685473603 5626129482254708528210405)
                    ·
                      refine ⟨1054899277922757849039451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5626129482254708528210405 1054899277922757849039451)
                      ·
                        rfl

theorem cell23_2054409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_2054409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054409 prefixEnd_2054409 := by exact prefixLift 2054409
  have htrace : WordTrace (prefixWord ++ tailWord_2054409) baseStart_2054409 baseEnd_2054409 := by
    simpa [prefixWord, tailWord_2054409, baseEnd_2054409] using wordTrace_append hprefix tailTrace_2054409
  have hstable : (prefixWord ++ tailWord_2054409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054409).length < 2 ^ (prefixWord ++ tailWord_2054409).sum := by decide
  have hdescent : baseEnd_2054409 < baseStart_2054409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054412 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2054412 : Nat := 118140960795 + 2054412 * 2 ^ 59
def prefixEnd_2054412 : Nat := 4983230072969 + 3 ^ 40 * 2054412 * 2
def baseEnd_2054412 : Nat := 1054900818364721337301937

theorem tailTrace_2054412 : CollatzResearch.WordTrace tailWord_2054412 prefixEnd_2054412 1054900818364721337301937 := by
  unfold tailWord_2054412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37465280716611832240434745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49953707622149109653912993 37465280716611832240434745)
  ·
    refine ⟨28098960537458874180326059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37465280716611832240434745 28098960537458874180326059)
    ·
      refine ⟨42148440806188311270489089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28098960537458874180326059 42148440806188311270489089)
      ·
        refine ⟨31611330604641233452866817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42148440806188311270489089 31611330604641233452866817)
        ·
          refine ⟨23708497953480925089650113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31611330604641233452866817 23708497953480925089650113)
          ·
            refine ⟨17781373465110693817237585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23708497953480925089650113 17781373465110693817237585)
            ·
              refine ⟨13336030098833020362928189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781373465110693817237585 13336030098833020362928189)
              ·
                refine ⟨5001011287062382636098071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13336030098833020362928189 5001011287062382636098071)
                ·
                  refine ⟨7501516930593573954147107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001011287062382636098071 7501516930593573954147107)
                  ·
                    refine ⟨11252275395890360931220661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501516930593573954147107 11252275395890360931220661)
                    ·
                      refine ⟨1054900818364721337301937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11252275395890360931220661 1054900818364721337301937)
                      ·
                        rfl

theorem cell23_2054412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2054412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054412 prefixEnd_2054412 := by exact prefixLift 2054412
  have htrace : WordTrace (prefixWord ++ tailWord_2054412) baseStart_2054412 baseEnd_2054412 := by
    simpa [prefixWord, tailWord_2054412, baseEnd_2054412] using wordTrace_append hprefix tailTrace_2054412
  have hstable : (prefixWord ++ tailWord_2054412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054412).length < 2 ^ (prefixWord ++ tailWord_2054412).sum := by decide
  have hdescent : baseEnd_2054412 < baseStart_2054412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054469 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_2054469 : Nat := 118140960795 + 2054469 * 2 ^ 59
def prefixEnd_2054469 : Nat := 4983230072969 + 3 ^ 40 * 2054469 * 2
def baseEnd_2054469 : Nat := 1054930086762027614289175

theorem tailTrace_2054469 : CollatzResearch.WordTrace tailWord_2054469 prefixEnd_2054469 1054930086762027614289175 := by
  unfold tailWord_2054469
  simp only [CollatzResearch.WordTrace]
  refine ⟨74932640394017163215694461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49955093596011442143796307 74932640394017163215694461)
  ·
    refine ⟨28099740147756436205885423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74932640394017163215694461 28099740147756436205885423)
    ·
      refine ⟨42149610221634654308828135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28099740147756436205885423 42149610221634654308828135)
      ·
        refine ⟨63224415332451981463242203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42149610221634654308828135 63224415332451981463242203)
        ·
          refine ⟨94836622998677972194863305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63224415332451981463242203 94836622998677972194863305)
          ·
            refine ⟨71127467249008479146147479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94836622998677972194863305 71127467249008479146147479)
            ·
              refine ⟨106691200873512718719221219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71127467249008479146147479 106691200873512718719221219)
              ·
                refine ⟨160036801310269078078831829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106691200873512718719221219 160036801310269078078831829)
                ·
                  refine ⟨3750862530709431517472621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160036801310269078078831829 3750862530709431517472621)
                  ·
                    refine ⟨1406573449016036819052233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750862530709431517472621 1406573449016036819052233)
                    ·
                      refine ⟨1054930086762027614289175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406573449016036819052233 1054930086762027614289175)
                      ·
                        rfl

theorem cell23_2054469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_2054469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054469 prefixEnd_2054469 := by exact prefixLift 2054469
  have htrace : WordTrace (prefixWord ++ tailWord_2054469) baseStart_2054469 baseEnd_2054469 := by
    simpa [prefixWord, tailWord_2054469, baseEnd_2054469] using wordTrace_append hprefix tailTrace_2054469
  have hstable : (prefixWord ++ tailWord_2054469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054469).length < 2 ^ (prefixWord ++ tailWord_2054469).sum := by decide
  have hdescent : baseEnd_2054469 < baseStart_2054469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054476 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2054476 : Nat := 118140960795 + 2054476 * 2 ^ 59
def prefixEnd_2054476 : Nat := 4983230072969 + 3 ^ 40 * 2054476 * 2
def baseEnd_2054476 : Nat := 1054933681126609086901643

theorem tailTrace_2054476 : CollatzResearch.WordTrace tailWord_2054476 prefixEnd_2054476 1054933681126609086901643 := by
  unfold tailWord_2054476
  simp only [CollatzResearch.WordTrace]
  refine ⟨37466447852495901705599641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49955263803327868940799521 37466447852495901705599641)
  ·
    refine ⟨28099835889371926279199731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37466447852495901705599641 28099835889371926279199731)
    ·
      refine ⟨42149753834057889418799597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28099835889371926279199731 42149753834057889418799597)
      ·
        refine ⟨15806157687771708532049849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42149753834057889418799597 15806157687771708532049849)
        ·
          refine ⟨11854618265828781399037387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15806157687771708532049849 11854618265828781399037387)
          ·
            refine ⟨17781927398743172098556081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854618265828781399037387 17781927398743172098556081)
            ·
              refine ⟨13336445549057379073917061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781927398743172098556081 13336445549057379073917061)
              ·
                refine ⟨2500583540448258576359449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13336445549057379073917061 2500583540448258576359449)
                ·
                  refine ⟨1875437655336193932269587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500583540448258576359449 1875437655336193932269587)
                  ·
                    refine ⟨2813156483004290898404381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875437655336193932269587 2813156483004290898404381)
                    ·
                      refine ⟨1054933681126609086901643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813156483004290898404381 1054933681126609086901643)
                      ·
                        rfl

theorem cell23_2054476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2054476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054476 prefixEnd_2054476 := by exact prefixLift 2054476
  have htrace : WordTrace (prefixWord ++ tailWord_2054476) baseStart_2054476 baseEnd_2054476 := by
    simpa [prefixWord, tailWord_2054476, baseEnd_2054476] using wordTrace_append hprefix tailTrace_2054476
  have hstable : (prefixWord ++ tailWord_2054476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054476).length < 2 ^ (prefixWord ++ tailWord_2054476).sum := by decide
  have hdescent : baseEnd_2054476 < baseStart_2054476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054494 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2054494 : Nat := 118140960795 + 2054494 * 2 ^ 59
def prefixEnd_2054494 : Nat := 4983230072969 + 3 ^ 40 * 2054494 * 2
def baseEnd_2054494 : Nat := 1054942923778390016476561

theorem tailTrace_2054494 : CollatzResearch.WordTrace tailWord_2054494 prefixEnd_2054494 1054942923778390016476561 := by
  unfold tailWord_2054494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9366694027365824060669317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49955701479284394990236357 9366694027365824060669317)
  ·
    refine ⟨1756255130131092011375497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9366694027365824060669317 1756255130131092011375497)
    ·
      refine ⟨1317191347598319008531623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1756255130131092011375497 1317191347598319008531623)
      ·
        refine ⟨1975787021397478512797435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317191347598319008531623 1975787021397478512797435)
        ·
          refine ⟨2963680532096217769196153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975787021397478512797435 2963680532096217769196153)
          ·
            refine ⟨2222760399072163326897115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963680532096217769196153 2222760399072163326897115)
            ·
              refine ⟨3334140598608244990345673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222760399072163326897115 3334140598608244990345673)
              ·
                refine ⟨2500605448956183742759255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334140598608244990345673 2500605448956183742759255)
                ·
                  refine ⟨3750908173434275614138883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500605448956183742759255 3750908173434275614138883)
                  ·
                    refine ⟨5626362260151413421208325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750908173434275614138883 5626362260151413421208325)
                    ·
                      refine ⟨1054942923778390016476561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5626362260151413421208325 1054942923778390016476561)
                      ·
                        rfl

theorem cell23_2054494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2054494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054494 prefixEnd_2054494 := by exact prefixLift 2054494
  have htrace : WordTrace (prefixWord ++ tailWord_2054494) baseStart_2054494 baseEnd_2054494 := by
    simpa [prefixWord, tailWord_2054494, baseEnd_2054494] using wordTrace_append hprefix tailTrace_2054494
  have hstable : (prefixWord ++ tailWord_2054494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054494).length < 2 ^ (prefixWord ++ tailWord_2054494).sum := by decide
  have hdescent : baseEnd_2054494 < baseStart_2054494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054503 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_2054503 : Nat := 118140960795 + 2054503 * 2 ^ 59
def prefixEnd_2054503 : Nat := 4983230072969 + 3 ^ 40 * 2054503 * 2
def baseEnd_2054503 : Nat := 1054947545104280481264019

theorem tailTrace_2054503 : CollatzResearch.WordTrace tailWord_2054503 prefixEnd_2054503 1054947545104280481264019 := by
  unfold tailWord_2054503
  simp only [CollatzResearch.WordTrace]
  refine ⟨74933880475893987022432163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49955920317262658014954775 74933880475893987022432163)
  ·
    refine ⟨112400820713840980533648245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74933880475893987022432163 112400820713840980533648245)
    ·
      refine ⟨10537576941922591925029523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112400820713840980533648245 10537576941922591925029523)
      ·
        refine ⟨15806365412883887887544285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537576941922591925029523 15806365412883887887544285)
        ·
          refine ⟨5927387029831457957829107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15806365412883887887544285 5927387029831457957829107)
          ·
            refine ⟨8891080544747186936743661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927387029831457957829107 8891080544747186936743661)
            ·
              refine ⟨3334155204280195101278873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8891080544747186936743661 3334155204280195101278873)
              ·
                refine ⟨2500616403210146325959155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334155204280195101278873 2500616403210146325959155)
                ·
                  refine ⟨3750924604815219488938733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500616403210146325959155 3750924604815219488938733)
                  ·
                    refine ⟨1406596726805707308352025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3750924604815219488938733 1406596726805707308352025)
                    ·
                      refine ⟨1054947545104280481264019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406596726805707308352025 1054947545104280481264019)
                      ·
                        rfl

theorem cell23_2054503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_2054503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054503 prefixEnd_2054503 := by exact prefixLift 2054503
  have htrace : WordTrace (prefixWord ++ tailWord_2054503) baseStart_2054503 baseEnd_2054503 := by
    simpa [prefixWord, tailWord_2054503, baseEnd_2054503] using wordTrace_append hprefix tailTrace_2054503
  have hstable : (prefixWord ++ tailWord_2054503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054503).length < 2 ^ (prefixWord ++ tailWord_2054503).sum := by decide
  have hdescent : baseEnd_2054503 < baseStart_2054503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054646 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_2054646 : Nat := 118140960795 + 2054646 * 2 ^ 59
def prefixEnd_2054646 : Nat := 4983230072969 + 3 ^ 40 * 2054646 * 2
def baseEnd_2054646 : Nat := 117224552537541491308429

theorem tailTrace_2054646 : CollatzResearch.WordTrace tailWord_2054646 prefixEnd_2054646 117224552537541491308429 := by
  unfold tailWord_2054646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683693507148495152805487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49959397409583948296591861 4683693507148495152805487)
  ·
    refine ⟨7025540260722742729208231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4683693507148495152805487 7025540260722742729208231)
    ·
      refine ⟨10538310391084114093812347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025540260722742729208231 10538310391084114093812347)
      ·
        refine ⟨15807465586626171140718521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538310391084114093812347 15807465586626171140718521)
        ·
          refine ⟨11855599189969628355538891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15807465586626171140718521 11855599189969628355538891)
          ·
            refine ⟨17783398784954442533308337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855599189969628355538891 17783398784954442533308337)
            ·
              refine ⟨13337549088715831899981253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783398784954442533308337 13337549088715831899981253)
              ·
                refine ⟨2500790454134218481246485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13337549088715831899981253 2500790454134218481246485)
                ·
                  refine ⟨117224552537541491308429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2500790454134218481246485 117224552537541491308429)
                  ·
                    rfl

theorem cell23_2054646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_2054646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054646 prefixEnd_2054646 := by exact prefixLift 2054646
  have htrace : WordTrace (prefixWord ++ tailWord_2054646) baseStart_2054646 baseEnd_2054646 := by
    simpa [prefixWord, tailWord_2054646, baseEnd_2054646] using wordTrace_append hprefix tailTrace_2054646
  have hstable : (prefixWord ++ tailWord_2054646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054646).length < 2 ^ (prefixWord ++ tailWord_2054646).sum := by decide
  have hdescent : baseEnd_2054646 < baseStart_2054646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054659 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 3, 5]
def baseStart_2054659 : Nat := 118140960795 + 2054659 * 2 ^ 59
def prefixEnd_2054659 : Nat := 4983230072969 + 3 ^ 40 * 2054659 * 2
def baseEnd_2054659 : Nat := 351675882695460623637767

theorem tailTrace_2054659 : CollatzResearch.WordTrace tailWord_2054659 prefixEnd_2054659 351675882695460623637767 := by
  unfold tailWord_2054659
  simp only [CollatzResearch.WordTrace]
  refine ⟨74939570263328825665111031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49959713508885883776740687 74939570263328825665111031)
  ·
    refine ⟨112409355394993238497666547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74939570263328825665111031 112409355394993238497666547)
    ·
      refine ⟨168614033092489857746499821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112409355394993238497666547 168614033092489857746499821)
      ·
        refine ⟨63230262409683696654937433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168614033092489857746499821 63230262409683696654937433)
        ·
          refine ⟨47422696807262772491203075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63230262409683696654937433 47422696807262772491203075)
          ·
            refine ⟨71134045210894158736804613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47422696807262772491203075 71134045210894158736804613)
            ·
              refine ⟨13337633477042654763150865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71134045210894158736804613 13337633477042654763150865)
              ·
                refine ⟨10003225107781991072363149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13337633477042654763150865 10003225107781991072363149)
                ·
                  refine ⟨3751209415418246652136181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10003225107781991072363149 3751209415418246652136181)
                  ·
                    refine ⟨351675882695460623637767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3751209415418246652136181 351675882695460623637767)
                    ·
                      rfl

theorem cell23_2054659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].length) (baseStart_2054659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054659 prefixEnd_2054659 := by exact prefixLift 2054659
  have htrace : WordTrace (prefixWord ++ tailWord_2054659) baseStart_2054659 baseEnd_2054659 := by
    simpa [prefixWord, tailWord_2054659, baseEnd_2054659] using wordTrace_append hprefix tailTrace_2054659
  have hstable : (prefixWord ++ tailWord_2054659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054659).length < 2 ^ (prefixWord ++ tailWord_2054659).sum := by decide
  have hdescent : baseEnd_2054659 < baseStart_2054659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054690 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2054690 : Nat := 118140960795 + 2054690 * 2 ^ 59
def prefixEnd_2054690 : Nat := 4983230072969 + 3 ^ 40 * 2054690 * 2
def baseEnd_2054690 : Nat := 1055043565986671249625659

theorem tailTrace_2054690 : CollatzResearch.WordTrace tailWord_2054690 prefixEnd_2054690 1055043565986671249625659 := by
  unfold tailWord_2054690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735175231554129489872381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49960467284144345306326349 18735175231554129489872381)
  ·
    refine ⟨7025690711832798558702143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18735175231554129489872381 7025690711832798558702143)
    ·
      refine ⟨10538536067749197838053215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7025690711832798558702143 10538536067749197838053215)
      ·
        refine ⟨15807804101623796757079823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538536067749197838053215 15807804101623796757079823)
        ·
          refine ⟨23711706152435695135619735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807804101623796757079823 23711706152435695135619735)
          ·
            refine ⟨35567559228653542703429603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23711706152435695135619735 35567559228653542703429603)
            ·
              refine ⟨53351338842980314055144405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35567559228653542703429603 53351338842980314055144405)
              ·
                refine ⟨1250422004132351110667447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53351338842980314055144405 1250422004132351110667447)
                ·
                  refine ⟨1875633006198526666001171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250422004132351110667447 1875633006198526666001171)
                  ·
                    refine ⟨2813449509297789999001757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875633006198526666001171 2813449509297789999001757)
                    ·
                      refine ⟨1055043565986671249625659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813449509297789999001757 1055043565986671249625659)
                      ·
                        rfl

theorem cell23_2054690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2054690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054690 prefixEnd_2054690 := by exact prefixLift 2054690
  have htrace : WordTrace (prefixWord ++ tailWord_2054690) baseStart_2054690 baseEnd_2054690 := by
    simpa [prefixWord, tailWord_2054690, baseEnd_2054690] using wordTrace_append hprefix tailTrace_2054690
  have hstable : (prefixWord ++ tailWord_2054690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054690).length < 2 ^ (prefixWord ++ tailWord_2054690).sum := by decide
  have hdescent : baseEnd_2054690 < baseStart_2054690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054706 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2054706 : Nat := 118140960795 + 2054706 * 2 ^ 59
def prefixEnd_2054706 : Nat := 4983230072969 + 3 ^ 40 * 2054706 * 2
def baseEnd_2054706 : Nat := 351683927225714395675195

theorem tailTrace_2054706 : CollatzResearch.WordTrace tailWord_2054706 prefixEnd_2054706 351683927225714395675195 := by
  unfold tailWord_2054706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735321123539638173017993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49960856329439035128047981 18735321123539638173017993)
  ·
    refine ⟨14051490842654728629763495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18735321123539638173017993 14051490842654728629763495)
    ·
      refine ⟨21077236263982092944645243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14051490842654728629763495 21077236263982092944645243)
      ·
        refine ⟨31615854395973139416967865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077236263982092944645243 31615854395973139416967865)
        ·
          refine ⟨23711890796979854562725899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31615854395973139416967865 23711890796979854562725899)
          ·
            refine ⟨35567836195469781844088849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23711890796979854562725899 35567836195469781844088849)
            ·
              refine ⟨26675877146602336383066637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35567836195469781844088849 26675877146602336383066637)
              ·
                refine ⟨10003453929975876143649989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26675877146602336383066637 10003453929975876143649989)
                ·
                  refine ⟨1875647611870476776934373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10003453929975876143649989 1875647611870476776934373)
                  ·
                    refine ⟨351683927225714395675195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875647611870476776934373 351683927225714395675195)
                    ·
                      rfl

theorem cell23_2054706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2054706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054706 prefixEnd_2054706 := by exact prefixLift 2054706
  have htrace : WordTrace (prefixWord ++ tailWord_2054706) baseStart_2054706 baseEnd_2054706 := by
    simpa [prefixWord, tailWord_2054706, baseEnd_2054706] using wordTrace_append hprefix tailTrace_2054706
  have hstable : (prefixWord ++ tailWord_2054706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054706).length < 2 ^ (prefixWord ++ tailWord_2054706).sum := by decide
  have hdescent : baseEnd_2054706 < baseStart_2054706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054724 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2054724 : Nat := 118140960795 + 2054724 * 2 ^ 59
def prefixEnd_2054724 : Nat := 4983230072969 + 3 ^ 40 * 2054724 * 2
def baseEnd_2054724 : Nat := 1055061024328924116600503

theorem tailTrace_2054724 : CollatzResearch.WordTrace tailWord_2054724 prefixEnd_2054724 1055061024328924116600503 := by
  unfold tailWord_2054724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37470970504046670883113613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49961294005395561177484817 37470970504046670883113613)
  ·
    refine ⟨14051613939017501581167605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37470970504046670883113613 14051613939017501581167605)
    ·
      refine ⟨1317338806782890773234463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14051613939017501581167605 1317338806782890773234463)
      ·
        refine ⟨1976008210174336159851695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317338806782890773234463 1976008210174336159851695)
        ·
          refine ⟨2964012315261504239777543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976008210174336159851695 2964012315261504239777543)
          ·
            refine ⟨4446018472892256359666315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964012315261504239777543 4446018472892256359666315)
            ·
              refine ⟨6669027709338384539499473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446018472892256359666315 6669027709338384539499473)
              ·
                refine ⟨5001770782003788404624605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669027709338384539499473 5001770782003788404624605)
                ·
                  refine ⟨1875664043251420651734227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5001770782003788404624605 1875664043251420651734227)
                  ·
                    refine ⟨2813496064877130977601341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875664043251420651734227 2813496064877130977601341)
                    ·
                      refine ⟨1055061024328924116600503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813496064877130977601341 1055061024328924116600503)
                      ·
                        rfl

theorem cell23_2054724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2054724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054724 prefixEnd_2054724 := by exact prefixLift 2054724
  have htrace : WordTrace (prefixWord ++ tailWord_2054724) baseStart_2054724 baseEnd_2054724 := by
    simpa [prefixWord, tailWord_2054724, baseEnd_2054724] using wordTrace_append hprefix tailTrace_2054724
  have hstable : (prefixWord ++ tailWord_2054724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054724).length < 2 ^ (prefixWord ++ tailWord_2054724).sum := by decide
  have hdescent : baseEnd_2054724 < baseStart_2054724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054730 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_2054730 : Nat := 118140960795 + 2054730 * 2 ^ 59
def prefixEnd_2054730 : Nat := 4983230072969 + 3 ^ 40 * 2054730 * 2
def baseEnd_2054730 : Nat := 1055064105212851093125475

theorem tailTrace_2054730 : CollatzResearch.WordTrace tailWord_2054730 prefixEnd_2054730 1055064105212851093125475 := by
  unfold tailWord_2054730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18735539961517901197736411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49961439897381069860630429 18735539961517901197736411)
  ·
    refine ⟨28103309942276851796604617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18735539961517901197736411 28103309942276851796604617)
    ·
      refine ⟨21077482456707638847453463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28103309942276851796604617 21077482456707638847453463)
      ·
        refine ⟨31616223685061458271180195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077482456707638847453463 31616223685061458271180195)
        ·
          refine ⟨47424335527592187406770293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31616223685061458271180195 47424335527592187406770293)
          ·
            refine ⟨4446031455711767569384715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47424335527592187406770293 4446031455711767569384715)
            ·
              refine ⟨6669047183567651354077073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446031455711767569384715 6669047183567651354077073)
              ·
                refine ⟨5001785387675738515557805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669047183567651354077073 5001785387675738515557805)
                ·
                  refine ⟨1875669520378401943334177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5001785387675738515557805 1875669520378401943334177)
                  ·
                    refine ⟨1406752140283801457500633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875669520378401943334177 1406752140283801457500633)
                    ·
                      refine ⟨1055064105212851093125475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406752140283801457500633 1055064105212851093125475)
                      ·
                        rfl

theorem cell23_2054730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_2054730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054730 prefixEnd_2054730 := by exact prefixLift 2054730
  have htrace : WordTrace (prefixWord ++ tailWord_2054730) baseStart_2054730 baseEnd_2054730 := by
    simpa [prefixWord, tailWord_2054730, baseEnd_2054730] using wordTrace_append hprefix tailTrace_2054730
  have hstable : (prefixWord ++ tailWord_2054730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054730).length < 2 ^ (prefixWord ++ tailWord_2054730).sum := by decide
  have hdescent : baseEnd_2054730 < baseStart_2054730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054757 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_2054757 : Nat := 118140960795 + 2054757 * 2 ^ 59
def prefixEnd_2054757 : Nat := 4983230072969 + 3 ^ 40 * 2054757 * 2
def baseEnd_2054757 : Nat := 351692656396840829162617

theorem tailTrace_2054757 : CollatzResearch.WordTrace tailWord_2054757 prefixEnd_2054757 351692656396840829162617 := by
  unfold tailWord_2054757
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943144616973788402178525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49962096411315858934785683 74943144616973788402178525)
  ·
    refine ⟨28103679231365170650816947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74943144616973788402178525 28103679231365170650816947)
    ·
      refine ⟨42155518847047755976225421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28103679231365170650816947 42155518847047755976225421)
      ·
        refine ⟨15808319567642908491084533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42155518847047755976225421 15808319567642908491084533)
        ·
          refine ⟨1482029959466522671039175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15808319567642908491084533 1482029959466522671039175)
          ·
            refine ⟨2223044939199784006558763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482029959466522671039175 2223044939199784006558763)
            ·
              refine ⟨3334567408799676009838145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223044939199784006558763 3334567408799676009838145)
              ·
                refine ⟨2500925556599757007378609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334567408799676009838145 2500925556599757007378609)
                ·
                  refine ⟨1875694167449817755533957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500925556599757007378609 1875694167449817755533957)
                  ·
                    refine ⟨351692656396840829162617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875694167449817755533957 351692656396840829162617)
                    ·
                      rfl

theorem cell23_2054757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_2054757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054757 prefixEnd_2054757 := by exact prefixLift 2054757
  have htrace : WordTrace (prefixWord ++ tailWord_2054757) baseStart_2054757 baseEnd_2054757 := by
    simpa [prefixWord, tailWord_2054757, baseEnd_2054757] using wordTrace_append hprefix tailTrace_2054757
  have hstable : (prefixWord ++ tailWord_2054757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054757).length < 2 ^ (prefixWord ++ tailWord_2054757).sum := by decide
  have hdescent : baseEnd_2054757 < baseStart_2054757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054763 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 3]
def baseStart_2054763 : Nat := 118140960795 + 2054763 * 2 ^ 59
def prefixEnd_2054763 : Nat := 4983230072969 + 3 ^ 40 * 2054763 * 2
def baseEnd_2054763 : Nat := 1055081050074449464012823

theorem tailTrace_2054763 : CollatzResearch.WordTrace tailWord_2054763 prefixEnd_2054763 1055081050074449464012823 := by
  unfold tailWord_2054763
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943363454952051426896943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49962242303301367617931295 74943363454952051426896943)
  ·
    refine ⟨112415045182428077140345415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74943363454952051426896943 112415045182428077140345415)
    ·
      refine ⟨168622567773642115710518123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112415045182428077140345415 168622567773642115710518123)
      ·
        refine ⟨252933851660463173565777185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168622567773642115710518123 252933851660463173565777185)
        ·
          refine ⟨189700388745347380174332889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252933851660463173565777185 189700388745347380174332889)
          ·
            refine ⟨142275291559010535130749667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189700388745347380174332889 142275291559010535130749667)
            ·
              refine ⟨213412937338515802696124501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142275291559010535130749667 213412937338515802696124501)
              ·
                refine ⟨2500932859435732062845209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 213412937338515802696124501 2500932859435732062845209)
                ·
                  refine ⟨1875699644576799047133907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2500932859435732062845209 1875699644576799047133907)
                  ·
                    refine ⟨2813549466865198570700861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1875699644576799047133907 2813549466865198570700861)
                    ·
                      refine ⟨1055081050074449464012823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813549466865198570700861 1055081050074449464012823)
                      ·
                        rfl

theorem cell23_2054763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 3].length) (baseStart_2054763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054763 prefixEnd_2054763 := by exact prefixLift 2054763
  have htrace : WordTrace (prefixWord ++ tailWord_2054763) baseStart_2054763 baseEnd_2054763 := by
    simpa [prefixWord, tailWord_2054763, baseEnd_2054763] using wordTrace_append hprefix tailTrace_2054763
  have hstable : (prefixWord ++ tailWord_2054763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054763).length < 2 ^ (prefixWord ++ tailWord_2054763).sum := by decide
  have hdescent : baseEnd_2054763 < baseStart_2054763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054779 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 8]
def baseStart_2054779 : Nat := 118140960795 + 2054779 * 2 ^ 59
def prefixEnd_2054779 : Nat := 4983230072969 + 3 ^ 40 * 2054779 * 2
def baseEnd_2054779 : Nat := 351696421921640467137583

theorem tailTrace_2054779 : CollatzResearch.WordTrace tailWord_2054779 prefixEnd_2054779 351696421921640467137583 := by
  unfold tailWord_2054779
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943947022894086159479391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49962631348596057439652927 74943947022894086159479391)
  ·
    refine ⟨112415920534341129239219087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74943947022894086159479391 112415920534341129239219087)
    ·
      refine ⟨168623880801511693858828631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112415920534341129239219087 168623880801511693858828631)
      ·
        refine ⟨252935821202267540788242947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168623880801511693858828631 252935821202267540788242947)
        ·
          refine ⟨379403731803401311182364421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252935821202267540788242947 379403731803401311182364421)
          ·
            refine ⟨71138199713137745846693329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379403731803401311182364421 71138199713137745846693329)
            ·
              refine ⟨53353649784853309385019997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71138199713137745846693329 53353649784853309385019997)
              ·
                refine ⟨20007618669319991019382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53353649784853309385019997 20007618669319991019382499)
                ·
                  refine ⟨30011428003979986529073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20007618669319991019382499 30011428003979986529073749)
                  ·
                    refine ⟨351696421921640467137583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30011428003979986529073749 351696421921640467137583)
                    ·
                      rfl

theorem cell23_2054779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_2054779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054779 prefixEnd_2054779 := by exact prefixLift 2054779
  have htrace : WordTrace (prefixWord ++ tailWord_2054779) baseStart_2054779 baseEnd_2054779 := by
    simpa [prefixWord, tailWord_2054779, baseEnd_2054779] using wordTrace_append hprefix tailTrace_2054779
  have hstable : (prefixWord ++ tailWord_2054779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054779).length < 2 ^ (prefixWord ++ tailWord_2054779).sum := by decide
  have hdescent : baseEnd_2054779 < baseStart_2054779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054820 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_2054820 : Nat := 118140960795 + 2054820 * 2 ^ 59
def prefixEnd_2054820 : Nat := 4983230072969 + 3 ^ 40 * 2054820 * 2
def baseEnd_2054820 : Nat := 1055110318471755741000061

theorem tailTrace_2054820 : CollatzResearch.WordTrace tailWord_2054820 prefixEnd_2054820 1055110318471755741000061 := by
  unfold tailWord_2054820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37472721207872775080860957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49963628277163700107814609 37472721207872775080860957)
  ·
    refine ⟨14052270452952290655322859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37472721207872775080860957 14052270452952290655322859)
    ·
      refine ⟨21078405679428435982984289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14052270452952290655322859 21078405679428435982984289)
      ·
        refine ⟨15808804259571326987238217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21078405679428435982984289 15808804259571326987238217)
        ·
          refine ⟨11856603194678495240428663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15808804259571326987238217 11856603194678495240428663)
          ·
            refine ⟨17784904792017742860642995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856603194678495240428663 17784904792017742860642995)
            ·
              refine ⟨26677357188026614290964493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17784904792017742860642995 26677357188026614290964493)
              ·
                refine ⟨10004008945509980359111685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26677357188026614290964493 10004008945509980359111685)
                ·
                  refine ⟨1875751677283121317333441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10004008945509980359111685 1875751677283121317333441)
                  ·
                    refine ⟨1406813757962340988000081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875751677283121317333441 1406813757962340988000081)
                    ·
                      refine ⟨1055110318471755741000061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406813757962340988000081 1055110318471755741000061)
                      ·
                        rfl

theorem cell23_2054820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_2054820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054820 prefixEnd_2054820 := by exact prefixLift 2054820
  have htrace : WordTrace (prefixWord ++ tailWord_2054820) baseStart_2054820 baseEnd_2054820 := by
    simpa [prefixWord, tailWord_2054820, baseEnd_2054820] using wordTrace_append hprefix tailTrace_2054820
  have hstable : (prefixWord ++ tailWord_2054820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054820).length < 2 ^ (prefixWord ++ tailWord_2054820).sum := by decide
  have hdescent : baseEnd_2054820 < baseStart_2054820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054883 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2054883 : Nat := 118140960795 + 2054883 * 2 ^ 59
def prefixEnd_2054883 : Nat := 4983230072969 + 3 ^ 40 * 2054883 * 2
def baseEnd_2054883 : Nat := 1055142667752988994512271

theorem tailTrace_2054883 : CollatzResearch.WordTrace tailWord_2054883 prefixEnd_2054883 1055142667752988994512271 := by
  unfold tailWord_2054883
  simp only [CollatzResearch.WordTrace]
  refine ⟨74947740214517311921265303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49965160143011541280843535 74947740214517311921265303)
  ·
    refine ⟨112421610321775967881897955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74947740214517311921265303 112421610321775967881897955)
    ·
      refine ⟨168632415482663951822846933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112421610321775967881897955 168632415482663951822846933)
      ·
        refine ⟨3952322237874936370847975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168632415482663951822846933 3952322237874936370847975)
        ·
          refine ⟨5928483356812404556271963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952322237874936370847975 5928483356812404556271963)
          ·
            refine ⟨8892725035218606834407945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928483356812404556271963 8892725035218606834407945)
            ·
              refine ⟨6669543776413955125805959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892725035218606834407945 6669543776413955125805959)
              ·
                refine ⟨10004315664620932688708939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669543776413955125805959 10004315664620932688708939)
                ·
                  refine ⟨15006473496931399033063409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004315664620932688708939 15006473496931399033063409)
                  ·
                    refine ⟨11254855122698549274797557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15006473496931399033063409 11254855122698549274797557)
                    ·
                      refine ⟨1055142667752988994512271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11254855122698549274797557 1055142667752988994512271)
                      ·
                        rfl

theorem cell23_2054883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2054883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054883 prefixEnd_2054883 := by exact prefixLift 2054883
  have htrace : WordTrace (prefixWord ++ tailWord_2054883) baseStart_2054883 baseEnd_2054883 := by
    simpa [prefixWord, tailWord_2054883, baseEnd_2054883] using wordTrace_append hprefix tailTrace_2054883
  have hstable : (prefixWord ++ tailWord_2054883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054883).length < 2 ^ (prefixWord ++ tailWord_2054883).sum := by decide
  have hdescent : baseEnd_2054883 < baseStart_2054883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054893 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2054893 : Nat := 118140960795 + 2054893 * 2 ^ 59
def prefixEnd_2054893 : Nat := 4983230072969 + 3 ^ 40 * 2054893 * 2
def baseEnd_2054893 : Nat := 1055147802559533955387225

theorem tailTrace_2054893 : CollatzResearch.WordTrace tailWord_2054893 prefixEnd_2054893 1055147802559533955387225 := by
  unfold tailWord_2054893
  simp only [CollatzResearch.WordTrace]
  refine ⟨74948104944481083629129333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49965403296320722419419555 74948104944481083629129333)
  ·
    refine ⟨7026384838545101590230875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74948104944481083629129333 7026384838545101590230875)
    ·
      refine ⟨10539577257817652385346313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7026384838545101590230875 10539577257817652385346313)
      ·
        refine ⟨7904682943363239289009735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10539577257817652385346313 7904682943363239289009735)
        ·
          refine ⟨11857024415044858933514603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904682943363239289009735 11857024415044858933514603)
          ·
            refine ⟨17785536622567288400271905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857024415044858933514603 17785536622567288400271905)
            ·
              refine ⟨13339152466925466300203929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17785536622567288400271905 13339152466925466300203929)
              ·
                refine ⟨10004364350194099725152947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13339152466925466300203929 10004364350194099725152947)
                ·
                  refine ⟨15006546525291149587729421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004364350194099725152947 15006546525291149587729421)
                  ·
                    refine ⟨5627454946984181095398533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15006546525291149587729421 5627454946984181095398533)
                    ·
                      refine ⟨1055147802559533955387225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5627454946984181095398533 1055147802559533955387225)
                      ·
                        rfl

theorem cell23_2054893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2054893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054893 prefixEnd_2054893 := by exact prefixLift 2054893
  have htrace : WordTrace (prefixWord ++ tailWord_2054893) baseStart_2054893 baseEnd_2054893 := by
    simpa [prefixWord, tailWord_2054893, baseEnd_2054893] using wordTrace_append hprefix tailTrace_2054893
  have hstable : (prefixWord ++ tailWord_2054893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054893).length < 2 ^ (prefixWord ++ tailWord_2054893).sum := by decide
  have hdescent : baseEnd_2054893 < baseStart_2054893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054910 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2054910 : Nat := 118140960795 + 2054910 * 2 ^ 59
def prefixEnd_2054910 : Nat := 4983230072969 + 3 ^ 40 * 2054910 * 2
def baseEnd_2054910 : Nat := 1055156531730660388874647

theorem tailTrace_2054910 : CollatzResearch.WordTrace tailWord_2054910 prefixEnd_2054910 1055156531730660388874647 := by
  unfold tailWord_2054910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9368590623177436941562273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49965816656946330354998789 9368590623177436941562273)
  ·
    refine ⟨7026442967383077706171705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9368590623177436941562273 7026442967383077706171705)
    ·
      refine ⟨5269832225537308279628779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7026442967383077706171705 5269832225537308279628779)
      ·
        refine ⟨7904748338305962419443169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269832225537308279628779 7904748338305962419443169)
        ·
          refine ⟨5928561253729471814582377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7904748338305962419443169 5928561253729471814582377)
          ·
            refine ⟨4446420940297103860936783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928561253729471814582377 4446420940297103860936783)
            ·
              refine ⟨6669631410445655791405175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446420940297103860936783 6669631410445655791405175)
              ·
                refine ⟨10004447115668483687107763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669631410445655791405175 10004447115668483687107763)
                ·
                  refine ⟨15006670673502725530661645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004447115668483687107763 15006670673502725530661645)
                  ·
                    refine ⟨5627501502563522073998117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15006670673502725530661645 5627501502563522073998117)
                    ·
                      refine ⟨1055156531730660388874647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5627501502563522073998117 1055156531730660388874647)
                      ·
                        rfl

theorem cell23_2054910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2054910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054910 prefixEnd_2054910 := by exact prefixLift 2054910
  have htrace : WordTrace (prefixWord ++ tailWord_2054910) baseStart_2054910 baseEnd_2054910 := by
    simpa [prefixWord, tailWord_2054910, baseEnd_2054910] using wordTrace_append hprefix tailTrace_2054910
  have hstable : (prefixWord ++ tailWord_2054910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054910).length < 2 ^ (prefixWord ++ tailWord_2054910).sum := by decide
  have hdescent : baseEnd_2054910 < baseStart_2054910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054983 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2054983 : Nat := 118140960795 + 2054983 * 2 ^ 59
def prefixEnd_2054983 : Nat := 4983230072969 + 3 ^ 40 * 2054983 * 2
def baseEnd_2054983 : Nat := 1055194015818438603261811

theorem tailTrace_2054983 : CollatzResearch.WordTrace tailWord_2054983 prefixEnd_2054983 1055194015818438603261811 := by
  unfold tailWord_2054983
  simp only [CollatzResearch.WordTrace]
  refine ⟨74951387514155028999905603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49967591676103352666603735 74951387514155028999905603)
  ·
    refine ⟨112427081271232543499858405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74951387514155028999905603 112427081271232543499858405)
    ·
      refine ⟨21080077738356101906223451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112427081271232543499858405 21080077738356101906223451)
      ·
        refine ⟨31620116607534152859335177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21080077738356101906223451 31620116607534152859335177)
        ·
          refine ⟨23715087455650614644501383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31620116607534152859335177 23715087455650614644501383)
          ·
            refine ⟨35572631183475921966752075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23715087455650614644501383 35572631183475921966752075)
            ·
              refine ⟨53358946775213882950128113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35572631183475921966752075 53358946775213882950128113)
              ·
                refine ⟨40019210081410412212596085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53358946775213882950128113 40019210081410412212596085)
                ·
                  refine ⟨3751800945132226144930883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40019210081410412212596085 3751800945132226144930883)
                  ·
                    refine ⟨5627701417698339217396325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751800945132226144930883 5627701417698339217396325)
                    ·
                      refine ⟨1055194015818438603261811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5627701417698339217396325 1055194015818438603261811)
                      ·
                        rfl

theorem cell23_2054983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2054983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2054983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2054983 prefixEnd_2054983 := by exact prefixLift 2054983
  have htrace : WordTrace (prefixWord ++ tailWord_2054983) baseStart_2054983 baseEnd_2054983 := by
    simpa [prefixWord, tailWord_2054983, baseEnd_2054983] using wordTrace_append hprefix tailTrace_2054983
  have hstable : (prefixWord ++ tailWord_2054983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054983).length < 2 ^ (prefixWord ++ tailWord_2054983).sum := by decide
  have hdescent : baseEnd_2054983 < baseStart_2054983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055013 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2055013 : Nat := 118140960795 + 2055013 * 2 ^ 59
def prefixEnd_2055013 : Nat := 4983230072969 + 3 ^ 40 * 2055013 * 2
def baseEnd_2055013 : Nat := 1055209420238073485886673

theorem tailTrace_2055013 : CollatzResearch.WordTrace tailWord_2055013 prefixEnd_2055013 1055209420238073485886673 := by
  unfold tailWord_2055013
  simp only [CollatzResearch.WordTrace]
  refine ⟨74952481704046344123497693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49968321136030896082331795 74952481704046344123497693)
  ·
    refine ⟨28107180639017379046311635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74952481704046344123497693 28107180639017379046311635)
    ·
      refine ⟨42160770958526068569467453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28107180639017379046311635 42160770958526068569467453)
      ·
        refine ⟨15810289109447275713550295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42160770958526068569467453 15810289109447275713550295)
        ·
          refine ⟨23715433664170913570325443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15810289109447275713550295 23715433664170913570325443)
          ·
            refine ⟨35573150496256370355488165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23715433664170913570325443 35573150496256370355488165)
            ·
              refine ⟨6669965718048069441654031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35573150496256370355488165 6669965718048069441654031)
              ·
                refine ⟨10004948577072104162481047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669965718048069441654031 10004948577072104162481047)
                ·
                  refine ⟨15007422865608156243721571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004948577072104162481047 15007422865608156243721571)
                  ·
                    refine ⟨22511134298412234365582357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15007422865608156243721571 22511134298412234365582357)
                    ·
                      refine ⟨1055209420238073485886673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22511134298412234365582357 1055209420238073485886673)
                      ·
                        rfl

theorem cell23_2055013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2055013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055013 prefixEnd_2055013 := by exact prefixLift 2055013
  have htrace : WordTrace (prefixWord ++ tailWord_2055013) baseStart_2055013 baseEnd_2055013 := by
    simpa [prefixWord, tailWord_2055013, baseEnd_2055013] using wordTrace_append hprefix tailTrace_2055013
  have hstable : (prefixWord ++ tailWord_2055013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055013).length < 2 ^ (prefixWord ++ tailWord_2055013).sum := by decide
  have hdescent : baseEnd_2055013 < baseStart_2055013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055020 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_2055020 : Nat := 118140960795 + 2055020 * 2 ^ 59
def prefixEnd_2055020 : Nat := 4983230072969 + 3 ^ 40 * 2055020 * 2
def baseEnd_2055020 : Nat := 1055213014602654958499141

theorem tailTrace_2055020 : CollatzResearch.WordTrace tailWord_2055020 prefixEnd_2055020 1055213014602654958499141 := by
  unfold tailWord_2055020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37476368507510492159501257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49968491343347322879335009 37476368507510492159501257)
  ·
    refine ⟨28107276380632869119625943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37476368507510492159501257 28107276380632869119625943)
    ·
      refine ⟨42160914570949303679438915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28107276380632869119625943 42160914570949303679438915)
      ·
        refine ⟨63241371856423955519158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42160914570949303679438915 63241371856423955519158373)
        ·
          refine ⟨11857757223079491659842195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63241371856423955519158373 11857757223079491659842195)
          ·
            refine ⟨17786635834619237489763293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11857757223079491659842195 17786635834619237489763293)
            ·
              refine ⟨6669988437982214058661235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17786635834619237489763293 6669988437982214058661235)
              ·
                refine ⟨10004982656973321087991853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669988437982214058661235 10004982656973321087991853)
                ·
                  refine ⟨3751868496364995407996945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10004982656973321087991853 3751868496364995407996945)
                  ·
                    refine ⟨2813901372273746555997709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3751868496364995407996945 2813901372273746555997709)
                    ·
                      refine ⟨1055213014602654958499141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2813901372273746555997709 1055213014602654958499141)
                      ·
                        rfl

theorem cell23_2055020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_2055020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055020 prefixEnd_2055020 := by exact prefixLift 2055020
  have htrace : WordTrace (prefixWord ++ tailWord_2055020) baseStart_2055020 baseEnd_2055020 := by
    simpa [prefixWord, tailWord_2055020, baseEnd_2055020] using wordTrace_append hprefix tailTrace_2055020
  have hstable : (prefixWord ++ tailWord_2055020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055020).length < 2 ^ (prefixWord ++ tailWord_2055020).sum := by decide
  have hdescent : baseEnd_2055020 < baseStart_2055020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055034 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_2055034 : Nat := 118140960795 + 2055034 * 2 ^ 59
def prefixEnd_2055034 : Nat := 4983230072969 + 3 ^ 40 * 2055034 * 2
def baseEnd_2055034 : Nat := 1055220203331817903724077

theorem tailTrace_2055034 : CollatzResearch.WordTrace tailWord_2055034 prefixEnd_2055034 1055220203331817903724077 := by
  unfold tailWord_2055034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738311909242566177503039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49968831757980176473341437 18738311909242566177503039)
  ·
    refine ⟨28107467863863849266254559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18738311909242566177503039 28107467863863849266254559)
    ·
      refine ⟨42161201795795773899381839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28107467863863849266254559 42161201795795773899381839)
      ·
        refine ⟨63241802693693660849072759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42161201795795773899381839 63241802693693660849072759)
        ·
          refine ⟨94862704040540491273609139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63241802693693660849072759 94862704040540491273609139)
          ·
            refine ⟨142294056060810736910413709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94862704040540491273609139 142294056060810736910413709)
            ·
              refine ⟨53360271022804026341405141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142294056060810736910413709 53360271022804026341405141)
              ·
                refine ⟨1250631352096969367376683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53360271022804026341405141 1250631352096969367376683)
                ·
                  refine ⟨1875947028145454051065025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250631352096969367376683 1875947028145454051065025)
                  ·
                    refine ⟨1406960271109090538298769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875947028145454051065025 1406960271109090538298769)
                    ·
                      refine ⟨1055220203331817903724077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406960271109090538298769 1055220203331817903724077)
                      ·
                        rfl

theorem cell23_2055034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_2055034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055034 prefixEnd_2055034 := by exact prefixLift 2055034
  have htrace : WordTrace (prefixWord ++ tailWord_2055034) baseStart_2055034 baseEnd_2055034 := by
    simpa [prefixWord, tailWord_2055034, baseEnd_2055034] using wordTrace_append hprefix tailTrace_2055034
  have hstable : (prefixWord ++ tailWord_2055034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055034).length < 2 ^ (prefixWord ++ tailWord_2055034).sum := by decide
  have hdescent : baseEnd_2055034 < baseStart_2055034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055051 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 1, 2, 2]
def baseStart_2055051 : Nat := 118140960795 + 2055051 * 2 ^ 59
def prefixEnd_2055051 : Nat := 4983230072969 + 3 ^ 40 * 2055051 * 2
def baseEnd_2055051 : Nat := 1055228932502944337211499

theorem tailTrace_2055051 : CollatzResearch.WordTrace tailWord_2055051 prefixEnd_2055051 1055228932502944337211499 := by
  unfold tailWord_2055051
  simp only [CollatzResearch.WordTrace]
  refine ⟨74953867677908676613381007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49969245118605784408920671 74953867677908676613381007)
  ·
    refine ⟨112430801516863014920071511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74953867677908676613381007 112430801516863014920071511)
    ·
      refine ⟨168646202275294522380107267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112430801516863014920071511 168646202275294522380107267)
      ·
        refine ⟨252969303412941783570160901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168646202275294522380107267 252969303412941783570160901)
        ·
          refine ⟨47431744389926584419405169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252969303412941783570160901 47431744389926584419405169)
          ·
            refine ⟨35573808292444938314553877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47431744389926584419405169 35573808292444938314553877)
            ·
              refine ⟨1667522263708356483494713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35573808292444938314553877 1667522263708356483494713)
              ·
                refine ⟨1250641697781267362621035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667522263708356483494713 1250641697781267362621035)
                ·
                  refine ⟨1875962546671901043931553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250641697781267362621035 1875962546671901043931553)
                  ·
                    refine ⟨1406971910003925782948665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875962546671901043931553 1406971910003925782948665)
                    ·
                      refine ⟨1055228932502944337211499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406971910003925782948665 1055228932502944337211499)
                      ·
                        rfl

theorem cell23_2055051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 2, 2].length) (baseStart_2055051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055051 prefixEnd_2055051 := by exact prefixLift 2055051
  have htrace : WordTrace (prefixWord ++ tailWord_2055051) baseStart_2055051 baseEnd_2055051 := by
    simpa [prefixWord, tailWord_2055051, baseEnd_2055051] using wordTrace_append hprefix tailTrace_2055051
  have hstable : (prefixWord ++ tailWord_2055051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055051).length < 2 ^ (prefixWord ++ tailWord_2055051).sum := by decide
  have hdescent : baseEnd_2055051 < baseStart_2055051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055085 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2055085 : Nat := 118140960795 + 2055085 * 2 ^ 59
def prefixEnd_2055085 : Nat := 4983230072969 + 3 ^ 40 * 2055085 * 2
def baseEnd_2055085 : Nat := 1055246390845197204186343

theorem tailTrace_2055085 : CollatzResearch.WordTrace tailWord_2055085 prefixEnd_2055085 1055246390845197204186343 := by
  unfold tailWord_2055085
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955107759785500420118709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49970071839857000280079139 74955107759785500420118709)
  ·
    refine ⟨7027041352479890664386129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74955107759785500420118709 7027041352479890664386129)
    ·
      refine ⟨5270281014359917998289597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7027041352479890664386129 5270281014359917998289597)
      ·
        refine ⟨1976355380384969249358599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5270281014359917998289597 1976355380384969249358599)
        ·
          refine ⟨2964533070577453874037899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976355380384969249358599 2964533070577453874037899)
          ·
            refine ⟨4446799605866180811056849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964533070577453874037899 4446799605866180811056849)
            ·
              refine ⟨3335099704399635608292637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4446799605866180811056849 3335099704399635608292637)
              ·
                refine ⟨1250662389149863353109739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3335099704399635608292637 1250662389149863353109739)
                ·
                  refine ⟨1875993583724795029664609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250662389149863353109739 1875993583724795029664609)
                  ·
                    refine ⟨1406995187793596272248457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1875993583724795029664609 1406995187793596272248457)
                    ·
                      refine ⟨1055246390845197204186343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1406995187793596272248457 1055246390845197204186343)
                      ·
                        rfl

theorem cell23_2055085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2055085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055085 prefixEnd_2055085 := by exact prefixLift 2055085
  have htrace : WordTrace (prefixWord ++ tailWord_2055085) baseStart_2055085 baseEnd_2055085 := by
    simpa [prefixWord, tailWord_2055085, baseEnd_2055085] using wordTrace_append hprefix tailTrace_2055085
  have hstable : (prefixWord ++ tailWord_2055085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055085).length < 2 ^ (prefixWord ++ tailWord_2055085).sum := by decide
  have hdescent : baseEnd_2055085 < baseStart_2055085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055101 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2055101 : Nat := 118140960795 + 2055101 * 2 ^ 59
def prefixEnd_2055101 : Nat := 4983230072969 + 3 ^ 40 * 2055101 * 2
def baseEnd_2055101 : Nat := 1055254606535669141586269

theorem tailTrace_2055101 : CollatzResearch.WordTrace tailWord_2055101 prefixEnd_2055101 1055254606535669141586269 := by
  unfold tailWord_2055101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955691327727535152701157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49970460885151690101800771 74955691327727535152701157)
  ·
    refine ⟨14054192123948912841131467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74955691327727535152701157 14054192123948912841131467)
    ·
      refine ⟨21081288185923369261697201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14054192123948912841131467 21081288185923369261697201)
      ·
        refine ⟨15810966139442526946272901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21081288185923369261697201 15810966139442526946272901)
        ·
          refine ⟨2964556151145473802426169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15810966139442526946272901 2964556151145473802426169)
          ·
            refine ⟨2223417113359105351819627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964556151145473802426169 2223417113359105351819627)
            ·
              refine ⟨3335125670038658027729441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223417113359105351819627 3335125670038658027729441)
              ·
                refine ⟨2501344252528993520797081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335125670038658027729441 2501344252528993520797081)
                ·
                  refine ⟨1876008189396745140597811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2501344252528993520797081 1876008189396745140597811)
                  ·
                    refine ⟨2814012284095117710896717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1876008189396745140597811 2814012284095117710896717)
                    ·
                      refine ⟨1055254606535669141586269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814012284095117710896717 1055254606535669141586269)
                      ·
                        rfl

theorem cell23_2055101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2055101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055101 prefixEnd_2055101 := by exact prefixLift 2055101
  have htrace : WordTrace (prefixWord ++ tailWord_2055101) baseStart_2055101 baseEnd_2055101 := by
    simpa [prefixWord, tailWord_2055101, baseEnd_2055101] using wordTrace_append hprefix tailTrace_2055101
  have hstable : (prefixWord ++ tailWord_2055101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055101).length < 2 ^ (prefixWord ++ tailWord_2055101).sum := by decide
  have hdescent : baseEnd_2055101 < baseStart_2055101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 4, 2, 2]
def baseStart_2055107 : Nat := 118140960795 + 2055107 * 2 ^ 59
def prefixEnd_2055107 : Nat := 4983230072969 + 3 ^ 40 * 2055107 * 2
def baseEnd_2055107 : Nat := 1055257687419596118111241

theorem tailTrace_2055107 : CollatzResearch.WordTrace tailWord_2055107 prefixEnd_2055107 1055257687419596118111241 := by
  unfold tailWord_2055107
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955910165705798177419575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49970606777137198784946383 74955910165705798177419575)
  ·
    refine ⟨112433865248558697266129363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74955910165705798177419575 112433865248558697266129363)
    ·
      refine ⟨168650797872838045899194045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112433865248558697266129363 168650797872838045899194045)
      ·
        refine ⟨63244049202314267212197767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168650797872838045899194045 63244049202314267212197767)
        ·
          refine ⟨94866073803471400818296651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63244049202314267212197767 94866073803471400818296651)
          ·
            refine ⟨142299110705207101227444977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94866073803471400818296651 142299110705207101227444977)
            ·
              refine ⟨106724333028905325920583733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142299110705207101227444977 106724333028905325920583733)
              ·
                refine ⟨10005406221459874305054725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106724333028905325920583733 10005406221459874305054725)
                ·
                  refine ⟨1876013666523726432197761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10005406221459874305054725 1876013666523726432197761)
                  ·
                    refine ⟨1407010249892794824148321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876013666523726432197761 1407010249892794824148321)
                    ·
                      refine ⟨1055257687419596118111241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407010249892794824148321 1055257687419596118111241)
                      ·
                        rfl

theorem cell23_2055107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_2055107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055107 prefixEnd_2055107 := by exact prefixLift 2055107
  have htrace : WordTrace (prefixWord ++ tailWord_2055107) baseStart_2055107 baseEnd_2055107 := by
    simpa [prefixWord, tailWord_2055107, baseEnd_2055107] using wordTrace_append hprefix tailTrace_2055107
  have hstable : (prefixWord ++ tailWord_2055107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055107).length < 2 ^ (prefixWord ++ tailWord_2055107).sum := by decide
  have hdescent : baseEnd_2055107 < baseStart_2055107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055124 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2055124 : Nat := 118140960795 + 2055124 * 2 ^ 59
def prefixEnd_2055124 : Nat := 4983230072969 + 3 ^ 40 * 2055124 * 2
def baseEnd_2055124 : Nat := 1055266416590722551598663

theorem tailTrace_2055124 : CollatzResearch.WordTrace tailWord_2055124 prefixEnd_2055124 1055266416590722551598663 := by
  unfold tailWord_2055124
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478265103322105040394213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49971020137762806720525617 37478265103322105040394213)
  ·
    refine ⟨7027174706872894695073915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37478265103322105040394213 7027174706872894695073915)
    ·
      refine ⟨10540762060309342042610873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027174706872894695073915 10540762060309342042610873)
      ·
        refine ⟨7905571545232006531958155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10540762060309342042610873 7905571545232006531958155)
        ·
          refine ⟨11858357317848009797937233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905571545232006531958155 11858357317848009797937233)
          ·
            refine ⟨8893767988386007348452925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11858357317848009797937233 8893767988386007348452925)
            ·
              refine ⟨3335162995644752755669847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8893767988386007348452925 3335162995644752755669847)
              ·
                refine ⟨5002744493467129133504771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335162995644752755669847 5002744493467129133504771)
                ·
                  refine ⟨7504116740200693700257157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002744493467129133504771 7504116740200693700257157)
                  ·
                    refine ⟨1407021888787630068798217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504116740200693700257157 1407021888787630068798217)
                    ·
                      refine ⟨1055266416590722551598663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407021888787630068798217 1055266416590722551598663)
                      ·
                        rfl

theorem cell23_2055124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2055124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055124 prefixEnd_2055124 := by exact prefixLift 2055124
  have htrace : WordTrace (prefixWord ++ tailWord_2055124) baseStart_2055124 baseEnd_2055124 := by
    simpa [prefixWord, tailWord_2055124, baseEnd_2055124] using wordTrace_append hprefix tailTrace_2055124
  have hstable : (prefixWord ++ tailWord_2055124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055124).length < 2 ^ (prefixWord ++ tailWord_2055124).sum := by decide
  have hdescent : baseEnd_2055124 < baseStart_2055124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055130 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_2055130 : Nat := 118140960795 + 2055130 * 2 ^ 59
def prefixEnd_2055130 : Nat := 4983230072969 + 3 ^ 40 * 2055130 * 2
def baseEnd_2055130 : Nat := 117252166386072169791515

theorem tailTrace_2055130 : CollatzResearch.WordTrace tailWord_2055130 prefixEnd_2055130 117252166386072169791515 := by
  unfold tailWord_2055130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18739187261155618276376711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49971166029748315403671229 18739187261155618276376711)
  ·
    refine ⟨28108780891733427414565067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18739187261155618276376711 28108780891733427414565067)
    ·
      refine ⟨42163171337600141121847601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28108780891733427414565067 42163171337600141121847601)
      ·
        refine ⟨31622378503200105841385701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42163171337600141121847601 31622378503200105841385701)
        ·
          refine ⟨5929195969350019845259819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31622378503200105841385701 5929195969350019845259819)
          ·
            refine ⟨8893793954025029767889729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929195969350019845259819 8893793954025029767889729)
            ·
              refine ⟨6670345465518772325917297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8893793954025029767889729 6670345465518772325917297)
              ·
                refine ⟨5002759099139079244437973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6670345465518772325917297 5002759099139079244437973)
                ·
                  refine ⟨117252166386072169791515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5002759099139079244437973 117252166386072169791515)
                  ·
                    rfl

theorem cell23_2055130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_2055130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055130 prefixEnd_2055130 := by exact prefixLift 2055130
  have htrace : WordTrace (prefixWord ++ tailWord_2055130) baseStart_2055130 baseEnd_2055130 := by
    simpa [prefixWord, tailWord_2055130, baseEnd_2055130] using wordTrace_append hprefix tailTrace_2055130
  have hstable : (prefixWord ++ tailWord_2055130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055130).length < 2 ^ (prefixWord ++ tailWord_2055130).sum := by decide
  have hdescent : baseEnd_2055130 < baseStart_2055130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055140 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_2055140 : Nat := 118140960795 + 2055140 * 2 ^ 59
def prefixEnd_2055140 : Nat := 4983230072969 + 3 ^ 40 * 2055140 * 2
def baseEnd_2055140 : Nat := 1055274632281194488998589

theorem tailTrace_2055140 : CollatzResearch.WordTrace tailWord_2055140 prefixEnd_2055140 1055274632281194488998589 := by
  unfold tailWord_2055140
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478556887293122406685437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49971409183057496542247249 37478556887293122406685437)
  ·
    refine ⟨14054458832734920902507039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37478556887293122406685437 14054458832734920902507039)
    ·
      refine ⟨21081688249102381353760559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14054458832734920902507039 21081688249102381353760559)
      ·
        refine ⟨31622532373653572030640839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21081688249102381353760559 31622532373653572030640839)
        ·
          refine ⟨47433798560480358045961259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622532373653572030640839 47433798560480358045961259)
          ·
            refine ⟨71150697840720537068941889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47433798560480358045961259 71150697840720537068941889)
            ·
              refine ⟨53363023380540402801706417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71150697840720537068941889 53363023380540402801706417)
              ·
                refine ⟨40022267535405302101279813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53363023380540402801706417 40022267535405302101279813)
                ·
                  refine ⟨7504175162888494143989965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40022267535405302101279813 7504175162888494143989965)
                  ·
                    refine ⟨2814065686083185303996237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7504175162888494143989965 2814065686083185303996237)
                    ·
                      refine ⟨1055274632281194488998589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814065686083185303996237 1055274632281194488998589)
                      ·
                        rfl

theorem cell23_2055140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_2055140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055140 prefixEnd_2055140 := by exact prefixLift 2055140
  have htrace : WordTrace (prefixWord ++ tailWord_2055140) baseStart_2055140 baseEnd_2055140 := by
    simpa [prefixWord, tailWord_2055140, baseEnd_2055140] using wordTrace_append hprefix tailTrace_2055140
  have hstable : (prefixWord ++ tailWord_2055140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055140).length < 2 ^ (prefixWord ++ tailWord_2055140).sum := by decide
  have hdescent : baseEnd_2055140 < baseStart_2055140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055164 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 5]
def baseStart_2055164 : Nat := 118140960795 + 2055164 * 2 ^ 59
def prefixEnd_2055164 : Nat := 4983230072969 + 3 ^ 40 * 2055164 * 2
def baseEnd_2055164 : Nat := 117254106201878043899831

theorem tailTrace_2055164 : CollatzResearch.WordTrace tailWord_2055164 prefixEnd_2055164 117254106201878043899831 := by
  unfold tailWord_2055164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478994563249648456122273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49971992750999531274829697 37478994563249648456122273)
  ·
    refine ⟨28109245922437236342091705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37478994563249648456122273 28109245922437236342091705)
    ·
      refine ⟨21081934441827927256568779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28109245922437236342091705 21081934441827927256568779)
      ·
        refine ⟨31622901662741890884853169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21081934441827927256568779 31622901662741890884853169)
        ·
          refine ⟨23717176247056418163639877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31622901662741890884853169 23717176247056418163639877)
          ·
            refine ⟨4446970546323078405682477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23717176247056418163639877 4446970546323078405682477)
            ·
              refine ⟨1667613954871154402130929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4446970546323078405682477 1667613954871154402130929)
              ·
                refine ⟨1250710466153365801598197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667613954871154402130929 1250710466153365801598197)
                ·
                  refine ⟨117254106201878043899831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250710466153365801598197 117254106201878043899831)
                  ·
                    rfl

theorem cell23_2055164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_2055164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055164 prefixEnd_2055164 := by exact prefixLift 2055164
  have htrace : WordTrace (prefixWord ++ tailWord_2055164) baseStart_2055164 baseEnd_2055164 := by
    simpa [prefixWord, tailWord_2055164, baseEnd_2055164] using wordTrace_append hprefix tailTrace_2055164
  have hstable : (prefixWord ++ tailWord_2055164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055164).length < 2 ^ (prefixWord ++ tailWord_2055164).sum := by decide
  have hdescent : baseEnd_2055164 < baseStart_2055164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055214 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2055214 : Nat := 118140960795 + 2055214 * 2 ^ 59
def prefixEnd_2055214 : Nat := 4983230072969 + 3 ^ 40 * 2055214 * 2
def baseEnd_2055214 : Nat := 1055312629849627199473249

theorem tailTrace_2055214 : CollatzResearch.WordTrace tailWord_2055214 prefixEnd_2055214 1055312629849627199473249 := by
  unfold tailWord_2055214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9369976597039769431445587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49973208517545436967709797 9369976597039769431445587)
  ·
    refine ⟨14054964895559654147168381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9369976597039769431445587 14054964895559654147168381)
    ·
      refine ⟨5270611835834870305188143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14054964895559654147168381 5270611835834870305188143)
      ·
        refine ⟨7905917753752305457782215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270611835834870305188143 7905917753752305457782215)
        ·
          refine ⟨11858876630628458186673323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905917753752305457782215 11858876630628458186673323)
          ·
            refine ⟨17788314945942687280009985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858876630628458186673323 17788314945942687280009985)
            ·
              refine ⟨13341236209457015460007489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17788314945942687280009985 13341236209457015460007489)
              ·
                refine ⟨10005927157092761595005617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13341236209457015460007489 10005927157092761595005617)
                ·
                  refine ⟨7504445367819571196254213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005927157092761595005617 7504445367819571196254213)
                  ·
                    refine ⟨1407083506466169599297665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7504445367819571196254213 1407083506466169599297665)
                    ·
                      refine ⟨1055312629849627199473249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407083506466169599297665 1055312629849627199473249)
                      ·
                        rfl

theorem cell23_2055214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2055214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055214 prefixEnd_2055214 := by exact prefixLift 2055214
  have htrace : WordTrace (prefixWord ++ tailWord_2055214) baseStart_2055214 baseEnd_2055214 := by
    simpa [prefixWord, tailWord_2055214, baseEnd_2055214] using wordTrace_append hprefix tailTrace_2055214
  have hstable : (prefixWord ++ tailWord_2055214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055214).length < 2 ^ (prefixWord ++ tailWord_2055214).sum := by decide
  have hdescent : baseEnd_2055214 < baseStart_2055214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055217 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2055217 : Nat := 118140960795 + 2055217 * 2 ^ 59
def prefixEnd_2055217 : Nat := 4983230072969 + 3 ^ 40 * 2055217 * 2
def baseEnd_2055217 : Nat := 1055314170291590687735735

theorem tailTrace_2055217 : CollatzResearch.WordTrace tailWord_2055217 prefixEnd_2055217 1055314170291590687735735 := by
  unfold tailWord_2055217
  simp only [CollatzResearch.WordTrace]
  refine ⟨74959922195307286963923905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49973281463538191309282603 74959922195307286963923905)
  ·
    refine ⟨56219941646480465222942929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74959922195307286963923905 56219941646480465222942929)
    ·
      refine ⟨42164956234860348917207197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56219941646480465222942929 42164956234860348917207197)
      ·
        refine ⟨15811858588072630843952699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42164956234860348917207197 15811858588072630843952699)
        ·
          refine ⟨23717787882108946265929049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15811858588072630843952699 23717787882108946265929049)
          ·
            refine ⟨17788340911581709699446787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23717787882108946265929049 17788340911581709699446787)
            ·
              refine ⟨26682511367372564549170181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17788340911581709699446787 26682511367372564549170181)
              ·
                refine ⟨5002970881382355852969409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26682511367372564549170181 5002970881382355852969409)
                ·
                  refine ⟨3752228161036766889727057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5002970881382355852969409 3752228161036766889727057)
                  ·
                    refine ⟨2814171120777575167295293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3752228161036766889727057 2814171120777575167295293)
                    ·
                      refine ⟨1055314170291590687735735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814171120777575167295293 1055314170291590687735735)
                      ·
                        rfl

theorem cell23_2055217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2055217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055217 prefixEnd_2055217 := by exact prefixLift 2055217
  have htrace : WordTrace (prefixWord ++ tailWord_2055217) baseStart_2055217 baseEnd_2055217 := by
    simpa [prefixWord, tailWord_2055217, baseEnd_2055217] using wordTrace_append hprefix tailTrace_2055217
  have hstable : (prefixWord ++ tailWord_2055217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055217).length < 2 ^ (prefixWord ++ tailWord_2055217).sum := by decide
  have hdescent : baseEnd_2055217 < baseStart_2055217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055307 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3]
def baseStart_2055307 : Nat := 118140960795 + 2055307 * 2 ^ 59
def prefixEnd_2055307 : Nat := 4983230072969 + 3 ^ 40 * 2055307 * 2
def baseEnd_2055307 : Nat := 1055360383550495335610321

theorem tailTrace_2055307 : CollatzResearch.WordTrace tailWord_2055307 prefixEnd_2055307 1055360383550495335610321 := by
  unfold tailWord_2055307
  simp only [CollatzResearch.WordTrace]
  refine ⟨74963204764981232334700175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49975469843320821556466783 74963204764981232334700175)
  ·
    refine ⟨112444807147471848502050263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74963204764981232334700175 112444807147471848502050263)
    ·
      refine ⟨168667210721207772753075395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112444807147471848502050263 168667210721207772753075395)
      ·
        refine ⟨253000816081811659129613093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168667210721207772753075395 253000816081811659129613093)
        ·
          refine ⟨47437653015339686086802455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253000816081811659129613093 47437653015339686086802455)
          ·
            refine ⟨71156479523009529130203683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47437653015339686086802455 71156479523009529130203683)
            ·
              refine ⟨106734719284514293695305525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71156479523009529130203683 106734719284514293695305525)
              ·
                refine ⟨10006379932923215033934893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106734719284514293695305525 10006379932923215033934893)
                ·
                  refine ⟨3752392474846205637725585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10006379932923215033934893 3752392474846205637725585)
                  ·
                    refine ⟨2814294356134654228294189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3752392474846205637725585 2814294356134654228294189)
                    ·
                      refine ⟨1055360383550495335610321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814294356134654228294189 1055360383550495335610321)
                      ·
                        rfl

theorem cell23_2055307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].length) (baseStart_2055307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055307 prefixEnd_2055307 := by exact prefixLift 2055307
  have htrace : WordTrace (prefixWord ++ tailWord_2055307) baseStart_2055307 baseEnd_2055307 := by
    simpa [prefixWord, tailWord_2055307, baseEnd_2055307] using wordTrace_append hprefix tailTrace_2055307
  have hstable : (prefixWord ++ tailWord_2055307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055307).length < 2 ^ (prefixWord ++ tailWord_2055307).sum := by decide
  have hdescent : baseEnd_2055307 < baseStart_2055307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055314 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2055314 : Nat := 118140960795 + 2055314 * 2 ^ 59
def prefixEnd_2055314 : Nat := 4983230072969 + 3 ^ 40 * 2055314 * 2
def baseEnd_2055314 : Nat := 351787992638358936074263

theorem tailTrace_2055314 : CollatzResearch.WordTrace tailWord_2055314 prefixEnd_2055314 351787992638358936074263 := by
  unfold tailWord_2055314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740865018988968132551249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49975640050637248353469997 18740865018988968132551249)
  ·
    refine ⟨14055648764241726099413437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18740865018988968132551249 14055648764241726099413437)
    ·
      refine ⟨5270868286590647287280039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14055648764241726099413437 5270868286590647287280039)
      ·
        refine ⟨7906302429885970930920059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270868286590647287280039 7906302429885970930920059)
        ·
          refine ⟨11859453644828956396380089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906302429885970930920059 11859453644828956396380089)
          ·
            refine ⟨8894590233621717297285067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11859453644828956396380089 8894590233621717297285067)
            ·
              refine ⟨13341885350432575945927601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894590233621717297285067 13341885350432575945927601)
              ·
                refine ⟨10006414012824431959445701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13341885350432575945927601 10006414012824431959445701)
                ·
                  refine ⟨1876202627404580992396069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10006414012824431959445701 1876202627404580992396069)
                  ·
                    refine ⟨351787992638358936074263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876202627404580992396069 351787992638358936074263)
                    ·
                      rfl

theorem cell23_2055314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2055314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055314 prefixEnd_2055314 := by exact prefixLift 2055314
  have htrace : WordTrace (prefixWord ++ tailWord_2055314) baseStart_2055314 baseEnd_2055314 := by
    simpa [prefixWord, tailWord_2055314, baseEnd_2055314] using wordTrace_append hprefix tailTrace_2055314
  have hstable : (prefixWord ++ tailWord_2055314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055314).length < 2 ^ (prefixWord ++ tailWord_2055314).sum := by decide
  have hdescent : baseEnd_2055314 < baseStart_2055314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055324 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2055324 : Nat := 118140960795 + 2055324 * 2 ^ 59
def prefixEnd_2055324 : Nat := 4983230072969 + 3 ^ 40 * 2055324 * 2
def baseEnd_2055324 : Nat := 1055369112721621769097743

theorem tailTrace_2055324 : CollatzResearch.WordTrace tailWord_2055324 prefixEnd_2055324 1055369112721621769097743 := by
  unfold tailWord_2055324
  simp only [CollatzResearch.WordTrace]
  refine ⟨37481912402959822119034513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49975883203946429492046017 37481912402959822119034513)
  ·
    refine ⟨28111434302219866589275885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37481912402959822119034513 28111434302219866589275885)
    ·
      refine ⟨10541787863332449970978457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28111434302219866589275885 10541787863332449970978457)
      ·
        refine ⟨7906340897499337478233843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10541787863332449970978457 7906340897499337478233843)
        ·
          refine ⟨11859511346249006217350765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906340897499337478233843 11859511346249006217350765)
          ·
            refine ⟨4447316754843377331506537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11859511346249006217350765 4447316754843377331506537)
            ·
              refine ⟨3335487566132532998629903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447316754843377331506537 3335487566132532998629903)
              ·
                refine ⟨5003231349198799497944855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335487566132532998629903 5003231349198799497944855)
                ·
                  refine ⟨7504847023798199246917283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003231349198799497944855 7504847023798199246917283)
                  ·
                    refine ⟨11257270535697298870375925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504847023798199246917283 11257270535697298870375925)
                    ·
                      refine ⟨1055369112721621769097743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11257270535697298870375925 1055369112721621769097743)
                      ·
                        rfl

theorem cell23_2055324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2055324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055324 prefixEnd_2055324 := by exact prefixLift 2055324
  have htrace : WordTrace (prefixWord ++ tailWord_2055324) baseStart_2055324 baseEnd_2055324 := by
    simpa [prefixWord, tailWord_2055324, baseEnd_2055324] using wordTrace_append hprefix tailTrace_2055324
  have hstable : (prefixWord ++ tailWord_2055324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055324).length < 2 ^ (prefixWord ++ tailWord_2055324).sum := by decide
  have hdescent : baseEnd_2055324 < baseStart_2055324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055358 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2055358 : Nat := 118140960795 + 2055358 * 2 ^ 59
def prefixEnd_2055358 : Nat := 4983230072969 + 3 ^ 40 * 2055358 * 2
def baseEnd_2055358 : Nat := 1055386571063874636072587

theorem tailTrace_2055358 : CollatzResearch.WordTrace tailWord_2055358 prefixEnd_2055358 1055386571063874636072587 := by
  unfold tailWord_2055358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370633110974558505600841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49976709925197645363204485 9370633110974558505600841)
  ·
    refine ⟨7027974833230918879200631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9370633110974558505600841 7027974833230918879200631)
    ·
      refine ⟨10541962249846378318800947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027974833230918879200631 10541962249846378318800947)
      ·
        refine ⟨15812943374769567478201421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10541962249846378318800947 15812943374769567478201421)
        ·
          refine ⟨5929853765538587804325533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15812943374769567478201421 5929853765538587804325533)
          ·
            refine ⟨2223695162076970426622075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5929853765538587804325533 2223695162076970426622075)
            ·
              refine ⟨3335542743115455639933113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223695162076970426622075 3335542743115455639933113)
              ·
                refine ⟨2501657057336591729949835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335542743115455639933113 2501657057336591729949835)
                ·
                  refine ⟨3752485586004887594924753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501657057336591729949835 3752485586004887594924753)
                  ·
                    refine ⟨2814364189503665696193565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3752485586004887594924753 2814364189503665696193565)
                    ·
                      refine ⟨1055386571063874636072587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814364189503665696193565 1055386571063874636072587)
                      ·
                        rfl

theorem cell23_2055358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2055358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055358 prefixEnd_2055358 := by exact prefixLift 2055358
  have htrace : WordTrace (prefixWord ++ tailWord_2055358) baseStart_2055358 baseEnd_2055358 := by
    simpa [prefixWord, tailWord_2055358, baseEnd_2055358] using wordTrace_append hprefix tailTrace_2055358
  have hstable : (prefixWord ++ tailWord_2055358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055358).length < 2 ^ (prefixWord ++ tailWord_2055358).sum := by decide
  have hdescent : baseEnd_2055358 < baseStart_2055358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055389 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2055389 : Nat := 118140960795 + 2055389 * 2 ^ 59
def prefixEnd_2055389 : Nat := 4983230072969 + 3 ^ 40 * 2055389 * 2
def baseEnd_2055389 : Nat := 1055402488964164014784945

theorem tailTrace_2055389 : CollatzResearch.WordTrace tailWord_2055389 prefixEnd_2055389 1055402488964164014784945 := by
  unfold tailWord_2055389
  simp only [CollatzResearch.WordTrace]
  refine ⟨74966195550684160339185221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49977463700456106892790147 74966195550684160339185221)
  ·
    refine ⟨14056161665753280063597229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74966195550684160339185221 14056161665753280063597229)
    ·
      refine ⟨5271060624657480023848961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14056161665753280063597229 5271060624657480023848961)
      ·
        refine ⟨3953295468493110017886721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5271060624657480023848961 3953295468493110017886721)
        ·
          refine ⟨2964971601369832513415041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953295468493110017886721 2964971601369832513415041)
          ·
            refine ⟨2223728701027374385061281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2964971601369832513415041 2223728701027374385061281)
            ·
              refine ⟨1667796525770530788795961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223728701027374385061281 1667796525770530788795961)
              ·
                refine ⟨1250847394327898091596971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667796525770530788795961 1250847394327898091596971)
                ·
                  refine ⟨1876271091491847137395457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1250847394327898091596971 1876271091491847137395457)
                  ·
                    refine ⟨1407203318618885353046593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876271091491847137395457 1407203318618885353046593)
                    ·
                      refine ⟨1055402488964164014784945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407203318618885353046593 1055402488964164014784945)
                      ·
                        rfl

theorem cell23_2055389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2055389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055389 prefixEnd_2055389 := by exact prefixLift 2055389
  have htrace : WordTrace (prefixWord ++ tailWord_2055389) baseStart_2055389 baseEnd_2055389 := by
    simpa [prefixWord, tailWord_2055389, baseEnd_2055389] using wordTrace_append hprefix tailTrace_2055389
  have hstable : (prefixWord ++ tailWord_2055389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055389).length < 2 ^ (prefixWord ++ tailWord_2055389).sum := by decide
  have hdescent : baseEnd_2055389 < baseStart_2055389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055411 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 4, 2]
def baseStart_2055411 : Nat := 118140960795 + 2055411 * 2 ^ 59
def prefixEnd_2055411 : Nat := 4983230072969 + 3 ^ 40 * 2055411 * 2
def baseEnd_2055411 : Nat := 1055413785538562928709843

theorem tailTrace_2055411 : CollatzResearch.WordTrace tailWord_2055411 prefixEnd_2055411 1055413785538562928709843 := by
  unfold tailWord_2055411
  simp only [CollatzResearch.WordTrace]
  refine ⟨74966997956604458096486087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49977998637736305397657391 74966997956604458096486087)
  ·
    refine ⟨112450496934906687144729131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74966997956604458096486087 112450496934906687144729131)
    ·
      refine ⟨168675745402360030717093697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112450496934906687144729131 168675745402360030717093697)
      ·
        refine ⟨126506809051770023037820273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168675745402360030717093697 126506809051770023037820273)
        ·
          refine ⟨94880106788827517278365205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126506809051770023037820273 94880106788827517278365205)
          ·
            refine ⟨4447505005726289872423369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94880106788827517278365205 4447505005726289872423369)
            ·
              refine ⟨3335628754294717404317527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447505005726289872423369 3335628754294717404317527)
              ·
                refine ⟨5003443131442076106476291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335628754294717404317527 5003443131442076106476291)
                ·
                  refine ⟨7505164697163114159714437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003443131442076106476291 7505164697163114159714437)
                  ·
                    refine ⟨1407218380718083904946457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7505164697163114159714437 1407218380718083904946457)
                    ·
                      refine ⟨1055413785538562928709843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407218380718083904946457 1055413785538562928709843)
                      ·
                        rfl

theorem cell23_2055411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 4, 2].length) (baseStart_2055411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055411 prefixEnd_2055411 := by exact prefixLift 2055411
  have htrace : WordTrace (prefixWord ++ tailWord_2055411) baseStart_2055411 baseEnd_2055411 := by
    simpa [prefixWord, tailWord_2055411, baseEnd_2055411] using wordTrace_append hprefix tailTrace_2055411
  have hstable : (prefixWord ++ tailWord_2055411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055411).length < 2 ^ (prefixWord ++ tailWord_2055411).sum := by decide
  have hdescent : baseEnd_2055411 < baseStart_2055411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055414 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2055414 : Nat := 118140960795 + 2055414 * 2 ^ 59
def prefixEnd_2055414 : Nat := 4983230072969 + 3 ^ 40 * 2055414 * 2
def baseEnd_2055414 : Nat := 1055415325980526416972329

theorem tailTrace_2055414 : CollatzResearch.WordTrace tailWord_2055414 prefixEnd_2055414 1055415325980526416972329 := by
  unfold tailWord_2055414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685444210974599350552831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49978071583729059739230197 4685444210974599350552831)
  ·
    refine ⟨7028166316461899025829247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685444210974599350552831 7028166316461899025829247)
    ·
      refine ⟨10542249474692848538743871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028166316461899025829247 10542249474692848538743871)
      ·
        refine ⟨15813374212039272808115807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542249474692848538743871 15813374212039272808115807)
        ·
          refine ⟨23720061318058909212173711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813374212039272808115807 23720061318058909212173711)
          ·
            refine ⟨35580091977088363818260567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23720061318058909212173711 35580091977088363818260567)
            ·
              refine ⟨53370137965632545727390851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35580091977088363818260567 53370137965632545727390851)
              ·
                refine ⟨80055206948448818591086277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53370137965632545727390851 80055206948448818591086277)
                ·
                  refine ⟨15010351302834153485828677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80055206948448818591086277 15010351302834153485828677)
                  ·
                    refine ⟨2814440869281403778592877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15010351302834153485828677 2814440869281403778592877)
                    ·
                      refine ⟨1055415325980526416972329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814440869281403778592877 1055415325980526416972329)
                      ·
                        rfl

theorem cell23_2055414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2055414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055414 prefixEnd_2055414 := by exact prefixLift 2055414
  have htrace : WordTrace (prefixWord ++ tailWord_2055414) baseStart_2055414 baseEnd_2055414 := by
    simpa [prefixWord, tailWord_2055414, baseEnd_2055414] using wordTrace_append hprefix tailTrace_2055414
  have hstable : (prefixWord ++ tailWord_2055414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055414).length < 2 ^ (prefixWord ++ tailWord_2055414).sum := by decide
  have hdescent : baseEnd_2055414 < baseStart_2055414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055417 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 7]
def baseStart_2055417 : Nat := 118140960795 + 2055417 * 2 ^ 59
def prefixEnd_2055417 : Nat := 4983230072969 + 3 ^ 40 * 2055417 * 2
def baseEnd_2055417 : Nat := 117268540713609989470535

theorem tailTrace_2055417 : CollatzResearch.WordTrace tailWord_2055417 prefixEnd_2055417 117268540713609989470535 := by
  unfold tailWord_2055417
  simp only [CollatzResearch.WordTrace]
  refine ⟨74967216794582721121204505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49978144529721814080803003 74967216794582721121204505)
  ·
    refine ⟨56225412595937040840903379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74967216794582721121204505 56225412595937040840903379)
    ·
      refine ⟨84338118893905561261355069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56225412595937040840903379 84338118893905561261355069)
      ·
        refine ⟨31626794585214585473008151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84338118893905561261355069 31626794585214585473008151)
        ·
          refine ⟨47440191877821878209512227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31626794585214585473008151 47440191877821878209512227)
          ·
            refine ⟨71160287816732817314268341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47440191877821878209512227 71160287816732817314268341)
            ·
              refine ⟨6671276982818701623212657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71160287816732817314268341 6671276982818701623212657)
              ·
                refine ⟨5003457737114026217409493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6671276982818701623212657 5003457737114026217409493)
                ·
                  refine ⟨117268540713609989470535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5003457737114026217409493 117268540713609989470535)
                  ·
                    rfl

theorem cell23_2055417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_2055417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055417 prefixEnd_2055417 := by exact prefixLift 2055417
  have htrace : WordTrace (prefixWord ++ tailWord_2055417) baseStart_2055417 baseEnd_2055417 := by
    simpa [prefixWord, tailWord_2055417, baseEnd_2055417] using wordTrace_append hprefix tailTrace_2055417
  have hstable : (prefixWord ++ tailWord_2055417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055417).length < 2 ^ (prefixWord ++ tailWord_2055417).sum := by decide
  have hdescent : baseEnd_2055417 < baseStart_2055417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055432 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_2055432 : Nat := 118140960795 + 2055432 * 2 ^ 59
def prefixEnd_2055432 : Nat := 4983230072969 + 3 ^ 40 * 2055432 * 2
def baseEnd_2055432 : Nat := 1055424568632307346547247

theorem tailTrace_2055432 : CollatzResearch.WordTrace tailWord_2055432 prefixEnd_2055432 1055424568632307346547247 := by
  unfold tailWord_2055432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37483881944764189341500275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49978509259685585788667033 37483881944764189341500275)
  ·
    refine ⟨56225822917146284012250413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37483881944764189341500275 56225822917146284012250413)
    ·
      refine ⟨21084683593929856504593905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56225822917146284012250413 21084683593929856504593905)
      ·
        refine ⟨15813512695447392378445429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21084683593929856504593905 15813512695447392378445429)
        ·
          refine ⟨1482516815198193035479259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15813512695447392378445429 1482516815198193035479259)
          ·
            refine ⟨2223775222797289553218889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482516815198193035479259 2223775222797289553218889)
            ·
              refine ⟨1667831417097967164914167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223775222797289553218889 1667831417097967164914167)
              ·
                refine ⟨2501747125646950747371251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667831417097967164914167 2501747125646950747371251)
                ·
                  refine ⟨3752620688470426121056877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501747125646950747371251 3752620688470426121056877)
                  ·
                    refine ⟨1407232758176409795396329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3752620688470426121056877 1407232758176409795396329)
                    ·
                      refine ⟨1055424568632307346547247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407232758176409795396329 1055424568632307346547247)
                      ·
                        rfl

theorem cell23_2055432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_2055432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055432 prefixEnd_2055432 := by exact prefixLift 2055432
  have htrace : WordTrace (prefixWord ++ tailWord_2055432) baseStart_2055432 baseEnd_2055432 := by
    simpa [prefixWord, tailWord_2055432, baseEnd_2055432] using wordTrace_append hprefix tailTrace_2055432
  have hstable : (prefixWord ++ tailWord_2055432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055432).length < 2 ^ (prefixWord ++ tailWord_2055432).sum := by decide
  have hdescent : baseEnd_2055432 < baseStart_2055432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055457 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2055457 : Nat := 118140960795 + 2055457 * 2 ^ 59
def prefixEnd_2055457 : Nat := 4983230072969 + 3 ^ 40 * 2055457 * 2
def baseEnd_2055457 : Nat := 1055437405648669748734631

theorem tailTrace_2055457 : CollatzResearch.WordTrace tailWord_2055457 prefixEnd_2055457 1055437405648669748734631 := by
  unfold tailWord_2055457
  simp only [CollatzResearch.WordTrace]
  refine ⟨74968675714437807952660625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49979117142958538635107083 74968675714437807952660625)
  ·
    refine ⟨56226506785828355964495469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74968675714437807952660625 56226506785828355964495469)
    ·
      refine ⟨21084940044685633486685801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56226506785828355964495469 21084940044685633486685801)
      ·
        refine ⟨15813705033514225115014351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21084940044685633486685801 15813705033514225115014351)
        ·
          refine ⟨23720557550271337672521527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813705033514225115014351 23720557550271337672521527)
          ·
            refine ⟨35580836325407006508782291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23720557550271337672521527 35580836325407006508782291)
            ·
              refine ⟨53371254488110509763173437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35580836325407006508782291 53371254488110509763173437)
              ·
                refine ⟨20014220433041441161190039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53371254488110509763173437 20014220433041441161190039)
                ·
                  refine ⟨30021330649562161741785059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20014220433041441161190039 30021330649562161741785059)
                  ·
                    refine ⟨45031995974343242612677589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30021330649562161741785059 45031995974343242612677589)
                    ·
                      refine ⟨1055437405648669748734631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45031995974343242612677589 1055437405648669748734631)
                      ·
                        rfl

theorem cell23_2055457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2055457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055457 prefixEnd_2055457 := by exact prefixLift 2055457
  have htrace : WordTrace (prefixWord ++ tailWord_2055457) baseStart_2055457 baseEnd_2055457 := by
    simpa [prefixWord, tailWord_2055457, baseEnd_2055457] using wordTrace_append hprefix tailTrace_2055457
  have hstable : (prefixWord ++ tailWord_2055457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055457).length < 2 ^ (prefixWord ++ tailWord_2055457).sum := by decide
  have hdescent : baseEnd_2055457 < baseStart_2055457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055464 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2055464 : Nat := 118140960795 + 2055464 * 2 ^ 59
def prefixEnd_2055464 : Nat := 4983230072969 + 3 ^ 40 * 2055464 * 2
def baseEnd_2055464 : Nat := 351813666671083740449033

theorem tailTrace_2055464 : CollatzResearch.WordTrace tailWord_2055464 prefixEnd_2055464 351813666671083740449033 := by
  unfold tailWord_2055464
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484465512706224074082723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49979287350274965432110297 37484465512706224074082723)
  ·
    refine ⟨56226698269059336111124085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37484465512706224074082723 56226698269059336111124085)
    ·
      refine ⟨5271252962724312760417883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56226698269059336111124085 5271252962724312760417883)
      ·
        refine ⟨7906879444086469140626825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271252962724312760417883 7906879444086469140626825)
        ·
          refine ⟨5930159583064851855470119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906879444086469140626825 5930159583064851855470119)
          ·
            refine ⟨8895239374597277783205179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930159583064851855470119 8895239374597277783205179)
            ·
              refine ⟨13342859061895916674807769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8895239374597277783205179 13342859061895916674807769)
              ·
                refine ⟨10007144296421937506105827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342859061895916674807769 10007144296421937506105827)
                ·
                  refine ⟨15010716444632906259158741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007144296421937506105827 15010716444632906259158741)
                  ·
                    refine ⟨351813666671083740449033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15010716444632906259158741 351813666671083740449033)
                    ·
                      rfl

theorem cell23_2055464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2055464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055464 prefixEnd_2055464 := by exact prefixLift 2055464
  have htrace : WordTrace (prefixWord ++ tailWord_2055464) baseStart_2055464 baseEnd_2055464 := by
    simpa [prefixWord, tailWord_2055464, baseEnd_2055464] using wordTrace_append hprefix tailTrace_2055464
  have hstable : (prefixWord ++ tailWord_2055464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055464).length < 2 ^ (prefixWord ++ tailWord_2055464).sum := by decide
  have hdescent : baseEnd_2055464 < baseStart_2055464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055484 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2055484 : Nat := 118140960795 + 2055484 * 2 ^ 59
def prefixEnd_2055484 : Nat := 4983230072969 + 3 ^ 40 * 2055484 * 2
def baseEnd_2055484 : Nat := 1055451269626341143097007

theorem tailTrace_2055484 : CollatzResearch.WordTrace tailWord_2055484 prefixEnd_2055484 1055451269626341143097007 := by
  unfold tailWord_2055484
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484830242669995781946753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49979773656893327709262337 37484830242669995781946753)
  ·
    refine ⟨28113622682002496836460065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37484830242669995781946753 28113622682002496836460065)
    ·
      refine ⟨21085217011501872627345049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28113622682002496836460065 21085217011501872627345049)
      ·
        refine ⟨15813912758626404470508787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21085217011501872627345049 15813912758626404470508787)
        ·
          refine ⟨23720869137939606705763181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813912758626404470508787 23720869137939606705763181)
          ·
            refine ⟨8895325926727352514661193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23720869137939606705763181 8895325926727352514661193)
            ·
              refine ⟨6671494445045514385995895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895325926727352514661193 6671494445045514385995895)
              ·
                refine ⟨10007241667568271578993843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671494445045514385995895 10007241667568271578993843)
                ·
                  refine ⟨15010862501352407368490765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007241667568271578993843 15010862501352407368490765)
                  ·
                    refine ⟨5629073438007152763184037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010862501352407368490765 5629073438007152763184037)
                    ·
                      refine ⟨1055451269626341143097007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5629073438007152763184037 1055451269626341143097007)
                      ·
                        rfl

theorem cell23_2055484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2055484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055484 prefixEnd_2055484 := by exact prefixLift 2055484
  have htrace : WordTrace (prefixWord ++ tailWord_2055484) baseStart_2055484 baseEnd_2055484 := by
    simpa [prefixWord, tailWord_2055484, baseEnd_2055484] using wordTrace_append hprefix tailTrace_2055484
  have hstable : (prefixWord ++ tailWord_2055484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055484).length < 2 ^ (prefixWord ++ tailWord_2055484).sum := by decide
  have hdescent : baseEnd_2055484 < baseStart_2055484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055485 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2055485 : Nat := 118140960795 + 2055485 * 2 ^ 59
def prefixEnd_2055485 : Nat := 4983230072969 + 3 ^ 40 * 2055485 * 2
def baseEnd_2055485 : Nat := 117272420345221737687167

theorem tailTrace_2055485 : CollatzResearch.WordTrace tailWord_2055485 prefixEnd_2055485 117272420345221737687167 := by
  unfold tailWord_2055485
  simp only [CollatzResearch.WordTrace]
  refine ⟨74969696958336368734679909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49979797972224245823119939 74969696958336368734679909)
  ·
    refine ⟨14056818179688069137752483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74969696958336368734679909 14056818179688069137752483)
    ·
      refine ⟨21085227269532103706628725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056818179688069137752483 21085227269532103706628725)
      ·
        refine ⟨1976740056518634722496443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21085227269532103706628725 1976740056518634722496443)
        ·
          refine ⟨2965110084777952083744665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976740056518634722496443 2965110084777952083744665)
          ·
            refine ⟨2223832563583464062808499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965110084777952083744665 2223832563583464062808499)
            ·
              refine ⟨3335748845375196094212749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223832563583464062808499 3335748845375196094212749)
              ·
                refine ⟨1250905817015698535329781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3335748845375196094212749 1250905817015698535329781)
                ·
                  refine ⟨117272420345221737687167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1250905817015698535329781 117272420345221737687167)
                  ·
                    rfl

theorem cell23_2055485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2055485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055485 prefixEnd_2055485 := by exact prefixLift 2055485
  have htrace : WordTrace (prefixWord ++ tailWord_2055485) baseStart_2055485 baseEnd_2055485 := by
    simpa [prefixWord, tailWord_2055485, baseEnd_2055485] using wordTrace_append hprefix tailTrace_2055485
  have hstable : (prefixWord ++ tailWord_2055485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055485).length < 2 ^ (prefixWord ++ tailWord_2055485).sum := by decide
  have hdescent : baseEnd_2055485 < baseStart_2055485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055497 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_2055497 : Nat := 118140960795 + 2055497 * 2 ^ 59
def prefixEnd_2055497 : Nat := 4983230072969 + 3 ^ 40 * 2055497 * 2
def baseEnd_2055497 : Nat := 1055457944874849592234447

theorem tailTrace_2055497 : CollatzResearch.WordTrace tailWord_2055497 prefixEnd_2055497 1055457944874849592234447 := by
  unfold tailWord_2055497
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970134634292894784116745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49980089756195263189411163 74970134634292894784116745)
  ·
    refine ⟨56227600975719671088087559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74970134634292894784116745 56227600975719671088087559)
    ·
      refine ⟨84341401463579506632131339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56227600975719671088087559 84341401463579506632131339)
      ·
        refine ⟨126512102195369259948197009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84341401463579506632131339 126512102195369259948197009)
        ·
          refine ⟨94884076646526944961147757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126512102195369259948197009 94884076646526944961147757)
          ·
            refine ⟨35581528742447604360430409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94884076646526944961147757 35581528742447604360430409)
            ·
              refine ⟨26686146556835703270322807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35581528742447604360430409 26686146556835703270322807)
              ·
                refine ⟨40029219835253554905484211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686146556835703270322807 40029219835253554905484211)
                ·
                  refine ⟨60043829752880332358226317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40029219835253554905484211 60043829752880332358226317)
                  ·
                    refine ⟨22516436157330124634334869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60043829752880332358226317 22516436157330124634334869)
                    ·
                      refine ⟨1055457944874849592234447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22516436157330124634334869 1055457944874849592234447)
                      ·
                        rfl

theorem cell23_2055497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_2055497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055497 prefixEnd_2055497 := by exact prefixLift 2055497
  have htrace : WordTrace (prefixWord ++ tailWord_2055497) baseStart_2055497 baseEnd_2055497 := by
    simpa [prefixWord, tailWord_2055497, baseEnd_2055497] using wordTrace_append hprefix tailTrace_2055497
  have hstable : (prefixWord ++ tailWord_2055497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055497).length < 2 ^ (prefixWord ++ tailWord_2055497).sum := by decide
  have hdescent : baseEnd_2055497 < baseStart_2055497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055507 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 8]
def baseStart_2055507 : Nat := 118140960795 + 2055507 * 2 ^ 59
def prefixEnd_2055507 : Nat := 4983230072969 + 3 ^ 40 * 2055507 * 2
def baseEnd_2055507 : Nat := 117273675520154950345489

theorem tailTrace_2055507 : CollatzResearch.WordTrace tailWord_2055507 prefixEnd_2055507 117273675520154950345489 := by
  unfold tailWord_2055507
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970499364256666491980775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49980332909504444327987183 74970499364256666491980775)
  ·
    refine ⟨112455749046384999737971163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74970499364256666491980775 112455749046384999737971163)
    ·
      refine ⟨168683623569577499606956745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112455749046384999737971163 168683623569577499606956745)
      ·
        refine ⟨126512717677183124705217559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168683623569577499606956745 126512717677183124705217559)
        ·
          refine ⟨189769076515774687057826339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126512717677183124705217559 189769076515774687057826339)
          ·
            refine ⟨284653614773662030586739509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189769076515774687057826339 284653614773662030586739509)
            ·
              refine ⟨26686276385030815367506829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284653614773662030586739509 26686276385030815367506829)
              ·
                refine ⟨10007353644386555762815061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26686276385030815367506829 10007353644386555762815061)
                ·
                  refine ⟨117273675520154950345489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10007353644386555762815061 117273675520154950345489)
                  ·
                    rfl

theorem cell23_2055507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 8].length) (baseStart_2055507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055507 prefixEnd_2055507 := by exact prefixLift 2055507
  have htrace : WordTrace (prefixWord ++ tailWord_2055507) baseStart_2055507 baseEnd_2055507 := by
    simpa [prefixWord, tailWord_2055507, baseEnd_2055507] using wordTrace_append hprefix tailTrace_2055507
  have hstable : (prefixWord ++ tailWord_2055507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055507).length < 2 ^ (prefixWord ++ tailWord_2055507).sum := by decide
  have hdescent : baseEnd_2055507 < baseStart_2055507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055511 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 3, 4]
def baseStart_2055511 : Nat := 118140960795 + 2055511 * 2 ^ 59
def prefixEnd_2055511 : Nat := 4983230072969 + 3 ^ 40 * 2055511 * 2
def baseEnd_2055511 : Nat := 351821711201337512486461

theorem tailTrace_2055511 : CollatzResearch.WordTrace tailWord_2055511 prefixEnd_2055511 351821711201337512486461 := by
  unfold tailWord_2055511
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970645256242175175126387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49980430170828116783417591 74970645256242175175126387)
  ·
    refine ⟨112455967884363262762689581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74970645256242175175126387 112455967884363262762689581)
    ·
      refine ⟨42170987956636223536008593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112455967884363262762689581 42170987956636223536008593)
      ·
        refine ⟨31628240967477167652006445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42170987956636223536008593 31628240967477167652006445)
        ·
          refine ⟨11860590362803937869502417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31628240967477167652006445 11860590362803937869502417)
          ·
            refine ⟨8895442772102953402126813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11860590362803937869502417 8895442772102953402126813)
            ·
              refine ⟨3335791039538607525797555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8895442772102953402126813 3335791039538607525797555)
              ·
                refine ⟨5003686559307911288696333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335791039538607525797555 5003686559307911288696333)
                ·
                  refine ⟨1876382459740466733261125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5003686559307911288696333 1876382459740466733261125)
                  ·
                    refine ⟨351821711201337512486461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876382459740466733261125 351821711201337512486461)
                    ·
                      rfl

theorem cell23_2055511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_2055511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055511 prefixEnd_2055511 := by exact prefixLift 2055511
  have htrace : WordTrace (prefixWord ++ tailWord_2055511) baseStart_2055511 baseEnd_2055511 := by
    simpa [prefixWord, tailWord_2055511, baseEnd_2055511] using wordTrace_append hprefix tailTrace_2055511
  have hstable : (prefixWord ++ tailWord_2055511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055511).length < 2 ^ (prefixWord ++ tailWord_2055511).sum := by decide
  have hdescent : baseEnd_2055511 < baseStart_2055511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055591 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2055591 : Nat := 118140960795 + 2055591 * 2 ^ 59
def prefixEnd_2055591 : Nat := 4983230072969 + 3 ^ 40 * 2055591 * 2
def baseEnd_2055591 : Nat := 1055506212056372224459015

theorem tailTrace_2055591 : CollatzResearch.WordTrace tailWord_2055591 prefixEnd_2055591 1055506212056372224459015 := by
  unfold tailWord_2055591
  simp only [CollatzResearch.WordTrace]
  refine ⟨74973563095952348838038627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49982375397301565892025751 74973563095952348838038627)
  ·
    refine ⟨112460344643928523257057941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74973563095952348838038627 112460344643928523257057941)
    ·
      refine ⟨5271578655184149527674591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112460344643928523257057941 5271578655184149527674591)
      ·
        refine ⟨7907367982776224291511887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271578655184149527674591 7907367982776224291511887)
        ·
          refine ⟨11861051974164336437267831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907367982776224291511887 11861051974164336437267831)
          ·
            refine ⟨17791577961246504655901747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861051974164336437267831 17791577961246504655901747)
            ·
              refine ⟨26687366941869756983852621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791577961246504655901747 26687366941869756983852621)
              ·
                refine ⟨10007762603201158868944733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26687366941869756983852621 10007762603201158868944733)
                ·
                  refine ⟨3752910976200434575854275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10007762603201158868944733 3752910976200434575854275)
                  ·
                    refine ⟨5629366464300651863781413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752910976200434575854275 5629366464300651863781413)
                    ·
                      refine ⟨1055506212056372224459015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5629366464300651863781413 1055506212056372224459015)
                      ·
                        rfl

theorem cell23_2055591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2055591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055591 prefixEnd_2055591 := by exact prefixLift 2055591
  have htrace : WordTrace (prefixWord ++ tailWord_2055591) baseStart_2055591 baseEnd_2055591 := by
    simpa [prefixWord, tailWord_2055591, baseEnd_2055591] using wordTrace_append hprefix tailTrace_2055591
  have hstable : (prefixWord ++ tailWord_2055591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055591).length < 2 ^ (prefixWord ++ tailWord_2055591).sum := by decide
  have hdescent : baseEnd_2055591 < baseStart_2055591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055601 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2055601 : Nat := 118140960795 + 2055601 * 2 ^ 59
def prefixEnd_2055601 : Nat := 4983230072969 + 3 ^ 40 * 2055601 * 2
def baseEnd_2055601 : Nat := 351837115620972395111323

theorem tailTrace_2055601 : CollatzResearch.WordTrace tailWord_2055601 prefixEnd_2055601 351837115620972395111323 := by
  unfold tailWord_2055601
  simp only [CollatzResearch.WordTrace]
  refine ⟨74973927825916120545902657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49982618550610747030601771 74973927825916120545902657)
  ·
    refine ⟨56230445869437090409426993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74973927825916120545902657 56230445869437090409426993)
    ·
      refine ⟨42172834402077817807070245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56230445869437090409426993 42172834402077817807070245)
      ·
        refine ⟨7907406450389590838825671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42172834402077817807070245 7907406450389590838825671)
        ·
          refine ⟨11861109675584386258238507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907406450389590838825671 11861109675584386258238507)
          ·
            refine ⟨17791664513376579387357761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861109675584386258238507 17791664513376579387357761)
            ·
              refine ⟨13343748385032434540518321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17791664513376579387357761 13343748385032434540518321)
              ·
                refine ⟨10007811288774325905388741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13343748385032434540518321 10007811288774325905388741)
                ·
                  refine ⟨1876464616645186107260389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10007811288774325905388741 1876464616645186107260389)
                  ·
                    refine ⟨351837115620972395111323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876464616645186107260389 351837115620972395111323)
                    ·
                      rfl

theorem cell23_2055601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2055601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055601 prefixEnd_2055601 := by exact prefixLift 2055601
  have htrace : WordTrace (prefixWord ++ tailWord_2055601) baseStart_2055601 baseEnd_2055601 := by
    simpa [prefixWord, tailWord_2055601, baseEnd_2055601] using wordTrace_append hprefix tailTrace_2055601
  have hstable : (prefixWord ++ tailWord_2055601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055601).length < 2 ^ (prefixWord ++ tailWord_2055601).sum := by decide
  have hdescent : baseEnd_2055601 < baseStart_2055601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055605 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2055605 : Nat := 118140960795 + 2055605 * 2 ^ 59
def prefixEnd_2055605 : Nat := 4983230072969 + 3 ^ 40 * 2055605 * 2
def baseEnd_2055605 : Nat := 351837800261845056561317

theorem tailTrace_2055605 : CollatzResearch.WordTrace tailWord_2055605 prefixEnd_2055605 351837800261845056561317 := by
  unfold tailWord_2055605
  simp only [CollatzResearch.WordTrace]
  refine ⟨74974073717901629229048269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49982715811934419486032179 74974073717901629229048269)
  ·
    refine ⟨28115277644213110960893101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74974073717901629229048269 28115277644213110960893101)
    ·
      refine ⟨10543229116579916610334913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28115277644213110960893101 10543229116579916610334913)
      ·
        refine ⟨7907421837434937457751185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10543229116579916610334913 7907421837434937457751185)
        ·
          refine ⟨5930566378076203093313389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7907421837434937457751185 5930566378076203093313389)
          ·
            refine ⟨2223962391778576159992521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5930566378076203093313389 2223962391778576159992521)
            ·
              refine ⟨1667971793833932119994391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223962391778576159992521 1667971793833932119994391)
              ·
                refine ⟨2501957690750898179991587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667971793833932119994391 2501957690750898179991587)
                ·
                  refine ⟨3752936536126347269987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501957690750898179991587 3752936536126347269987381)
                  ·
                    refine ⟨351837800261845056561317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3752936536126347269987381 351837800261845056561317)
                    ·
                      rfl

theorem cell23_2055605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2055605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055605 prefixEnd_2055605 := by exact prefixLift 2055605
  have htrace : WordTrace (prefixWord ++ tailWord_2055605) baseStart_2055605 baseEnd_2055605 := by
    simpa [prefixWord, tailWord_2055605, baseEnd_2055605] using wordTrace_append hprefix tailTrace_2055605
  have hstable : (prefixWord ++ tailWord_2055605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055605).length < 2 ^ (prefixWord ++ tailWord_2055605).sum := by decide
  have hdescent : baseEnd_2055605 < baseStart_2055605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055608 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_2055608 : Nat := 118140960795 + 2055608 * 2 ^ 59
def prefixEnd_2055608 : Nat := 4983230072969 + 3 ^ 40 * 2055608 * 2
def baseEnd_2055608 : Nat := 1055514941227498657946437

theorem tailTrace_2055608 : CollatzResearch.WordTrace tailWord_2055608 prefixEnd_2055608 1055514941227498657946437 := by
  unfold tailWord_2055608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37487091568445380370703739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49982788757927173827604985 37487091568445380370703739)
  ·
    refine ⟨56230637352668070556055609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37487091568445380370703739 56230637352668070556055609)
    ·
      refine ⟨42172978014501052917041707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56230637352668070556055609 42172978014501052917041707)
      ·
        refine ⟨63259467021751579375562561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42172978014501052917041707 63259467021751579375562561)
        ·
          refine ⟨47444600266313684531671921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63259467021751579375562561 47444600266313684531671921)
          ·
            refine ⟨35583450199735263398753941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47444600266313684531671921 35583450199735263398753941)
            ·
              refine ⟨1667974228112590471816591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35583450199735263398753941 1667974228112590471816591)
              ·
                refine ⟨2501961342168885707724887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667974228112590471816591 2501961342168885707724887)
                ·
                  refine ⟨3752942013253328561587331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501961342168885707724887 3752942013253328561587331)
                  ·
                    refine ⟨5629413019879992842380997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752942013253328561587331 5629413019879992842380997)
                    ·
                      refine ⟨1055514941227498657946437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5629413019879992842380997 1055514941227498657946437)
                      ·
                        rfl

theorem cell23_2055608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_2055608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055608 prefixEnd_2055608 := by exact prefixLift 2055608
  have htrace : WordTrace (prefixWord ++ tailWord_2055608) baseStart_2055608 baseEnd_2055608 := by
    simpa [prefixWord, tailWord_2055608, baseEnd_2055608] using wordTrace_append hprefix tailTrace_2055608
  have hstable : (prefixWord ++ tailWord_2055608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055608).length < 2 ^ (prefixWord ++ tailWord_2055608).sum := by decide
  have hdescent : baseEnd_2055608 < baseStart_2055608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055638 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2055638 : Nat := 118140960795 + 2055638 * 2 ^ 59
def prefixEnd_2055638 : Nat := 4983230072969 + 3 ^ 40 * 2055638 * 2
def baseEnd_2055638 : Nat := 1055530345647133540571299

theorem tailTrace_2055638 : CollatzResearch.WordTrace tailWord_2055638 prefixEnd_2055638 1055530345647133540571299 := by
  unfold tailWord_2055638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685954832923879741562473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49983518217854717243333045 4685954832923879741562473)
  ·
    refine ⟨3514466124692909806171855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4685954832923879741562473 3514466124692909806171855)
    ·
      refine ⟨5271699187039364709257783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514466124692909806171855 5271699187039364709257783)
      ·
        refine ⟨7907548780559047063886675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271699187039364709257783 7907548780559047063886675)
        ·
          refine ⟨11861323170838570595830013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907548780559047063886675 11861323170838570595830013)
          ·
            refine ⟨4447996189064463973436255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11861323170838570595830013 4447996189064463973436255)
            ·
              refine ⟨6671994283596695960154383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4447996189064463973436255 6671994283596695960154383)
              ·
                refine ⟨10007991425395043940231575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671994283596695960154383 10007991425395043940231575)
                ·
                  refine ⟨15011987138092565910347363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007991425395043940231575 15011987138092565910347363)
                  ·
                    refine ⟨22517980707138848865521045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15011987138092565910347363 22517980707138848865521045)
                    ·
                      refine ⟨1055530345647133540571299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22517980707138848865521045 1055530345647133540571299)
                      ·
                        rfl

theorem cell23_2055638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2055638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055638 prefixEnd_2055638 := by exact prefixLift 2055638
  have htrace : WordTrace (prefixWord ++ tailWord_2055638) baseStart_2055638 baseEnd_2055638 := by
    simpa [prefixWord, tailWord_2055638, baseEnd_2055638] using wordTrace_append hprefix tailTrace_2055638
  have hstable : (prefixWord ++ tailWord_2055638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055638).length < 2 ^ (prefixWord ++ tailWord_2055638).sum := by decide
  have hdescent : baseEnd_2055638 < baseStart_2055638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055645 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2055645 : Nat := 118140960795 + 2055645 * 2 ^ 59
def prefixEnd_2055645 : Nat := 4983230072969 + 3 ^ 40 * 2055645 * 2
def baseEnd_2055645 : Nat := 1055533940011715013183767

theorem tailTrace_2055645 : CollatzResearch.WordTrace tailWord_2055645 prefixEnd_2055645 1055533940011715013183767 := by
  unfold tailWord_2055645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74975532637756716060504389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49983688425171144040336259 74975532637756716060504389)
  ·
    refine ⟨14057912369579384261344573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74975532637756716060504389 14057912369579384261344573)
    ·
      refine ⟨5271717138592269098004215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14057912369579384261344573 5271717138592269098004215)
      ·
        refine ⟨7907575707888403647006323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271717138592269098004215 7907575707888403647006323)
        ·
          refine ⟨11861363561832605470509485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907575707888403647006323 11861363561832605470509485)
          ·
            refine ⟨4448011335687227051441057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11861363561832605470509485 4448011335687227051441057)
            ·
              refine ⟨3336008501765420288580793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448011335687227051441057 3336008501765420288580793)
              ·
                refine ⟨2502006376324065216435595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336008501765420288580793 2502006376324065216435595)
                ·
                  refine ⟨3753009564486097824653393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502006376324065216435595 3753009564486097824653393)
                  ·
                    refine ⟨2814757173364573368490045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3753009564486097824653393 2814757173364573368490045)
                    ·
                      refine ⟨1055533940011715013183767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2814757173364573368490045 1055533940011715013183767)
                      ·
                        rfl

theorem cell23_2055645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2055645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055645 prefixEnd_2055645 := by exact prefixLift 2055645
  have htrace : WordTrace (prefixWord ++ tailWord_2055645) baseStart_2055645 baseEnd_2055645 := by
    simpa [prefixWord, tailWord_2055645, baseEnd_2055645] using wordTrace_append hprefix tailTrace_2055645
  have hstable : (prefixWord ++ tailWord_2055645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055645).length < 2 ^ (prefixWord ++ tailWord_2055645).sum := by decide
  have hdescent : baseEnd_2055645 < baseStart_2055645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055701 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2055701 : Nat := 118140960795 + 2055701 * 2 ^ 59
def prefixEnd_2055701 : Nat := 4983230072969 + 3 ^ 40 * 2055701 * 2
def baseEnd_2055701 : Nat := 1055562694928366794083509

theorem tailTrace_2055701 : CollatzResearch.WordTrace tailWord_2055701 prefixEnd_2055701 1055562694928366794083509 := by
  unfold tailWord_2055701
  simp only [CollatzResearch.WordTrace]
  refine ⟨74977575125553837624542957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49985050083702558416361971 74977575125553837624542957)
  ·
    refine ⟨28116590672082689109203609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74977575125553837624542957 28116590672082689109203609)
    ·
      refine ⟨21087443004062016831902707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28116590672082689109203609 21087443004062016831902707)
      ·
        refine ⟨31631164506093025247854061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087443004062016831902707 31631164506093025247854061)
        ·
          refine ⟨11861686689784884467945273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31631164506093025247854061 11861686689784884467945273)
          ·
            refine ⟨8896265017338663350958955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11861686689784884467945273 8896265017338663350958955)
            ·
              refine ⟨13344397526007995026438433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896265017338663350958955 13344397526007995026438433)
              ·
                refine ⟨10008298144505996269828825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344397526007995026438433 10008298144505996269828825)
                ·
                  refine ⟨7506223608379497202371619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008298144505996269828825 7506223608379497202371619)
                  ·
                    refine ⟨11259335412569245803557429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506223608379497202371619 11259335412569245803557429)
                    ·
                      refine ⟨1055562694928366794083509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11259335412569245803557429 1055562694928366794083509)
                      ·
                        rfl

theorem cell23_2055701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2055701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055701 prefixEnd_2055701 := by exact prefixLift 2055701
  have htrace : WordTrace (prefixWord ++ tailWord_2055701) baseStart_2055701 baseEnd_2055701 := by
    simpa [prefixWord, tailWord_2055701, baseEnd_2055701] using wordTrace_append hprefix tailTrace_2055701
  have hstable : (prefixWord ++ tailWord_2055701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055701).length < 2 ^ (prefixWord ++ tailWord_2055701).sum := by decide
  have hdescent : baseEnd_2055701 < baseStart_2055701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055715 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 4, 2]
def baseStart_2055715 : Nat := 118140960795 + 2055715 * 2 ^ 59
def prefixEnd_2055715 : Nat := 4983230072969 + 3 ^ 40 * 2055715 * 2
def baseEnd_2055715 : Nat := 1055569883657529739308445

theorem tailTrace_2055715 : CollatzResearch.WordTrace tailWord_2055715 prefixEnd_2055715 1055569883657529739308445 := by
  unfold tailWord_2055715
  simp only [CollatzResearch.WordTrace]
  refine ⟨74978085747503118015552599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49985390498335412010368399 74978085747503118015552599)
  ·
    refine ⟨112467128621254677023328899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74978085747503118015552599 112467128621254677023328899)
    ·
      refine ⟨168700692931882015534993349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112467128621254677023328899 168700692931882015534993349)
      ·
        refine ⟨31631379924727877912811253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168700692931882015534993349 31631379924727877912811253)
        ·
          refine ⟨2965441867943238554326055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31631379924727877912811253 2965441867943238554326055)
          ·
            refine ⟨4448162801914857831489083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965441867943238554326055 4448162801914857831489083)
            ·
              refine ⟨6672244202872286747233625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448162801914857831489083 6672244202872286747233625)
              ·
                refine ⟨5004183152154215060425219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672244202872286747233625 5004183152154215060425219)
                ·
                  refine ⟨7506274728231322590637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004183152154215060425219 7506274728231322590637829)
                  ·
                    refine ⟨1407426511543372985744593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506274728231322590637829 1407426511543372985744593)
                    ·
                      refine ⟨1055569883657529739308445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407426511543372985744593 1055569883657529739308445)
                      ·
                        rfl

theorem cell23_2055715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_2055715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055715 prefixEnd_2055715 := by exact prefixLift 2055715
  have htrace : WordTrace (prefixWord ++ tailWord_2055715) baseStart_2055715 baseEnd_2055715 := by
    simpa [prefixWord, tailWord_2055715, baseEnd_2055715] using wordTrace_append hprefix tailTrace_2055715
  have hstable : (prefixWord ++ tailWord_2055715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055715).length < 2 ^ (prefixWord ++ tailWord_2055715).sum := by decide
  have hdescent : baseEnd_2055715 < baseStart_2055715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055738 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_2055738 : Nat := 118140960795 + 2055738 * 2 ^ 59
def prefixEnd_2055738 : Nat := 4983230072969 + 3 ^ 40 * 2055738 * 2
def baseEnd_2055738 : Nat := 117286854856953683257871

theorem tailTrace_2055738 : CollatzResearch.WordTrace tailWord_2055738 prefixEnd_2055738 117286854856953683257871 := by
  unfold tailWord_2055738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744731156604948235909967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49985949750946528629093245 18744731156604948235909967)
  ·
    refine ⟨28117096734907422353864951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744731156604948235909967 28117096734907422353864951)
    ·
      refine ⟨42175645102361133530797427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28117096734907422353864951 42175645102361133530797427)
      ·
        refine ⟨63263467653541700296196141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42175645102361133530797427 63263467653541700296196141)
        ·
          refine ⟨23723800370078137611073553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63263467653541700296196141 23723800370078137611073553)
          ·
            refine ⟨17792850277558603208305165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23723800370078137611073553 17792850277558603208305165)
            ·
              refine ⟨6672318854084476203114437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17792850277558603208305165 6672318854084476203114437)
              ·
                refine ⟨1251059785140839288083957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6672318854084476203114437 1251059785140839288083957)
                ·
                  refine ⟨117286854856953683257871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251059785140839288083957 117286854856953683257871)
                  ·
                    rfl

theorem cell23_2055738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_2055738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055738 prefixEnd_2055738 := by exact prefixLift 2055738
  have htrace : WordTrace (prefixWord ++ tailWord_2055738) baseStart_2055738 baseEnd_2055738 := by
    simpa [prefixWord, tailWord_2055738, baseEnd_2055738] using wordTrace_append hprefix tailTrace_2055738
  have hstable : (prefixWord ++ tailWord_2055738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055738).length < 2 ^ (prefixWord ++ tailWord_2055738).sum := by decide
  have hdescent : baseEnd_2055738 < baseStart_2055738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055758 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_2055758 : Nat := 118140960795 + 2055758 * 2 ^ 59
def prefixEnd_2055758 : Nat := 4983230072969 + 3 ^ 40 * 2055758 * 2
def baseEnd_2055758 : Nat := 1055591963325673071070747

theorem tailTrace_2055758 : CollatzResearch.WordTrace tailWord_2055758 prefixEnd_2055758 1055591963325673071070747 := by
  unfold tailWord_2055758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372456760793417044920991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49986436057564890906245285 9372456760793417044920991)
  ·
    refine ⟨14058685141190125567381487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372456760793417044920991 14058685141190125567381487)
    ·
      refine ⟨21088027711785188351072231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058685141190125567381487 21088027711785188351072231)
      ·
        refine ⟨31632041567677782526608347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088027711785188351072231 31632041567677782526608347)
        ·
          refine ⟨47448062351516673789912521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31632041567677782526608347 47448062351516673789912521)
          ·
            refine ⟨35586046763637505342434391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47448062351516673789912521 35586046763637505342434391)
            ·
              refine ⟨53379070145456258013651587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35586046763637505342434391 53379070145456258013651587)
              ·
                refine ⟨80068605218184387020477381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53379070145456258013651587 80068605218184387020477381)
                ·
                  refine ⟨15012863478409572566339509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80068605218184387020477381 15012863478409572566339509)
                  ·
                    refine ⟨1407455951100897428094329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15012863478409572566339509 1407455951100897428094329)
                    ·
                      refine ⟨1055591963325673071070747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407455951100897428094329 1055591963325673071070747)
                      ·
                        rfl

theorem cell23_2055758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_2055758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055758 prefixEnd_2055758 := by exact prefixLift 2055758
  have htrace : WordTrace (prefixWord ++ tailWord_2055758) baseStart_2055758 baseEnd_2055758 := by
    simpa [prefixWord, tailWord_2055758, baseEnd_2055758] using wordTrace_append hprefix tailTrace_2055758
  have hstable : (prefixWord ++ tailWord_2055758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055758).length < 2 ^ (prefixWord ++ tailWord_2055758).sum := by decide
  have hdescent : baseEnd_2055758 < baseStart_2055758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055801 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2055801 : Nat := 118140960795 + 2055801 * 2 ^ 59
def prefixEnd_2055801 : Nat := 4983230072969 + 3 ^ 40 * 2055801 * 2
def baseEnd_2055801 : Nat := 1055614042993816402833049

theorem tailTrace_2055801 : CollatzResearch.WordTrace tailWord_2055801 prefixEnd_2055801 1055614042993816402833049 := by
  unfold tailWord_2055801
  simp only [CollatzResearch.WordTrace]
  refine ⟨74981222425191554703183257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49987481616794369802122171 74981222425191554703183257)
  ·
    refine ⟨56235916818893666027387443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74981222425191554703183257 56235916818893666027387443)
    ·
      refine ⟨84353875228340499041081165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56235916818893666027387443 84353875228340499041081165)
      ·
        refine ⟨31632703210627687140405437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84353875228340499041081165 31632703210627687140405437)
        ·
          refine ⟨11862263703985382677652039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31632703210627687140405437 11862263703985382677652039)
          ·
            refine ⟨17793395555978074016478059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862263703985382677652039 17793395555978074016478059)
            ·
              refine ⟨26690093333967111024717089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17793395555978074016478059 26690093333967111024717089)
              ·
                refine ⟨20017570000475333268537817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26690093333967111024717089 20017570000475333268537817)
                ·
                  refine ⟨15013177500356499951403363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20017570000475333268537817 15013177500356499951403363)
                  ·
                    refine ⟨22519766250534749927105045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15013177500356499951403363 22519766250534749927105045)
                    ·
                      refine ⟨1055614042993816402833049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22519766250534749927105045 1055614042993816402833049)
                      ·
                        rfl

theorem cell23_2055801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2055801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055801 prefixEnd_2055801 := by exact prefixLift 2055801
  have htrace : WordTrace (prefixWord ++ tailWord_2055801) baseStart_2055801 baseEnd_2055801 := by
    simpa [prefixWord, tailWord_2055801, baseEnd_2055801] using wordTrace_append hprefix tailTrace_2055801
  have hstable : (prefixWord ++ tailWord_2055801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055801).length < 2 ^ (prefixWord ++ tailWord_2055801).sum := by decide
  have hdescent : baseEnd_2055801 < baseStart_2055801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055805 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_2055805 : Nat := 118140960795 + 2055805 * 2 ^ 59
def prefixEnd_2055805 : Nat := 4983230072969 + 3 ^ 40 * 2055805 * 2
def baseEnd_2055805 : Nat := 1055616096916434387183031

theorem tailTrace_2055805 : CollatzResearch.WordTrace tailWord_2055805 prefixEnd_2055805 1055616096916434387183031 := by
  unfold tailWord_2055805
  simp only [CollatzResearch.WordTrace]
  refine ⟨74981368317177063386328869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49987578878118042257552579 74981368317177063386328869)
  ·
    refine ⟨14059006559470699384936663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74981368317177063386328869 14059006559470699384936663)
    ·
      refine ⟨21088509839206049077404995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059006559470699384936663 21088509839206049077404995)
      ·
        refine ⟨31632764758809073616107493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088509839206049077404995 31632764758809073616107493)
        ·
          refine ⟨5931143392276701303020155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31632764758809073616107493 5931143392276701303020155)
          ·
            refine ⟨8896715088415051954530233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931143392276701303020155 8896715088415051954530233)
            ·
              refine ⟨6672536316311288965897675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896715088415051954530233 6672536316311288965897675)
              ·
                refine ⟨10008804474466933448846513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672536316311288965897675 10008804474466933448846513)
                ·
                  refine ⟨7506603355850200086634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008804474466933448846513 7506603355850200086634885)
                  ·
                    refine ⟨1407488129221912516244041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7506603355850200086634885 1407488129221912516244041)
                    ·
                      refine ⟨1055616096916434387183031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407488129221912516244041 1055616096916434387183031)
                      ·
                        rfl

theorem cell23_2055805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_2055805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055805 prefixEnd_2055805 := by exact prefixLift 2055805
  have htrace : WordTrace (prefixWord ++ tailWord_2055805) baseStart_2055805 baseEnd_2055805 := by
    simpa [prefixWord, tailWord_2055805, baseEnd_2055805] using wordTrace_append hprefix tailTrace_2055805
  have hstable : (prefixWord ++ tailWord_2055805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055805).length < 2 ^ (prefixWord ++ tailWord_2055805).sum := by decide
  have hdescent : baseEnd_2055805 < baseStart_2055805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055832 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 1, 4]
def baseStart_2055832 : Nat := 118140960795 + 2055832 * 2 ^ 59
def prefixEnd_2055832 : Nat := 4983230072969 + 3 ^ 40 * 2055832 * 2
def baseEnd_2055832 : Nat := 351876653631368593848469

theorem tailTrace_2055832 : CollatzResearch.WordTrace tailWord_2055832 prefixEnd_2055832 351876653631368593848469 := by
  unfold tailWord_2055832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491176544039623498780875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49988235392052831331707833 37491176544039623498780875)
  ·
    refine ⟨56236764816059435248171313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37491176544039623498780875 56236764816059435248171313)
    ·
      refine ⟨42177573612044576436128485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56236764816059435248171313 42177573612044576436128485)
      ·
        refine ⟨7908295052258358081774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42177573612044576436128485 7908295052258358081774091)
        ·
          refine ⟨11862442578387537122661137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908295052258358081774091 11862442578387537122661137)
          ·
            refine ⟨8896831933790652841995853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11862442578387537122661137 8896831933790652841995853)
            ·
              refine ⟨3336311975171494815748445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8896831933790652841995853 3336311975171494815748445)
              ·
                refine ⟨1251116990689310555905667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336311975171494815748445 1251116990689310555905667)
                ·
                  refine ⟨1876675486033965833858501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251116990689310555905667 1876675486033965833858501)
                  ·
                    refine ⟨351876653631368593848469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876675486033965833858501 351876653631368593848469)
                    ·
                      rfl

theorem cell23_2055832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_2055832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055832 prefixEnd_2055832 := by exact prefixLift 2055832
  have htrace : WordTrace (prefixWord ++ tailWord_2055832) baseStart_2055832 baseEnd_2055832 := by
    simpa [prefixWord, tailWord_2055832, baseEnd_2055832] using wordTrace_append hprefix tailTrace_2055832
  have hstable : (prefixWord ++ tailWord_2055832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055832).length < 2 ^ (prefixWord ++ tailWord_2055832).sum := by decide
  have hdescent : baseEnd_2055832 < baseStart_2055832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055862 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2055862 : Nat := 118140960795 + 2055862 * 2 ^ 59
def prefixEnd_2055862 : Nat := 4983230072969 + 3 ^ 40 * 2055862 * 2
def baseEnd_2055862 : Nat := 117293929479304518241141

theorem tailTrace_2055862 : CollatzResearch.WordTrace tailWord_2055862 prefixEnd_2055862 117293929479304518241141 := by
  unfold tailWord_2055862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686465454873160132572115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49988964851980374747435893 4686465454873160132572115)
  ·
    refine ⟨7029698182309740198858173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686465454873160132572115 7029698182309740198858173)
    ·
      refine ⟨2636136818366152574571815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7029698182309740198858173 2636136818366152574571815)
      ·
        refine ⟨3954205227549228861857723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636136818366152574571815 3954205227549228861857723)
        ·
          refine ⟨5931307841323843292786585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954205227549228861857723 5931307841323843292786585)
          ·
            refine ⟨4448480880992882469589939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931307841323843292786585 4448480880992882469589939)
            ·
              refine ⟨6672721321489323704384909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448480880992882469589939 6672721321489323704384909)
              ·
                refine ⟨2502270495558496389144341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6672721321489323704384909 2502270495558496389144341)
                ·
                  refine ⟨117293929479304518241141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2502270495558496389144341 117293929479304518241141)
                  ·
                    rfl

theorem cell23_2055862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2055862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055862 prefixEnd_2055862 := by exact prefixLift 2055862
  have htrace : WordTrace (prefixWord ++ tailWord_2055862) baseStart_2055862 baseEnd_2055862 := by
    simpa [prefixWord, tailWord_2055862, baseEnd_2055862] using wordTrace_append hprefix tailTrace_2055862
  have hstable : (prefixWord ++ tailWord_2055862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055862).length < 2 ^ (prefixWord ++ tailWord_2055862).sum := by decide
  have hdescent : baseEnd_2055862 < baseStart_2055862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055881 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_2055881 : Nat := 118140960795 + 2055881 * 2 ^ 59
def prefixEnd_2055881 : Nat := 4983230072969 + 3 ^ 40 * 2055881 * 2
def baseEnd_2055881 : Nat := 1055655121446176089832681

theorem tailTrace_2055881 : CollatzResearch.WordTrace tailWord_2055881 prefixEnd_2055881 1055655121446176089832681 := by
  unfold tailWord_2055881
  simp only [CollatzResearch.WordTrace]
  refine ⟨74984140264901728366095497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49989426843267818910730331 74984140264901728366095497)
  ·
    refine ⟨56238105198676296274571623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74984140264901728366095497 56238105198676296274571623)
    ·
      refine ⟨84357157798014444411857435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56238105198676296274571623 84357157798014444411857435)
      ·
        refine ⟨126535736697021666617786153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84357157798014444411857435 126535736697021666617786153)
        ·
          refine ⟨94901802522766249963339615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126535736697021666617786153 94901802522766249963339615)
          ·
            refine ⟨142352703784149374945009423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94901802522766249963339615 142352703784149374945009423)
            ·
              refine ⟨213529055676224062417514135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142352703784149374945009423 213529055676224062417514135)
              ·
                refine ⟨320293583514336093626271203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213529055676224062417514135 320293583514336093626271203)
                ·
                  refine ⟨480440375271504140439406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320293583514336093626271203 480440375271504140439406805)
                  ·
                    refine ⟨11260321295425878291548597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 480440375271504140439406805 11260321295425878291548597)
                    ·
                      refine ⟨1055655121446176089832681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11260321295425878291548597 1055655121446176089832681)
                      ·
                        rfl

theorem cell23_2055881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_2055881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055881 prefixEnd_2055881 := by exact prefixLift 2055881
  have htrace : WordTrace (prefixWord ++ tailWord_2055881) baseStart_2055881 baseEnd_2055881 := by
    simpa [prefixWord, tailWord_2055881, baseEnd_2055881] using wordTrace_append hprefix tailTrace_2055881
  have hstable : (prefixWord ++ tailWord_2055881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055881).length < 2 ^ (prefixWord ++ tailWord_2055881).sum := by decide
  have hdescent : baseEnd_2055881 < baseStart_2055881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_2055888 : Nat := 118140960795 + 2055888 * 2 ^ 59
def prefixEnd_2055888 : Nat := 4983230072969 + 3 ^ 40 * 2055888 * 2
def baseEnd_2055888 : Nat := 351886238603585854148383

theorem tailTrace_2055888 : CollatzResearch.WordTrace tailWord_2055888 prefixEnd_2055888 351886238603585854148383 := by
  unfold tailWord_2055888
  simp only [CollatzResearch.WordTrace]
  refine ⟨37492197787938184280800159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49989597050584245707733545 37492197787938184280800159)
  ·
    refine ⟨56238296681907276421200239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37492197787938184280800159 56238296681907276421200239)
    ·
      refine ⟨84357445022860914631800359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56238296681907276421200239 84357445022860914631800359)
      ·
        refine ⟨126536167534291371947700539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84357445022860914631800359 126536167534291371947700539)
        ·
          refine ⟨189804251301437057921550809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126536167534291371947700539 189804251301437057921550809)
          ·
            refine ⟨142353188476077793441163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189804251301437057921550809 142353188476077793441163107)
            ·
              refine ⟨213529782714116690161744661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142353188476077793441163107 213529782714116690161744661)
              ·
                refine ⟨10009208564724219851331781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213529782714116690161744661 10009208564724219851331781)
                ·
                  refine ⟨1876726605885791222124709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10009208564724219851331781 1876726605885791222124709)
                  ·
                    refine ⟨351886238603585854148383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876726605885791222124709 351886238603585854148383)
                    ·
                      rfl

theorem cell23_2055888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_2055888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055888 prefixEnd_2055888 := by exact prefixLift 2055888
  have htrace : WordTrace (prefixWord ++ tailWord_2055888) baseStart_2055888 baseEnd_2055888 := by
    simpa [prefixWord, tailWord_2055888, baseEnd_2055888] using wordTrace_append hprefix tailTrace_2055888
  have hstable : (prefixWord ++ tailWord_2055888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055888).length < 2 ^ (prefixWord ++ tailWord_2055888).sum := by decide
  have hdescent : baseEnd_2055888 < baseStart_2055888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055908 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2055908 : Nat := 118140960795 + 2055908 * 2 ^ 59
def prefixEnd_2055908 : Nat := 4983230072969 + 3 ^ 40 * 2055908 * 2
def baseEnd_2055908 : Nat := 1055668985423847484195057

theorem tailTrace_2055908 : CollatzResearch.WordTrace tailWord_2055908 prefixEnd_2055908 1055668985423847484195057 := by
  unfold tailWord_2055908
  simp only [CollatzResearch.WordTrace]
  refine ⟨37492562517901955988664189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49990083357202607984885585 37492562517901955988664189)
  ·
    refine ⟨14059710944213233495749071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37492562517901955988664189 14059710944213233495749071)
    ·
      refine ⟨21089566416319850243623607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059710944213233495749071 21089566416319850243623607)
      ·
        refine ⟨31634349624479775365435411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089566416319850243623607 31634349624479775365435411)
        ·
          refine ⟨47451524436719663048153117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31634349624479775365435411 47451524436719663048153117)
          ·
            refine ⟨17794321663769873643057419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47451524436719663048153117 17794321663769873643057419)
            ·
              refine ⟨26691482495654810464586129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17794321663769873643057419 26691482495654810464586129)
              ·
                refine ⟨20018611871741107848439597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26691482495654810464586129 20018611871741107848439597)
                ·
                  refine ⟨7506979451902915443164849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20018611871741107848439597 7506979451902915443164849)
                  ·
                    refine ⟨5630234588927186582373637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506979451902915443164849 5630234588927186582373637)
                    ·
                      refine ⟨1055668985423847484195057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5630234588927186582373637 1055668985423847484195057)
                      ·
                        rfl

theorem cell23_2055908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2055908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055908 prefixEnd_2055908 := by exact prefixLift 2055908
  have htrace : WordTrace (prefixWord ++ tailWord_2055908) baseStart_2055908 baseEnd_2055908 := by
    simpa [prefixWord, tailWord_2055908, baseEnd_2055908] using wordTrace_append hprefix tailTrace_2055908
  have hstable : (prefixWord ++ tailWord_2055908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055908).length < 2 ^ (prefixWord ++ tailWord_2055908).sum := by decide
  have hdescent : baseEnd_2055908 < baseStart_2055908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055945 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_2055945 : Nat := 118140960795 + 2055945 * 2 ^ 59
def prefixEnd_2055945 : Nat := 4983230072969 + 3 ^ 40 * 2055945 * 2
def baseEnd_2055945 : Nat := 1055687984208063839432387

theorem tailTrace_2055945 : CollatzResearch.WordTrace tailWord_2055945 prefixEnd_2055945 1055687984208063839432387 := by
  unfold tailWord_2055945
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986474536669867296425289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49990983024446578197616859 74986474536669867296425289)
  ·
    refine ⟨56239855902502400472318967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74986474536669867296425289 56239855902502400472318967)
    ·
      refine ⟨84359783853753600708478451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56239855902502400472318967 84359783853753600708478451)
      ·
        refine ⟨126539675780630401062717677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84359783853753600708478451 126539675780630401062717677)
        ·
          refine ⟨47452378417736400398519129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126539675780630401062717677 47452378417736400398519129)
          ·
            refine ⟨35589283813302300298889347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47452378417736400398519129 35589283813302300298889347)
            ·
              refine ⟨53383925719953450448334021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35589283813302300298889347 53383925719953450448334021)
              ·
                refine ⟨10009486072491271959062629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53383925719953450448334021 10009486072491271959062629)
                ·
                  refine ⟨1876778638592113492324243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10009486072491271959062629 1876778638592113492324243)
                  ·
                    refine ⟨2815167957888170238486365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1876778638592113492324243 2815167957888170238486365)
                    ·
                      refine ⟨1055687984208063839432387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815167957888170238486365 1055687984208063839432387)
                      ·
                        rfl

theorem cell23_2055945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_2055945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055945 prefixEnd_2055945 := by exact prefixLift 2055945
  have htrace : WordTrace (prefixWord ++ tailWord_2055945) baseStart_2055945 baseEnd_2055945 := by
    simpa [prefixWord, tailWord_2055945, baseEnd_2055945] using wordTrace_append hprefix tailTrace_2055945
  have hstable : (prefixWord ++ tailWord_2055945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055945).length < 2 ^ (prefixWord ++ tailWord_2055945).sum := by decide
  have hdescent : baseEnd_2055945 < baseStart_2055945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055946 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_2055946 : Nat := 118140960795 + 2055946 * 2 ^ 59
def prefixEnd_2055946 : Nat := 4983230072969 + 3 ^ 40 * 2055946 * 2
def baseEnd_2055946 : Nat := 1055688497688718335519883

theorem tailTrace_2055946 : CollatzResearch.WordTrace tailWord_2055946 prefixEnd_2055946 1055688497688718335519883 := by
  unfold tailWord_2055946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18746627752416561116802923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49991007339777496311474461 18746627752416561116802923)
  ·
    refine ⟨28119941628624841675204385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18746627752416561116802923 28119941628624841675204385)
    ·
      refine ⟨21089956221468631256403289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28119941628624841675204385 21089956221468631256403289)
      ·
        refine ⟨15817467166101473442302467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21089956221468631256403289 15817467166101473442302467)
        ·
          refine ⟨23726200749152210163453701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15817467166101473442302467 23726200749152210163453701)
          ·
            refine ⟨4448662640466039405647569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23726200749152210163453701 4448662640466039405647569)
            ·
              refine ⟨3336496980349529554235677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448662640466039405647569 3336496980349529554235677)
              ·
                refine ⟨1251186367631073582838379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336496980349529554235677 1251186367631073582838379)
                ·
                  refine ⟨1876779551446610374257569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251186367631073582838379 1876779551446610374257569)
                  ·
                    refine ⟨1407584663584957780693177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876779551446610374257569 1407584663584957780693177)
                    ·
                      refine ⟨1055688497688718335519883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407584663584957780693177 1055688497688718335519883)
                      ·
                        rfl

theorem cell23_2055946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_2055946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055946 prefixEnd_2055946 := by exact prefixLift 2055946
  have htrace : WordTrace (prefixWord ++ tailWord_2055946) baseStart_2055946 baseEnd_2055946 := by
    simpa [prefixWord, tailWord_2055946, baseEnd_2055946] using wordTrace_append hprefix tailTrace_2055946
  have hstable : (prefixWord ++ tailWord_2055946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055946).length < 2 ^ (prefixWord ++ tailWord_2055946).sum := by decide
  have hdescent : baseEnd_2055946 < baseStart_2055946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055955 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 5, 3, 2]
def baseStart_2055955 : Nat := 118140960795 + 2055955 * 2 ^ 59
def prefixEnd_2055955 : Nat := 4983230072969 + 3 ^ 40 * 2055955 * 2
def baseEnd_2055955 : Nat := 1055693119014608800307341

theorem tailTrace_2055955 : CollatzResearch.WordTrace tailWord_2055955 prefixEnd_2055955 1055693119014608800307341 := by
  unfold tailWord_2055955
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986839266633639004289319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49991226177755759336192879 74986839266633639004289319)
  ·
    refine ⟨112480258899950458506433979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74986839266633639004289319 112480258899950458506433979)
    ·
      refine ⟨168720388349925687759650969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112480258899950458506433979 168720388349925687759650969)
      ·
        refine ⟨126540291262444265819738227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168720388349925687759650969 126540291262444265819738227)
        ·
          refine ⟨189810436893666398729607341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126540291262444265819738227 189810436893666398729607341)
          ·
            refine ⟨71178913835124899523602753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189810436893666398729607341 71178913835124899523602753)
            ·
              refine ⟨53384185376343674642702065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71178913835124899523602753 53384185376343674642702065)
              ·
                refine ⟨40038139032257755982026549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53384185376343674642702065 40038139032257755982026549)
                ·
                  refine ⟨3753575534274164623314989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40038139032257755982026549 3753575534274164623314989)
                  ·
                    refine ⟨1407590825352811733743121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3753575534274164623314989 1407590825352811733743121)
                    ·
                      refine ⟨1055693119014608800307341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407590825352811733743121 1055693119014608800307341)
                      ·
                        rfl

theorem cell23_2055955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 3, 2].length) (baseStart_2055955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055955 prefixEnd_2055955 := by exact prefixLift 2055955
  have htrace : WordTrace (prefixWord ++ tailWord_2055955) baseStart_2055955 baseEnd_2055955 := by
    simpa [prefixWord, tailWord_2055955, baseEnd_2055955] using wordTrace_append hprefix tailTrace_2055955
  have hstable : (prefixWord ++ tailWord_2055955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055955).length < 2 ^ (prefixWord ++ tailWord_2055955).sum := by decide
  have hdescent : baseEnd_2055955 < baseStart_2055955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055956 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2055956 : Nat := 118140960795 + 2055956 * 2 ^ 59
def prefixEnd_2055956 : Nat := 4983230072969 + 3 ^ 40 * 2055956 * 2
def baseEnd_2055956 : Nat := 351897877498421098798279

theorem tailTrace_2055956 : CollatzResearch.WordTrace tailWord_2055956 prefixEnd_2055956 351897877498421098798279 := by
  unfold tailWord_2055956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37493437869815008087537861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49991250493086677450050481 37493437869815008087537861)
  ·
    refine ⟨7030019600590314016413349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37493437869815008087537861 7030019600590314016413349)
    ·
      refine ⟨1318128675110683878077503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7030019600590314016413349 1318128675110683878077503)
      ·
        refine ⟨1977193012666025817116255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318128675110683878077503 1977193012666025817116255)
        ·
          refine ⟨2965789518999038725674383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977193012666025817116255 2965789518999038725674383)
          ·
            refine ⟨4448684278498558088511575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965789518999038725674383 4448684278498558088511575)
            ·
              refine ⟨6673026417747837132767363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448684278498558088511575 6673026417747837132767363)
              ·
                refine ⟨10009539626621755699151045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673026417747837132767363 10009539626621755699151045)
                ·
                  refine ⟨1876788679991579193590821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10009539626621755699151045 1876788679991579193590821)
                  ·
                    refine ⟨351897877498421098798279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1876788679991579193590821 351897877498421098798279)
                    ·
                      rfl

theorem cell23_2055956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2055956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055956 prefixEnd_2055956 := by exact prefixLift 2055956
  have htrace : WordTrace (prefixWord ++ tailWord_2055956) baseStart_2055956 baseEnd_2055956 := by
    simpa [prefixWord, tailWord_2055956, baseEnd_2055956] using wordTrace_append hprefix tailTrace_2055956
  have hstable : (prefixWord ++ tailWord_2055956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055956).length < 2 ^ (prefixWord ++ tailWord_2055956).sum := by decide
  have hdescent : baseEnd_2055956 < baseStart_2055956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055962 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2055962 : Nat := 118140960795 + 2055962 * 2 ^ 59
def prefixEnd_2055962 : Nat := 4983230072969 + 3 ^ 40 * 2055962 * 2
def baseEnd_2055962 : Nat := 1055696713379190272919809

theorem tailTrace_2055962 : CollatzResearch.WordTrace tailWord_2055962 prefixEnd_2055962 1055696713379190272919809 := by
  unfold tailWord_2055962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18746773644402069799948535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49991396385072186133196093 18746773644402069799948535)
  ·
    refine ⟨28120160466603104699922803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18746773644402069799948535 28120160466603104699922803)
    ·
      refine ⟨42180240699904657049884205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28120160466603104699922803 42180240699904657049884205)
      ·
        refine ⟨15817590262464246393706577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42180240699904657049884205 15817590262464246393706577)
        ·
          refine ⟨11863192696848184795279933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15817590262464246393706577 11863192696848184795279933)
          ·
            refine ⟨4448697261318069298229975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11863192696848184795279933 4448697261318069298229975)
            ·
              refine ⟨6673045891977103947344963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448697261318069298229975 6673045891977103947344963)
              ·
                refine ⟨10009568837965655921017445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673045891977103947344963 10009568837965655921017445)
                ·
                  refine ⟨1876794157118560485190771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10009568837965655921017445 1876794157118560485190771)
                  ·
                    refine ⟨2815191235677840727786157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1876794157118560485190771 2815191235677840727786157)
                    ·
                      refine ⟨1055696713379190272919809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815191235677840727786157 1055696713379190272919809)
                      ·
                        rfl

theorem cell23_2055962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2055962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2055962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2055962 prefixEnd_2055962 := by exact prefixLift 2055962
  have htrace : WordTrace (prefixWord ++ tailWord_2055962) baseStart_2055962 baseEnd_2055962 := by
    simpa [prefixWord, tailWord_2055962, baseEnd_2055962] using wordTrace_append hprefix tailTrace_2055962
  have hstable : (prefixWord ++ tailWord_2055962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055962).length < 2 ^ (prefixWord ++ tailWord_2055962).sum := by decide
  have hdescent : baseEnd_2055962 < baseStart_2055962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056036 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_2056036 : Nat := 118140960795 + 2056036 * 2 ^ 59
def prefixEnd_2056036 : Nat := 4983230072969 + 3 ^ 40 * 2056036 * 2
def baseEnd_2056036 : Nat := 1055734710947622983394469

theorem tailTrace_2056036 : CollatzResearch.WordTrace tailWord_2056036 prefixEnd_2056036 1055734710947622983394469 := by
  unfold tailWord_2056036
  simp only [CollatzResearch.WordTrace]
  refine ⟨37494896789670094918993981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49993195719560126558658641 37494896789670094918993981)
  ·
    refine ⟨14060586296126285594622743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37494896789670094918993981 14060586296126285594622743)
    ·
      refine ⟨21090879444189428391934115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060586296126285594622743 21090879444189428391934115)
      ·
        refine ⟨31636319166284142587901173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21090879444189428391934115 31636319166284142587901173)
        ·
          refine ⟨2965904921839138367615735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31636319166284142587901173 2965904921839138367615735)
          ·
            refine ⟨4448857382758707551423603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965904921839138367615735 4448857382758707551423603)
            ·
              refine ⟨6673286074138061327135405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448857382758707551423603 6673286074138061327135405)
              ·
                refine ⟨2502482277801772997675777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6673286074138061327135405 2502482277801772997675777)
                ·
                  refine ⟨1876861708351329748256833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2502482277801772997675777 1876861708351329748256833)
                  ·
                    refine ⟨1407646281263497311192625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1876861708351329748256833 1407646281263497311192625)
                    ·
                      refine ⟨1055734710947622983394469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407646281263497311192625 1055734710947622983394469)
                      ·
                        rfl

theorem cell23_2056036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_2056036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056036 prefixEnd_2056036 := by exact prefixLift 2056036
  have htrace : WordTrace (prefixWord ++ tailWord_2056036) baseStart_2056036 baseEnd_2056036 := by
    simpa [prefixWord, tailWord_2056036, baseEnd_2056036] using wordTrace_append hprefix tailTrace_2056036
  have hstable : (prefixWord ++ tailWord_2056036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056036).length < 2 ^ (prefixWord ++ tailWord_2056036).sum := by decide
  have hdescent : baseEnd_2056036 < baseStart_2056036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056048 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_2056048 : Nat := 118140960795 + 2056048 * 2 ^ 59
def prefixEnd_2056048 : Nat := 4983230072969 + 3 ^ 40 * 2056048 * 2
def baseEnd_2056048 : Nat := 1055740872715476936444413

theorem tailTrace_2056048 : CollatzResearch.WordTrace tailWord_2056048 prefixEnd_2056048 1055740872715476936444413 := by
  unfold tailWord_2056048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37495115627648357943712399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49993487503531143924949865 37495115627648357943712399)
  ·
    refine ⟨56242673441472536915568599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37495115627648357943712399 56242673441472536915568599)
    ·
      refine ⟨84364010162208805373352899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56242673441472536915568599 84364010162208805373352899)
      ·
        refine ⟨126546015243313208060029349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84364010162208805373352899 126546015243313208060029349)
        ·
          refine ⟨23727377858121226511255503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126546015243313208060029349 23727377858121226511255503)
          ·
            refine ⟨35591066787181839766883255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23727377858121226511255503 35591066787181839766883255)
            ·
              refine ⟨53386600180772759650324883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35591066787181839766883255 53386600180772759650324883)
              ·
                refine ⟨80079900271159139475487325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53386600180772759650324883 80079900271159139475487325)
                ·
                  refine ⟨30029962601684677303307747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80079900271159139475487325 30029962601684677303307747)
                  ·
                    refine ⟨45044943902527015954961621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30029962601684677303307747 45044943902527015954961621)
                    ·
                      refine ⟨1055740872715476936444413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45044943902527015954961621 1055740872715476936444413)
                      ·
                        rfl

theorem cell23_2056048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_2056048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056048 prefixEnd_2056048 := by exact prefixLift 2056048
  have htrace : WordTrace (prefixWord ++ tailWord_2056048) baseStart_2056048 baseEnd_2056048 := by
    simpa [prefixWord, tailWord_2056048, baseEnd_2056048] using wordTrace_append hprefix tailTrace_2056048
  have hstable : (prefixWord ++ tailWord_2056048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056048).length < 2 ^ (prefixWord ++ tailWord_2056048).sum := by decide
  have hdescent : baseEnd_2056048 < baseStart_2056048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056082 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2056082 : Nat := 118140960795 + 2056082 * 2 ^ 59
def prefixEnd_2056082 : Nat := 4983230072969 + 3 ^ 40 * 2056082 * 2
def baseEnd_2056082 : Nat := 1055758331057729803419257

theorem tailTrace_2056082 : CollatzResearch.WordTrace tailWord_2056082 prefixEnd_2056082 1055758331057729803419257 := by
  unfold tailWord_2056082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747867834293384923540625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49994314224782359796108333 18747867834293384923540625)
  ·
    refine ⟨14060900875720038692655469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18747867834293384923540625 14060900875720038692655469)
    ·
      refine ⟨5272837828395014509745801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14060900875720038692655469 5272837828395014509745801)
      ·
        refine ⟨3954628371296260882309351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272837828395014509745801 3954628371296260882309351)
        ·
          refine ⟨5931942556944391323464027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954628371296260882309351 5931942556944391323464027)
          ·
            refine ⟨8897913835416586985196041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931942556944391323464027 8897913835416586985196041)
            ·
              refine ⟨6673435376562440238897031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897913835416586985196041 6673435376562440238897031)
              ·
                refine ⟨10010153064843660358345547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673435376562440238897031 10010153064843660358345547)
                ·
                  refine ⟨15015229597265490537518321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010153064843660358345547 15015229597265490537518321)
                  ·
                    refine ⟨11261422197949117903138741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15015229597265490537518321 11261422197949117903138741)
                    ·
                      refine ⟨1055758331057729803419257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11261422197949117903138741 1055758331057729803419257)
                      ·
                        rfl

theorem cell23_2056082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2056082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056082 prefixEnd_2056082 := by exact prefixLift 2056082
  have htrace : WordTrace (prefixWord ++ tailWord_2056082) baseStart_2056082 baseEnd_2056082 := by
    simpa [prefixWord, tailWord_2056082, baseEnd_2056082] using wordTrace_append hprefix tailTrace_2056082
  have hstable : (prefixWord ++ tailWord_2056082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056082).length < 2 ^ (prefixWord ++ tailWord_2056082).sum := by decide
  have hdescent : baseEnd_2056082 < baseStart_2056082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056145 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2056145 : Nat := 118140960795 + 2056145 * 2 ^ 59
def prefixEnd_2056145 : Nat := 4983230072969 + 3 ^ 40 * 2056145 * 2
def baseEnd_2056145 : Nat := 351930226779654352310489

theorem tailTrace_2056145 : CollatzResearch.WordTrace tailWord_2056145 prefixEnd_2056145 351930226779654352310489 := by
  unfold tailWord_2056145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74993769135945301453705889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49995846090630200969137259 74993769135945301453705889)
  ·
    refine ⟨56245326851958976090279417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74993769135945301453705889 56245326851958976090279417)
    ·
      refine ⟨42183995138969232067709563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56245326851958976090279417 42183995138969232067709563)
      ·
        refine ⟨63275992708453848101564345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42183995138969232067709563 63275992708453848101564345)
        ·
          refine ⟨47456994531340386076173259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63275992708453848101564345 47456994531340386076173259)
          ·
            refine ⟨71185491797010579114259889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47456994531340386076173259 71185491797010579114259889)
            ·
              refine ⟨53389118847757934335694917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71185491797010579114259889 53389118847757934335694917)
              ·
                refine ⟨10010459783954612687942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53389118847757934335694917 10010459783954612687942797)
                ·
                  refine ⟨3753922418982979757978549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10010459783954612687942797 3753922418982979757978549)
                  ·
                    refine ⟨351930226779654352310489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3753922418982979757978549 351930226779654352310489)
                    ·
                      rfl

theorem cell23_2056145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2056145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056145 prefixEnd_2056145 := by exact prefixLift 2056145
  have htrace : WordTrace (prefixWord ++ tailWord_2056145) baseStart_2056145 baseEnd_2056145 := by
    simpa [prefixWord, tailWord_2056145, baseEnd_2056145] using wordTrace_append hprefix tailTrace_2056145
  have hstable : (prefixWord ++ tailWord_2056145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056145).length < 2 ^ (prefixWord ++ tailWord_2056145).sum := by decide
  have hdescent : baseEnd_2056145 < baseStart_2056145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056149 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 6]
def baseStart_2056149 : Nat := 118140960795 + 2056149 * 2 ^ 59
def prefixEnd_2056149 : Nat := 4983230072969 + 3 ^ 40 * 2056149 * 2
def baseEnd_2056149 : Nat := 117310303806842337920161

theorem tailTrace_2056149 : CollatzResearch.WordTrace tailWord_2056149 prefixEnd_2056149 117310303806842337920161 := by
  unfold tailWord_2056149
  simp only [CollatzResearch.WordTrace]
  refine ⟨74993915027930810136851501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49995943351953873424567667 74993915027930810136851501)
  ·
    refine ⟨28122718135474053801319313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74993915027930810136851501 28122718135474053801319313)
    ·
      refine ⟨21092038601605540350989485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28122718135474053801319313 21092038601605540350989485)
      ·
        refine ⟨7909514475602077631621057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21092038601605540350989485 7909514475602077631621057)
        ·
          refine ⟨5932135856701558223715793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909514475602077631621057 5932135856701558223715793)
          ·
            refine ⟨4449101892526168667786845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932135856701558223715793 4449101892526168667786845)
            ·
              refine ⟨1668413209697313250420067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4449101892526168667786845 1668413209697313250420067)
              ·
                refine ⟨2502619814545969875630101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668413209697313250420067 2502619814545969875630101)
                ·
                  refine ⟨117310303806842337920161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2502619814545969875630101 117310303806842337920161)
                  ·
                    rfl

theorem cell23_2056149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_2056149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056149 prefixEnd_2056149 := by exact prefixLift 2056149
  have htrace : WordTrace (prefixWord ++ tailWord_2056149) baseStart_2056149 baseEnd_2056149 := by
    simpa [prefixWord, tailWord_2056149, baseEnd_2056149] using wordTrace_append hprefix tailTrace_2056149
  have hstable : (prefixWord ++ tailWord_2056149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056149).length < 2 ^ (prefixWord ++ tailWord_2056149).sum := by decide
  have hdescent : baseEnd_2056149 < baseStart_2056149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056152 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_2056152 : Nat := 118140960795 + 2056152 * 2 ^ 59
def prefixEnd_2056152 : Nat := 4983230072969 + 3 ^ 40 * 2056152 * 2
def baseEnd_2056152 : Nat := 1055794274703544529543935

theorem tailTrace_2056152 : CollatzResearch.WordTrace tailWord_2056152 prefixEnd_2056152 1055794274703544529543935 := by
  unfold tailWord_2056152
  simp only [CollatzResearch.WordTrace]
  refine ⟨37497012223459970824605355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49996016297946627766140473 37497012223459970824605355)
  ·
    refine ⟨56245518335189956236908033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37497012223459970824605355 56245518335189956236908033)
    ·
      refine ⟨42184138751392467177681025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56245518335189956236908033 42184138751392467177681025)
      ·
        refine ⟨31638104063544350383260769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42184138751392467177681025 31638104063544350383260769)
        ·
          refine ⟨23728578047658262787445577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31638104063544350383260769 23728578047658262787445577)
          ·
            refine ⟨17796433535743697090584183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23728578047658262787445577 17796433535743697090584183)
            ·
              refine ⟨26694650303615545635876275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17796433535743697090584183 26694650303615545635876275)
              ·
                refine ⟨40041975455423318453814413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26694650303615545635876275 40041975455423318453814413)
                ·
                  refine ⟨15015740795783744420180405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40041975455423318453814413 15015740795783744420180405)
                  ·
                    refine ⟨1407725699604726039391913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15015740795783744420180405 1407725699604726039391913)
                    ·
                      refine ⟨1055794274703544529543935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407725699604726039391913 1055794274703544529543935)
                      ·
                        rfl

theorem cell23_2056152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_2056152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056152 prefixEnd_2056152 := by exact prefixLift 2056152
  have htrace : WordTrace (prefixWord ++ tailWord_2056152) baseStart_2056152 baseEnd_2056152 := by
    simpa [prefixWord, tailWord_2056152, baseEnd_2056152] using wordTrace_append hprefix tailTrace_2056152
  have hstable : (prefixWord ++ tailWord_2056152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056152).length < 2 ^ (prefixWord ++ tailWord_2056152).sum := by decide
  have hdescent : baseEnd_2056152 < baseStart_2056152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056159 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2056159 : Nat := 118140960795 + 2056159 * 2 ^ 59
def prefixEnd_2056159 : Nat := 4983230072969 + 3 ^ 40 * 2056159 * 2
def baseEnd_2056159 : Nat := 1055797869068126002156403

theorem tailTrace_2056159 : CollatzResearch.WordTrace tailWord_2056159 prefixEnd_2056159 1055797869068126002156403 := by
  unfold tailWord_2056159
  simp only [CollatzResearch.WordTrace]
  refine ⟨74994279757894581844715531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49996186505263054563143687 74994279757894581844715531)
  ·
    refine ⟨112491419636841872767073297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74994279757894581844715531 112491419636841872767073297)
    ·
      refine ⟨84368564727631404575304973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112491419636841872767073297 84368564727631404575304973)
      ·
        refine ⟨31638211772861776715739365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84368564727631404575304973 31638211772861776715739365)
        ·
          refine ⟨5932164707411583134201131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31638211772861776715739365 5932164707411583134201131)
          ·
            refine ⟨8898247061117374701301697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932164707411583134201131 8898247061117374701301697)
            ·
              refine ⟨6673685295838031025976273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898247061117374701301697 6673685295838031025976273)
              ·
                refine ⟨5005263971878523269482205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673685295838031025976273 5005263971878523269482205)
                ·
                  refine ⟨1876973989454446226055827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5005263971878523269482205 1876973989454446226055827)
                  ·
                    refine ⟨2815460984181669339083741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1876973989454446226055827 2815460984181669339083741)
                    ·
                      refine ⟨1055797869068126002156403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815460984181669339083741 1055797869068126002156403)
                      ·
                        rfl

theorem cell23_2056159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2056159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056159 prefixEnd_2056159 := by exact prefixLift 2056159
  have htrace : WordTrace (prefixWord ++ tailWord_2056159) baseStart_2056159 baseEnd_2056159 := by
    simpa [prefixWord, tailWord_2056159, baseEnd_2056159] using wordTrace_append hprefix tailTrace_2056159
  have hstable : (prefixWord ++ tailWord_2056159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056159).length < 2 ^ (prefixWord ++ tailWord_2056159).sum := by decide
  have hdescent : baseEnd_2056159 < baseStart_2056159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056175 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 3, 6]
def baseStart_2056175 : Nat := 118140960795 + 2056175 * 2 ^ 59
def prefixEnd_2056175 : Nat := 4983230072969 + 3 ^ 40 * 2056175 * 2
def baseEnd_2056175 : Nat := 351935361586199313185443

theorem tailTrace_2056175 : CollatzResearch.WordTrace tailWord_2056175 prefixEnd_2056175 351935361586199313185443 := by
  unfold tailWord_2056175
  simp only [CollatzResearch.WordTrace]
  refine ⟨74994863325836616577297979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49996575550557744384865319 74994863325836616577297979)
  ·
    refine ⟨112492294988754924865946969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74994863325836616577297979 112492294988754924865946969)
    ·
      refine ⟨84369221241566193649460227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112492294988754924865946969 84369221241566193649460227)
      ·
        refine ⟨126553831862349290474190341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84369221241566193649460227 126553831862349290474190341)
        ·
          refine ⟨23728843474190491963910689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126553831862349290474190341 23728843474190491963910689)
          ·
            refine ⟨17796632605642868972933017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23728843474190491963910689 17796632605642868972933017)
            ·
              refine ⟨13347474454232151729699763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17796632605642868972933017 13347474454232151729699763)
              ·
                refine ⟨20021211681348227594549645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347474454232151729699763 20021211681348227594549645)
                ·
                  refine ⟨7507954380505585347956117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20021211681348227594549645 7507954380505585347956117)
                  ·
                    refine ⟨351935361586199313185443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7507954380505585347956117 351935361586199313185443)
                    ·
                      rfl

theorem cell23_2056175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_2056175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056175 prefixEnd_2056175 := by exact prefixLift 2056175
  have htrace : WordTrace (prefixWord ++ tailWord_2056175) baseStart_2056175 baseEnd_2056175 := by
    simpa [prefixWord, tailWord_2056175, baseEnd_2056175] using wordTrace_append hprefix tailTrace_2056175
  have hstable : (prefixWord ++ tailWord_2056175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056175).length < 2 ^ (prefixWord ++ tailWord_2056175).sum := by decide
  have hdescent : baseEnd_2056175 < baseStart_2056175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056176 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 1, 1, 3]
def baseStart_2056176 : Nat := 118140960795 + 2056176 * 2 ^ 59
def prefixEnd_2056176 : Nat := 4983230072969 + 3 ^ 40 * 2056176 * 2
def baseEnd_2056176 : Nat := 1055806598239252435643825

theorem tailTrace_2056176 : CollatzResearch.WordTrace tailWord_2056176 prefixEnd_2056176 1055806598239252435643825 := by
  unfold tailWord_2056176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37497449899416496874042191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49996599865888662498722921 37497449899416496874042191)
  ·
    refine ⟨56246174849124745311063287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37497449899416496874042191 56246174849124745311063287)
    ·
      refine ⟨84369262273687117966594931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246174849124745311063287 84369262273687117966594931)
      ·
        refine ⟨126553893410530676949892397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84369262273687117966594931 126553893410530676949892397)
        ·
          refine ⟨47457710028949003856209649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126553893410530676949892397 47457710028949003856209649)
          ·
            refine ⟨35593282521711752892157237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47457710028949003856209649 35593282521711752892157237)
            ·
              refine ⟨3336870236410476833639741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35593282521711752892157237 3336870236410476833639741)
              ·
                refine ⟨1251326338653928812614903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336870236410476833639741 1251326338653928812614903)
                ·
                  refine ⟨1876989507980893218922355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251326338653928812614903 1876989507980893218922355)
                  ·
                    refine ⟨2815484261971339828383533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1876989507980893218922355 2815484261971339828383533)
                    ·
                      refine ⟨1055806598239252435643825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815484261971339828383533 1055806598239252435643825)
                      ·
                        rfl

theorem cell23_2056176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 1, 3].length) (baseStart_2056176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056176 prefixEnd_2056176 := by exact prefixLift 2056176
  have htrace : WordTrace (prefixWord ++ tailWord_2056176) baseStart_2056176 baseEnd_2056176 := by
    simpa [prefixWord, tailWord_2056176, baseEnd_2056176] using wordTrace_append hprefix tailTrace_2056176
  have hstable : (prefixWord ++ tailWord_2056176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056176).length < 2 ^ (prefixWord ++ tailWord_2056176).sum := by decide
  have hdescent : baseEnd_2056176 < baseStart_2056176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056193 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_2056193 : Nat := 118140960795 + 2056193 * 2 ^ 59
def prefixEnd_2056193 : Nat := 4983230072969 + 3 ^ 40 * 2056193 * 2
def baseEnd_2056193 : Nat := 1055815327410378869131247

theorem tailTrace_2056193 : CollatzResearch.WordTrace tailWord_2056193 prefixEnd_2056193 1055815327410378869131247 := by
  unfold tailWord_2056193
  simp only [CollatzResearch.WordTrace]
  refine ⟨74995519839771405651453233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49997013226514270434302155 74995519839771405651453233)
  ·
    refine ⟨56246639879828554238589925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74995519839771405651453233 56246639879828554238589925)
    ·
      refine ⟨10546244977467853919735611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56246639879828554238589925 10546244977467853919735611)
      ·
        refine ⟨15819367466201780879603417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10546244977467853919735611 15819367466201780879603417)
        ·
          refine ⟨11864525599651335659702563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15819367466201780879603417 11864525599651335659702563)
          ·
            refine ⟨17796788399477003489553845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864525599651335659702563 17796788399477003489553845)
            ·
              refine ⟨1668448912450969077145673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17796788399477003489553845 1668448912450969077145673)
              ·
                refine ⟨1251336684338226807859255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668448912450969077145673 1251336684338226807859255)
                ·
                  refine ⟨1877005026507340211788883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251336684338226807859255 1877005026507340211788883)
                  ·
                    refine ⟨2815507539761010317683325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877005026507340211788883 2815507539761010317683325)
                    ·
                      refine ⟨1055815327410378869131247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815507539761010317683325 1055815327410378869131247)
                      ·
                        rfl

theorem cell23_2056193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_2056193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056193 prefixEnd_2056193 := by exact prefixLift 2056193
  have htrace : WordTrace (prefixWord ++ tailWord_2056193) baseStart_2056193 baseEnd_2056193 := by
    simpa [prefixWord, tailWord_2056193, baseEnd_2056193] using wordTrace_append hprefix tailTrace_2056193
  have hstable : (prefixWord ++ tailWord_2056193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056193).length < 2 ^ (prefixWord ++ tailWord_2056193).sum := by decide
  have hdescent : baseEnd_2056193 < baseStart_2056193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056244 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_2056244 : Nat := 118140960795 + 2056244 * 2 ^ 59
def prefixEnd_2056244 : Nat := 4983230072969 + 3 ^ 40 * 2056244 * 2
def baseEnd_2056244 : Nat := 1055841514923758169593513

theorem tailTrace_2056244 : CollatzResearch.WordTrace tailWord_2056244 prefixEnd_2056244 1055841514923758169593513 := by
  unfold tailWord_2056244
  simp only [CollatzResearch.WordTrace]
  refine ⟨37498689981293320680779893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49998253308391094241039857 37498689981293320680779893)
  ·
    refine ⟨3515502185746248813823115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37498689981293320680779893 3515502185746248813823115)
    ·
      refine ⟨5273253278619373220734673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515502185746248813823115 5273253278619373220734673)
      ·
        refine ⟨3954939958964529915551005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5273253278619373220734673 3954939958964529915551005)
        ·
          refine ⟨1483102484611698718331627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3954939958964529915551005 1483102484611698718331627)
          ·
            refine ⟨2224653726917548077497441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483102484611698718331627 2224653726917548077497441)
            ·
              refine ⟨1668490295188161058123081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224653726917548077497441 1668490295188161058123081)
              ·
                refine ⟨1251367721391120793592311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668490295188161058123081 1251367721391120793592311)
                ·
                  refine ⟨1877051582086681190388467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251367721391120793592311 1877051582086681190388467)
                  ·
                    refine ⟨2815577373130021785582701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877051582086681190388467 2815577373130021785582701)
                    ·
                      refine ⟨1055841514923758169593513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815577373130021785582701 1055841514923758169593513)
                      ·
                        rfl

theorem cell23_2056244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_2056244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056244 prefixEnd_2056244 := by exact prefixLift 2056244
  have htrace : WordTrace (prefixWord ++ tailWord_2056244) baseStart_2056244 baseEnd_2056244 := by
    simpa [prefixWord, tailWord_2056244, baseEnd_2056244] using wordTrace_append hprefix tailTrace_2056244
  have hstable : (prefixWord ++ tailWord_2056244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056244).length < 2 ^ (prefixWord ++ tailWord_2056244).sum := by decide
  have hdescent : baseEnd_2056244 < baseStart_2056244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056276 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_2056276 : Nat := 118140960795 + 2056276 * 2 ^ 59
def prefixEnd_2056276 : Nat := 4983230072969 + 3 ^ 40 * 2056276 * 2
def baseEnd_2056276 : Nat := 1055857946304702044393365

theorem tailTrace_2056276 : CollatzResearch.WordTrace tailWord_2056276 prefixEnd_2056276 1055857946304702044393365 := by
  unfold tailWord_2056276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37499273549235355413362341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49999031398980473884483121 37499273549235355413362341)
  ·
    refine ⟨7031113790481629140005439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37499273549235355413362341 7031113790481629140005439)
    ·
      refine ⟨10546670685722443710008159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031113790481629140005439 10546670685722443710008159)
      ·
        refine ⟨15820006028583665565012239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10546670685722443710008159 15820006028583665565012239)
        ·
          refine ⟨23730009042875498347518359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820006028583665565012239 23730009042875498347518359)
          ·
            refine ⟨35595013564313247521277539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730009042875498347518359 35595013564313247521277539)
            ·
              refine ⟨53392520346469871281916309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35595013564313247521277539 53392520346469871281916309)
              ·
                refine ⟨2502774391240775216339827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53392520346469871281916309 2502774391240775216339827)
                ·
                  refine ⟨3754161586861162824509741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502774391240775216339827 3754161586861162824509741)
                  ·
                    refine ⟨1407810595072936059191153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754161586861162824509741 1407810595072936059191153)
                    ·
                      refine ⟨1055857946304702044393365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407810595072936059191153 1055857946304702044393365)
                      ·
                        rfl

theorem cell23_2056276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_2056276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056276 prefixEnd_2056276 := by exact prefixLift 2056276
  have htrace : WordTrace (prefixWord ++ tailWord_2056276) baseStart_2056276 baseEnd_2056276 := by
    simpa [prefixWord, tailWord_2056276, baseEnd_2056276] using wordTrace_append hprefix tailTrace_2056276
  have hstable : (prefixWord ++ tailWord_2056276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056276).length < 2 ^ (prefixWord ++ tailWord_2056276).sum := by decide
  have hdescent : baseEnd_2056276 < baseStart_2056276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056292 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2056292 : Nat := 118140960795 + 2056292 * 2 ^ 59
def prefixEnd_2056292 : Nat := 4983230072969 + 3 ^ 40 * 2056292 * 2
def baseEnd_2056292 : Nat := 1055866161995173981793291

theorem tailTrace_2056292 : CollatzResearch.WordTrace tailWord_2056292 prefixEnd_2056292 1055866161995173981793291 := by
  unfold tailWord_2056292
  simp only [CollatzResearch.WordTrace]
  refine ⟨37499565333206372779653565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49999420444275163706204753 37499565333206372779653565)
  ·
    refine ⟨14062336999952389792370087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37499565333206372779653565 14062336999952389792370087)
    ·
      refine ⟨21093505499928584688555131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062336999952389792370087 21093505499928584688555131)
      ·
        refine ⟨31640258249892877032832697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21093505499928584688555131 31640258249892877032832697)
        ·
          refine ⟨23730193687419657774624523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31640258249892877032832697 23730193687419657774624523)
          ·
            refine ⟨35595290531129486661936785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730193687419657774624523 35595290531129486661936785)
            ·
              refine ⟨26696467898347114996452589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35595290531129486661936785 26696467898347114996452589)
              ·
                refine ⟨10011175461880168123669721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26696467898347114996452589 10011175461880168123669721)
                ·
                  refine ⟨7508381596410126092752291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011175461880168123669721 7508381596410126092752291)
                  ·
                    refine ⟨11262572394615189139128437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508381596410126092752291 11262572394615189139128437)
                    ·
                      refine ⟨1055866161995173981793291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11262572394615189139128437 1055866161995173981793291)
                      ·
                        rfl

theorem cell23_2056292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2056292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056292 prefixEnd_2056292 := by exact prefixLift 2056292
  have htrace : WordTrace (prefixWord ++ tailWord_2056292) baseStart_2056292 baseEnd_2056292 := by
    simpa [prefixWord, tailWord_2056292, baseEnd_2056292] using wordTrace_append hprefix tailTrace_2056292
  have hstable : (prefixWord ++ tailWord_2056292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056292).length < 2 ^ (prefixWord ++ tailWord_2056292).sum := by decide
  have hdescent : baseEnd_2056292 < baseStart_2056292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056293 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_2056293 : Nat := 118140960795 + 2056293 * 2 ^ 59
def prefixEnd_2056293 : Nat := 4983230072969 + 3 ^ 40 * 2056293 * 2
def baseEnd_2056293 : Nat := 1055866675475828477880787

theorem tailTrace_2056293 : CollatzResearch.WordTrace tailWord_2056293 prefixEnd_2056293 1055866675475828477880787 := by
  unfold tailWord_2056293
  simp only [CollatzResearch.WordTrace]
  refine ⟨74999167139409122730093533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49999444759606081820062355 74999167139409122730093533)
  ·
    refine ⟨28124687677278421023785075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74999167139409122730093533 28124687677278421023785075)
    ·
      refine ⟨42187031515917631535677613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28124687677278421023785075 42187031515917631535677613)
      ·
        refine ⟨15820136818469111825879105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42187031515917631535677613 15820136818469111825879105)
        ·
          refine ⟨11865102613851833869409329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15820136818469111825879105 11865102613851833869409329)
          ·
            refine ⟨8898826960388875402056997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11865102613851833869409329 8898826960388875402056997)
            ·
              refine ⟨1668530055072914137885687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8898826960388875402056997 1668530055072914137885687)
              ·
                refine ⟨2502795082609371206828531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668530055072914137885687 2502795082609371206828531)
                ·
                  refine ⟨3754192623914056810242797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502795082609371206828531 3754192623914056810242797)
                  ·
                    refine ⟨1407822233967771303841049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3754192623914056810242797 1407822233967771303841049)
                    ·
                      refine ⟨1055866675475828477880787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407822233967771303841049 1055866675475828477880787)
                      ·
                        rfl

theorem cell23_2056293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_2056293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056293 prefixEnd_2056293 := by exact prefixLift 2056293
  have htrace : WordTrace (prefixWord ++ tailWord_2056293) baseStart_2056293 baseEnd_2056293 := by
    simpa [prefixWord, tailWord_2056293, baseEnd_2056293] using wordTrace_append hprefix tailTrace_2056293
  have hstable : (prefixWord ++ tailWord_2056293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056293).length < 2 ^ (prefixWord ++ tailWord_2056293).sum := by decide
  have hdescent : baseEnd_2056293 < baseStart_2056293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056379 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 6, 2]
def baseStart_2056379 : Nat := 118140960795 + 2056379 * 2 ^ 59
def prefixEnd_2056379 : Nat := 4983230072969 + 3 ^ 40 * 2056379 * 2
def baseEnd_2056379 : Nat := 1055910834812115141405391

theorem tailTrace_2056379 : CollatzResearch.WordTrace tailWord_2056379 prefixEnd_2056379 1055910834812115141405391 := by
  unfold tailWord_2056379
  simp only [CollatzResearch.WordTrace]
  refine ⟨75002303817097559417724191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50001535878065039611816127 75002303817097559417724191)
  ·
    refine ⟨112503455725646339126586287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75002303817097559417724191 112503455725646339126586287)
    ·
      refine ⟨168755183588469508689879431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112503455725646339126586287 168755183588469508689879431)
      ·
        refine ⟨253132775382704263034819147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168755183588469508689879431 253132775382704263034819147)
        ·
          refine ⟨379699163074056394552228721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253132775382704263034819147 379699163074056394552228721)
          ·
            refine ⟨284774372305542295914171541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379699163074056394552228721 284774372305542295914171541)
            ·
              refine ⟨13348798701822295120976791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284774372305542295914171541 13348798701822295120976791)
              ·
                refine ⟨20023198052733442681465187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13348798701822295120976791 20023198052733442681465187)
                ·
                  refine ⟨30034797079100164022197781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20023198052733442681465187 30034797079100164022197781)
                  ·
                    refine ⟨1407881113082820188540521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30034797079100164022197781 1407881113082820188540521)
                    ·
                      refine ⟨1055910834812115141405391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1407881113082820188540521 1055910834812115141405391)
                      ·
                        rfl

theorem cell23_2056379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 6, 2].length) (baseStart_2056379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056379 prefixEnd_2056379 := by exact prefixLift 2056379
  have htrace : WordTrace (prefixWord ++ tailWord_2056379) baseStart_2056379 baseEnd_2056379 := by
    simpa [prefixWord, tailWord_2056379, baseEnd_2056379] using wordTrace_append hprefix tailTrace_2056379
  have hstable : (prefixWord ++ tailWord_2056379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056379).length < 2 ^ (prefixWord ++ tailWord_2056379).sum := by decide
  have hdescent : baseEnd_2056379 < baseStart_2056379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056389 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_2056389 : Nat := 118140960795 + 2056389 * 2 ^ 59
def prefixEnd_2056389 : Nat := 4983230072969 + 3 ^ 40 * 2056389 * 2
def baseEnd_2056389 : Nat := 351971989872886700760115

theorem tailTrace_2056389 : CollatzResearch.WordTrace tailWord_2056389 prefixEnd_2056389 351971989872886700760115 := by
  unfold tailWord_2056389
  simp only [CollatzResearch.WordTrace]
  refine ⟨75002668547061331125588221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50001779031374220750392147 75002668547061331125588221)
  ·
    refine ⟨28126000705147999172095583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75002668547061331125588221 28126000705147999172095583)
    ·
      refine ⟨42189001057721998758143375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28126000705147999172095583 42189001057721998758143375)
      ·
        refine ⟨63283501586582998137215063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42189001057721998758143375 63283501586582998137215063)
        ·
          refine ⟨94925252379874497205822595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63283501586582998137215063 94925252379874497205822595)
          ·
            refine ⟨142387878569811745808733893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94925252379874497205822595 142387878569811745808733893)
            ·
              refine ⟨26697727231839702339137605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142387878569811745808733893 26697727231839702339137605)
              ·
                refine ⟨5005823855969944188588301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26697727231839702339137605 5005823855969944188588301)
                ·
                  refine ⟨1877183945988729070720613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5005823855969944188588301 1877183945988729070720613)
                  ·
                    refine ⟨351971989872886700760115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877183945988729070720613 351971989872886700760115)
                    ·
                      rfl

theorem cell23_2056389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_2056389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056389 prefixEnd_2056389 := by exact prefixLift 2056389
  have htrace : WordTrace (prefixWord ++ tailWord_2056389) baseStart_2056389 baseEnd_2056389 := by
    simpa [prefixWord, tailWord_2056389, baseEnd_2056389] using wordTrace_append hprefix tailTrace_2056389
  have hstable : (prefixWord ++ tailWord_2056389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056389).length < 2 ^ (prefixWord ++ tailWord_2056389).sum := by decide
  have hdescent : baseEnd_2056389 < baseStart_2056389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056392 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2056392 : Nat := 118140960795 + 2056392 * 2 ^ 59
def prefixEnd_2056392 : Nat := 4983230072969 + 3 ^ 40 * 2056392 * 2
def baseEnd_2056392 : Nat := 1055917510060623590542831

theorem tailTrace_2056392 : CollatzResearch.WordTrace tailWord_2056392 prefixEnd_2056392 1055917510060623590542831 := by
  unfold tailWord_2056392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37501388983025231318973715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50001851977366975091964953 37501388983025231318973715)
  ·
    refine ⟨56252083474537846978460573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37501388983025231318973715 56252083474537846978460573)
    ·
      refine ⟨21094531302951692616922715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56252083474537846978460573 21094531302951692616922715)
      ·
        refine ⟨31641796954427538925384073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094531302951692616922715 31641796954427538925384073)
        ·
          refine ⟨23731347715820654194038055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31641796954427538925384073 23731347715820654194038055)
          ·
            refine ⟨35597021573730981291057083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23731347715820654194038055 35597021573730981291057083)
            ·
              refine ⟨53395532360596471936585625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35597021573730981291057083 53395532360596471936585625)
              ·
                refine ⟨40046649270447353952439219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53395532360596471936585625 40046649270447353952439219)
                ·
                  refine ⟨60069973905671030928658829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40046649270447353952439219 60069973905671030928658829)
                  ·
                    refine ⟨22526240214626636598247061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60069973905671030928658829 22526240214626636598247061)
                    ·
                      refine ⟨1055917510060623590542831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22526240214626636598247061 1055917510060623590542831)
                      ·
                        rfl

theorem cell23_2056392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2056392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056392 prefixEnd_2056392 := by exact prefixLift 2056392
  have htrace : WordTrace (prefixWord ++ tailWord_2056392) baseStart_2056392 baseEnd_2056392 := by
    simpa [prefixWord, tailWord_2056392, baseEnd_2056392] using wordTrace_append hprefix tailTrace_2056392
  have hstable : (prefixWord ++ tailWord_2056392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056392).length < 2 ^ (prefixWord ++ tailWord_2056392).sum := by decide
  have hdescent : baseEnd_2056392 < baseStart_2056392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056449 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2056449 : Nat := 118140960795 + 2056449 * 2 ^ 59
def prefixEnd_2056449 : Nat := 4983230072969 + 3 ^ 40 * 2056449 * 2
def baseEnd_2056449 : Nat := 351982259485976622510023

theorem tailTrace_2056449 : CollatzResearch.WordTrace tailWord_2056449 prefixEnd_2056449 351982259485976622510023 := by
  unfold tailWord_2056449
  simp only [CollatzResearch.WordTrace]
  refine ⟨75004856926843961372772401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50003237951229307581848267 75004856926843961372772401)
  ·
    refine ⟨56253642695132971029579301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75004856926843961372772401 56253642695132971029579301)
    ·
      refine ⟨10547558005337432068046119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56253642695132971029579301 10547558005337432068046119)
      ·
        refine ⟨15821337008006148102069179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547558005337432068046119 15821337008006148102069179)
        ·
          refine ⟨23732005512009222153103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821337008006148102069179 23732005512009222153103769)
          ·
            refine ⟨17799004134006916614827827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23732005512009222153103769 17799004134006916614827827)
            ·
              refine ⟨26698506201010374922241741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17799004134006916614827827 26698506201010374922241741)
              ·
                refine ⟨10011939825378890595840653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26698506201010374922241741 10011939825378890595840653)
                ·
                  refine ⟨3754477434517083973440245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10011939825378890595840653 3754477434517083973440245)
                  ·
                    refine ⟨351982259485976622510023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3754477434517083973440245 351982259485976622510023)
                    ·
                      rfl

theorem cell23_2056449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2056449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056449 prefixEnd_2056449 := by exact prefixLift 2056449
  have htrace : WordTrace (prefixWord ++ tailWord_2056449) baseStart_2056449 baseEnd_2056449 := by
    simpa [prefixWord, tailWord_2056449, baseEnd_2056449] using wordTrace_append hprefix tailTrace_2056449
  have hstable : (prefixWord ++ tailWord_2056449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056449).length < 2 ^ (prefixWord ++ tailWord_2056449).sum := by decide
  have hdescent : baseEnd_2056449 < baseStart_2056449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056450 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2056450 : Nat := 118140960795 + 2056450 * 2 ^ 59
def prefixEnd_2056450 : Nat := 4983230072969 + 3 ^ 40 * 2056450 * 2
def baseEnd_2056450 : Nat := 1055947291938584363617565

theorem tailTrace_2056450 : CollatzResearch.WordTrace tailWord_2056450 prefixEnd_2056450 1055947291938584363617565 := by
  unfold tailWord_2056450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751223349960084635889701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50003262266560225695705869 18751223349960084635889701)
  ·
    refine ⟨3515854378117515869229319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18751223349960084635889701 3515854378117515869229319)
    ·
      refine ⟨5273781567176273803843979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515854378117515869229319 5273781567176273803843979)
      ·
        refine ⟨7910672350764410705765969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273781567176273803843979 7910672350764410705765969)
        ·
          refine ⟨5933004263073308029324477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7910672350764410705765969 5933004263073308029324477)
          ·
            refine ⟨2224876598652490510996679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5933004263073308029324477 2224876598652490510996679)
            ·
              refine ⟨3337314897978735766495019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224876598652490510996679 3337314897978735766495019)
              ·
                refine ⟨5005972346968103649742529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337314897978735766495019 5005972346968103649742529)
                ·
                  refine ⟨3754479260226077737306897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005972346968103649742529 3754479260226077737306897)
                  ·
                    refine ⟨2815859445169558302980173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3754479260226077737306897 2815859445169558302980173)
                    ·
                      refine ⟨1055947291938584363617565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815859445169558302980173 1055947291938584363617565)
                      ·
                        rfl

theorem cell23_2056450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2056450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056450 prefixEnd_2056450 := by exact prefixLift 2056450
  have htrace : WordTrace (prefixWord ++ tailWord_2056450) baseStart_2056450 baseEnd_2056450 := by
    simpa [prefixWord, tailWord_2056450, baseEnd_2056450] using wordTrace_append hprefix tailTrace_2056450
  have hstable : (prefixWord ++ tailWord_2056450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056450).length < 2 ^ (prefixWord ++ tailWord_2056450).sum := by decide
  have hdescent : baseEnd_2056450 < baseStart_2056450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056480 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2056480 : Nat := 118140960795 + 2056480 * 2 ^ 59
def prefixEnd_2056480 : Nat := 4983230072969 + 3 ^ 40 * 2056480 * 2
def baseEnd_2056480 : Nat := 1055962696358219246242427

theorem tailTrace_2056480 : CollatzResearch.WordTrace tailWord_2056480 prefixEnd_2056480 1055962696358219246242427 := by
  unfold tailWord_2056480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37502993794865826833575447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50003991726487769111433929 37502993794865826833575447)
  ·
    refine ⟨56254490692298740250363171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37502993794865826833575447 56254490692298740250363171)
    ·
      refine ⟨84381736038448110375544757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56254490692298740250363171 84381736038448110375544757)
      ·
        refine ⟨7910787753604510347707321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84381736038448110375544757 7910787753604510347707321)
        ·
          refine ⟨5933090815203382760780491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7910787753604510347707321 5933090815203382760780491)
          ·
            refine ⟨8899636222805074141170737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933090815203382760780491 8899636222805074141170737)
            ·
              refine ⟨6674727167103805605878053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8899636222805074141170737 6674727167103805605878053)
              ·
                refine ⟨1251511343831963551102135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6674727167103805605878053 1251511343831963551102135)
                ·
                  refine ⟨1877267015747945326653203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251511343831963551102135 1877267015747945326653203)
                  ·
                    refine ⟨2815900523621917989979805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877267015747945326653203 2815900523621917989979805)
                    ·
                      refine ⟨1055962696358219246242427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2815900523621917989979805 1055962696358219246242427)
                      ·
                        rfl

theorem cell23_2056480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2056480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056480 prefixEnd_2056480 := by exact prefixLift 2056480
  have htrace : WordTrace (prefixWord ++ tailWord_2056480) baseStart_2056480 baseEnd_2056480 := by
    simpa [prefixWord, tailWord_2056480, baseEnd_2056480] using wordTrace_append hprefix tailTrace_2056480
  have hstable : (prefixWord ++ tailWord_2056480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056480).length < 2 ^ (prefixWord ++ tailWord_2056480).sum := by decide
  have hdescent : baseEnd_2056480 < baseStart_2056480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056487 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 6]
def baseStart_2056487 : Nat := 118140960795 + 2056487 * 2 ^ 59
def prefixEnd_2056487 : Nat := 4983230072969 + 3 ^ 40 * 2056487 * 2
def baseEnd_2056487 : Nat := 117329587858088968761655

theorem tailTrace_2056487 : CollatzResearch.WordTrace tailWord_2056487 prefixEnd_2056487 117329587858088968761655 := by
  unfold tailWord_2056487
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006242900706293862655715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50004161933804195908437143 75006242900706293862655715)
  ·
    refine ⟨112509364351059440793983573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75006242900706293862655715 112509364351059440793983573)
    ·
      refine ⟨1318469113488977821804495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 112509364351059440793983573 1318469113488977821804495)
      ·
        refine ⟨1977703670233466732706743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318469113488977821804495 1977703670233466732706743)
        ·
          refine ⟨2966555505350200099060115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977703670233466732706743 2966555505350200099060115)
          ·
            refine ⟨4449833258025300148590173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966555505350200099060115 4449833258025300148590173)
            ·
              refine ⟨1668687471759487555721315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4449833258025300148590173 1668687471759487555721315)
              ·
                refine ⟨2503031207639231333581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668687471759487555721315 2503031207639231333581973)
                ·
                  refine ⟨117329587858088968761655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2503031207639231333581973 117329587858088968761655)
                  ·
                    rfl

theorem cell23_2056487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 6].length) (baseStart_2056487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056487 prefixEnd_2056487 := by exact prefixLift 2056487
  have htrace : WordTrace (prefixWord ++ tailWord_2056487) baseStart_2056487 baseEnd_2056487 := by
    simpa [prefixWord, tailWord_2056487, baseEnd_2056487] using wordTrace_append hprefix tailTrace_2056487
  have hstable : (prefixWord ++ tailWord_2056487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056487).length < 2 ^ (prefixWord ++ tailWord_2056487).sum := by decide
  have hdescent : baseEnd_2056487 < baseStart_2056487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056499 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_2056499 : Nat := 118140960795 + 2056499 * 2 ^ 59
def prefixEnd_2056499 : Nat := 4983230072969 + 3 ^ 40 * 2056499 * 2
def baseEnd_2056499 : Nat := 1055972452490654671904839

theorem tailTrace_2056499 : CollatzResearch.WordTrace tailWord_2056499 prefixEnd_2056499 1055972452490654671904839 := by
  unfold tailWord_2056499
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006680576662819912092551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50004453717775213274728367 75006680576662819912092551)
  ·
    refine ⟨112510020864994229868138827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75006680576662819912092551 112510020864994229868138827)
    ·
      refine ⟨168765031297491344802208241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112510020864994229868138827 168765031297491344802208241)
      ·
        refine ⟨126573773473118508601656181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168765031297491344802208241 126573773473118508601656181)
        ·
          refine ⟨11866291263104860181405267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126573773473118508601656181 11866291263104860181405267)
          ·
            refine ⟨17799436894657290272107901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866291263104860181405267 17799436894657290272107901)
            ·
              refine ⟨6674788835496483852040463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17799436894657290272107901 6674788835496483852040463)
              ·
                refine ⟨10012183253244725778060695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6674788835496483852040463 10012183253244725778060695)
                ·
                  refine ⟨15018274879867088667091043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10012183253244725778060695 15018274879867088667091043)
                  ·
                    refine ⟨22527412319800633000636565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15018274879867088667091043 22527412319800633000636565)
                    ·
                      refine ⟨1055972452490654671904839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22527412319800633000636565 1055972452490654671904839)
                      ·
                        rfl

theorem cell23_2056499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_2056499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056499 prefixEnd_2056499 := by exact prefixLift 2056499
  have htrace : WordTrace (prefixWord ++ tailWord_2056499) baseStart_2056499 baseEnd_2056499 := by
    simpa [prefixWord, tailWord_2056499, baseEnd_2056499] using wordTrace_append hprefix tailTrace_2056499
  have hstable : (prefixWord ++ tailWord_2056499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056499).length < 2 ^ (prefixWord ++ tailWord_2056499).sum := by decide
  have hdescent : baseEnd_2056499 < baseStart_2056499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056553 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_2056553 : Nat := 118140960795 + 2056553 * 2 ^ 59
def prefixEnd_2056553 : Nat := 4983230072969 + 3 ^ 40 * 2056553 * 2
def baseEnd_2056553 : Nat := 1056000180445997460629591

theorem tailTrace_2056553 : CollatzResearch.WordTrace tailWord_2056553 prefixEnd_2056553 1056000180445997460629591 := by
  unfold tailWord_2056553
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008650118467187134558313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50005766745644791423038875 75008650118467187134558313)
  ·
    refine ⟨56256487588850390350918735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75008650118467187134558313 56256487588850390350918735)
    ·
      refine ⟨84384731383275585526378103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56256487588850390350918735 84384731383275585526378103)
      ·
        refine ⟨126577097074913378289567155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84384731383275585526378103 126577097074913378289567155)
        ·
          refine ⟨189865645612370067434350733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126577097074913378289567155 189865645612370067434350733)
          ·
            refine ⟨71199617104638775287881525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189865645612370067434350733 71199617104638775287881525)
            ·
              refine ⟨6674964103559885183238893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71199617104638775287881525 6674964103559885183238893)
              ·
                refine ⟨2503111538834956943714585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6674964103559885183238893 2503111538834956943714585)
                ·
                  refine ⟨1877333654126217707785939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503111538834956943714585 1877333654126217707785939)
                  ·
                    refine ⟨2816000481189326561678909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877333654126217707785939 2816000481189326561678909)
                    ·
                      refine ⟨1056000180445997460629591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816000481189326561678909 1056000180445997460629591)
                      ·
                        rfl

theorem cell23_2056553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_2056553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056553 prefixEnd_2056553 := by exact prefixLift 2056553
  have htrace : WordTrace (prefixWord ++ tailWord_2056553) baseStart_2056553 baseEnd_2056553 := by
    simpa [prefixWord, tailWord_2056553, baseEnd_2056553] using wordTrace_append hprefix tailTrace_2056553
  have hstable : (prefixWord ++ tailWord_2056553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056553).length < 2 ^ (prefixWord ++ tailWord_2056553).sum := by decide
  have hdescent : baseEnd_2056553 < baseStart_2056553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056559 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_2056559 : Nat := 118140960795 + 2056559 * 2 ^ 59
def prefixEnd_2056559 : Nat := 4983230072969 + 3 ^ 40 * 2056559 * 2
def baseEnd_2056559 : Nat := 1056003261329924437154563

theorem tailTrace_2056559 : CollatzResearch.WordTrace tailWord_2056559 prefixEnd_2056559 1056003261329924437154563 := by
  unfold tailWord_2056559
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008868956445450159276731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50005912637630300106184487 75008868956445450159276731)
  ·
    refine ⟨112513303434668175238915097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75008868956445450159276731 112513303434668175238915097)
    ·
      refine ⟨84384977576001131429186323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112513303434668175238915097 84384977576001131429186323)
      ·
        refine ⟨126577466364001697143779485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84384977576001131429186323 126577466364001697143779485)
        ·
          refine ⟨47466549886500636428917307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126577466364001697143779485 47466549886500636428917307)
          ·
            refine ⟨71199824829750954643375961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47466549886500636428917307 71199824829750954643375961)
            ·
              refine ⟨53399868622313215982531971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71199824829750954643375961 53399868622313215982531971)
              ·
                refine ⟨80099802933469823973797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53399868622313215982531971 80099802933469823973797957)
                ·
                  refine ⟨15018713050025591995087117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80099802933469823973797957 15018713050025591995087117)
                  ·
                    refine ⟨5632017393759596998157669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15018713050025591995087117 5632017393759596998157669)
                    ·
                      refine ⟨1056003261329924437154563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5632017393759596998157669 1056003261329924437154563)
                      ·
                        rfl

theorem cell23_2056559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_2056559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056559 prefixEnd_2056559 := by exact prefixLift 2056559
  have htrace : WordTrace (prefixWord ++ tailWord_2056559) baseStart_2056559 baseEnd_2056559 := by
    simpa [prefixWord, tailWord_2056559, baseEnd_2056559] using wordTrace_append hprefix tailTrace_2056559
  have hstable : (prefixWord ++ tailWord_2056559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056559).length < 2 ^ (prefixWord ++ tailWord_2056559).sum := by decide
  have hdescent : baseEnd_2056559 < baseStart_2056559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056569 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_2056569 : Nat := 118140960795 + 2056569 * 2 ^ 59
def prefixEnd_2056569 : Nat := 4983230072969 + 3 ^ 40 * 2056569 * 2
def baseEnd_2056569 : Nat := 352002798712156466009839

theorem tailTrace_2056569 : CollatzResearch.WordTrace tailWord_2056569 prefixEnd_2056569 352002798712156466009839 := by
  unfold tailWord_2056569
  simp only [CollatzResearch.WordTrace]
  refine ⟨75009233686409221867140761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50006155790939481244760507 75009233686409221867140761)
  ·
    refine ⟨56256925264806916400355571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75009233686409221867140761 56256925264806916400355571)
    ·
      refine ⟨84385387897210374600533357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56256925264806916400355571 84385387897210374600533357)
      ·
        refine ⟨31644520461453890475200009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84385387897210374600533357 31644520461453890475200009)
        ·
          refine ⟨23733390346090417856400007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31644520461453890475200009 23733390346090417856400007)
          ·
            refine ⟨35600085519135626784600011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23733390346090417856400007 35600085519135626784600011)
            ·
              refine ⟨53400128278703440176900017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35600085519135626784600011 53400128278703440176900017)
              ·
                refine ⟨40050096209027580132675013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53400128278703440176900017 40050096209027580132675013)
                ·
                  refine ⟨7509393039192671274876565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40050096209027580132675013 7509393039192671274876565)
                  ·
                    refine ⟨352002798712156466009839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7509393039192671274876565 352002798712156466009839)
                    ·
                      rfl

theorem cell23_2056569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_2056569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056569 prefixEnd_2056569 := by exact prefixLift 2056569
  have htrace : WordTrace (prefixWord ++ tailWord_2056569) baseStart_2056569 baseEnd_2056569 := by
    simpa [prefixWord, tailWord_2056569, baseEnd_2056569] using wordTrace_append hprefix tailTrace_2056569
  have hstable : (prefixWord ++ tailWord_2056569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056569).length < 2 ^ (prefixWord ++ tailWord_2056569).sum := by decide
  have hdescent : baseEnd_2056569 < baseStart_2056569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056610 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2056610 : Nat := 118140960795 + 2056610 * 2 ^ 59
def prefixEnd_2056610 : Nat := 4983230072969 + 3 ^ 40 * 2056610 * 2
def baseEnd_2056610 : Nat := 1056029448843303737616829

theorem tailTrace_2056610 : CollatzResearch.WordTrace tailWord_2056610 prefixEnd_2056610 1056029448843303737616829 := by
  unfold tailWord_2056610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752682269815171467345821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50007152719507123912922189 18752682269815171467345821)
  ·
    refine ⟨7032255851180689300254683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18752682269815171467345821 7032255851180689300254683)
    ·
      refine ⟨10548383776771033950382025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032255851180689300254683 10548383776771033950382025)
      ·
        refine ⟨7911287832578275462786519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548383776771033950382025 7911287832578275462786519)
        ·
          refine ⟨11866931748867413194179779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911287832578275462786519 11866931748867413194179779)
          ·
            refine ⟨17800397623301119791269669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866931748867413194179779 17800397623301119791269669)
            ·
              refine ⟨3337574554368959960863063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17800397623301119791269669 3337574554368959960863063)
              ·
                refine ⟨5006361831553439941294595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337574554368959960863063 5006361831553439941294595)
                ·
                  refine ⟨7509542747330159911941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006361831553439941294595 7509542747330159911941893)
                  ·
                    refine ⟨1408039265124404983489105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7509542747330159911941893 1408039265124404983489105)
                    ·
                      refine ⟨1056029448843303737616829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408039265124404983489105 1056029448843303737616829)
                      ·
                        rfl

theorem cell23_2056610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2056610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056610 prefixEnd_2056610 := by exact prefixLift 2056610
  have htrace : WordTrace (prefixWord ++ tailWord_2056610) baseStart_2056610 baseEnd_2056610 := by
    simpa [prefixWord, tailWord_2056610, baseEnd_2056610] using wordTrace_append hprefix tailTrace_2056610
  have hstable : (prefixWord ++ tailWord_2056610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056610).length < 2 ^ (prefixWord ++ tailWord_2056610).sum := by decide
  have hdescent : baseEnd_2056610 < baseStart_2056610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056626 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2056626 : Nat := 118140960795 + 2056626 * 2 ^ 59
def prefixEnd_2056626 : Nat := 4983230072969 + 3 ^ 40 * 2056626 * 2
def baseEnd_2056626 : Nat := 1056037664533775675016755

theorem tailTrace_2056626 : CollatzResearch.WordTrace tailWord_2056626 prefixEnd_2056626 1056037664533775675016755 := by
  unfold tailWord_2056626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18752828161800680150491433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50007541764801813734643821 18752828161800680150491433)
  ·
    refine ⟨14064621121350510112868575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18752828161800680150491433 14064621121350510112868575)
    ·
      refine ⟨21096931682025765169302863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14064621121350510112868575 21096931682025765169302863)
      ·
        refine ⟨31645397523038647753954295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096931682025765169302863 31645397523038647753954295)
        ·
          refine ⟨47468096284557971630931443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31645397523038647753954295 47468096284557971630931443)
          ·
            refine ⟨71202144426836957446397165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468096284557971630931443 71202144426836957446397165)
            ·
              refine ⟨26700804160063859042398937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71202144426836957446397165 26700804160063859042398937)
              ·
                refine ⟨20025603120047894281799203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26700804160063859042398937 20025603120047894281799203)
                ·
                  refine ⟨30038404680071841422698805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20025603120047894281799203 30038404680071841422698805)
                  ·
                    refine ⟨2816100438756735133378013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30038404680071841422698805 2816100438756735133378013)
                    ·
                      refine ⟨1056037664533775675016755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816100438756735133378013 1056037664533775675016755)
                      ·
                        rfl

theorem cell23_2056626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2056626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056626 prefixEnd_2056626 := by exact prefixLift 2056626
  have htrace : WordTrace (prefixWord ++ tailWord_2056626) baseStart_2056626 baseEnd_2056626 := by
    simpa [prefixWord, tailWord_2056626, baseEnd_2056626] using wordTrace_append hprefix tailTrace_2056626
  have hstable : (prefixWord ++ tailWord_2056626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056626).length < 2 ^ (prefixWord ++ tailWord_2056626).sum := by decide
  have hdescent : baseEnd_2056626 < baseStart_2056626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056633 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 5]
def baseStart_2056633 : Nat := 118140960795 + 2056633 * 2 ^ 59
def prefixEnd_2056633 : Nat := 4983230072969 + 3 ^ 40 * 2056633 * 2
def baseEnd_2056633 : Nat := 117337917655373016403247

theorem tailTrace_2056633 : CollatzResearch.WordTrace tailWord_2056633 prefixEnd_2056633 117337917655373016403247 := by
  unfold tailWord_2056633
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011567958177360797470553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50007711972118240531647035 75011567958177360797470553)
  ·
    refine ⟨56258675968633020598102915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75011567958177360797470553 56258675968633020598102915)
    ·
      refine ⟨84388013952949530897154373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56258675968633020598102915 84388013952949530897154373)
      ·
        refine ⟨15822752616178037043216445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84388013952949530897154373 15822752616178037043216445)
        ·
          refine ⟨5933532231066763891206167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15822752616178037043216445 5933532231066763891206167)
          ·
            refine ⟨8900298346600145836809251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933532231066763891206167 8900298346600145836809251)
            ·
              refine ⟨13350447519900218755213877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900298346600145836809251 13350447519900218755213877)
              ·
                refine ⟨1251604454990645508301301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13350447519900218755213877 1251604454990645508301301)
                ·
                  refine ⟨117337917655373016403247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251604454990645508301301 117337917655373016403247)
                  ·
                    rfl

theorem cell23_2056633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 5].length) (baseStart_2056633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056633 prefixEnd_2056633 := by exact prefixLift 2056633
  have htrace : WordTrace (prefixWord ++ tailWord_2056633) baseStart_2056633 baseEnd_2056633 := by
    simpa [prefixWord, tailWord_2056633, baseEnd_2056633] using wordTrace_append hprefix tailTrace_2056633
  have hstable : (prefixWord ++ tailWord_2056633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056633).length < 2 ^ (prefixWord ++ tailWord_2056633).sum := by decide
  have hdescent : baseEnd_2056633 < baseStart_2056633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056666 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2056666 : Nat := 118140960795 + 2056666 * 2 ^ 59
def prefixEnd_2056666 : Nat := 4983230072969 + 3 ^ 40 * 2056666 * 2
def baseEnd_2056666 : Nat := 1056058203759955518516571

theorem tailTrace_2056666 : CollatzResearch.WordTrace tailWord_2056666 prefixEnd_2056666 1056058203759955518516571 := by
  unfold tailWord_2056666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753192891764451858355463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50008514378038538288947901 18753192891764451858355463)
  ·
    refine ⟨28129789337646677787533195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753192891764451858355463 28129789337646677787533195)
    ·
      refine ⟨42194684006470016681299793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28129789337646677787533195 42194684006470016681299793)
      ·
        refine ⟨31646013004852512510974845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42194684006470016681299793 31646013004852512510974845)
        ·
          refine ⟨11867254876819692191615567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31646013004852512510974845 11867254876819692191615567)
          ·
            refine ⟨17800882315229538287423351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867254876819692191615567 17800882315229538287423351)
            ·
              refine ⟨26701323472844307431135027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800882315229538287423351 26701323472844307431135027)
              ·
                refine ⟨40051985209266461146702541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26701323472844307431135027 40051985209266461146702541)
                ·
                  refine ⟨15019494453474922930013453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40051985209266461146702541 15019494453474922930013453)
                  ·
                    refine ⟨5632310420053096098755045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15019494453474922930013453 5632310420053096098755045)
                    ·
                      refine ⟨1056058203759955518516571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5632310420053096098755045 1056058203759955518516571)
                      ·
                        rfl

theorem cell23_2056666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2056666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056666 prefixEnd_2056666 := by exact prefixLift 2056666
  have htrace : WordTrace (prefixWord ++ tailWord_2056666) baseStart_2056666 baseEnd_2056666 := by
    simpa [prefixWord, tailWord_2056666, baseEnd_2056666] using wordTrace_append hprefix tailTrace_2056666
  have hstable : (prefixWord ++ tailWord_2056666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056666).length < 2 ^ (prefixWord ++ tailWord_2056666).sum := by decide
  have hdescent : baseEnd_2056666 < baseStart_2056666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056703 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_2056703 : Nat := 118140960795 + 2056703 * 2 ^ 59
def prefixEnd_2056703 : Nat := 4983230072969 + 3 ^ 40 * 2056703 * 2
def baseEnd_2056703 : Nat := 1056077202544171873753901

theorem tailTrace_2056703 : CollatzResearch.WordTrace tailWord_2056703 prefixEnd_2056703 1056077202544171873753901 := by
  unfold tailWord_2056703
  simp only [CollatzResearch.WordTrace]
  refine ⟨75014121067923762752518763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50009414045282508501679175 75014121067923762752518763)
  ·
    refine ⟨112521181601885644128778145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75014121067923762752518763 112521181601885644128778145)
    ·
      refine ⟨84390886201414233096583609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112521181601885644128778145 84390886201414233096583609)
      ·
        refine ⟨63293164651060674822437707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84390886201414233096583609 63293164651060674822437707)
        ·
          refine ⟨94939746976591012233656561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63293164651060674822437707 94939746976591012233656561)
          ·
            refine ⟨71204810232443259175242421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94939746976591012233656561 71204810232443259175242421)
            ·
              refine ⟨6675450959291555547678977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71204810232443259175242421 6675450959291555547678977)
              ·
                refine ⟨5006588219468666660759233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6675450959291555547678977 5006588219468666660759233)
                ·
                  refine ⟨3754941164601499995569425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006588219468666660759233 3754941164601499995569425)
                  ·
                    refine ⟨2816205873451124996677069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3754941164601499995569425 2816205873451124996677069)
                    ·
                      refine ⟨1056077202544171873753901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816205873451124996677069 1056077202544171873753901)
                      ·
                        rfl

theorem cell23_2056703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_2056703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056703 prefixEnd_2056703 := by exact prefixLift 2056703
  have htrace : WordTrace (prefixWord ++ tailWord_2056703) baseStart_2056703 baseEnd_2056703 := by
    simpa [prefixWord, tailWord_2056703, baseEnd_2056703] using wordTrace_append hprefix tailTrace_2056703
  have hstable : (prefixWord ++ tailWord_2056703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056703).length < 2 ^ (prefixWord ++ tailWord_2056703).sum := by decide
  have hdescent : baseEnd_2056703 < baseStart_2056703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056753 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2056753 : Nat := 118140960795 + 2056753 * 2 ^ 59
def prefixEnd_2056753 : Nat := 4983230072969 + 3 ^ 40 * 2056753 * 2
def baseEnd_2056753 : Nat := 352034292192298892709557

theorem tailTrace_2056753 : CollatzResearch.WordTrace tailWord_2056753 prefixEnd_2056753 352034292192298892709557 := by
  unfold tailWord_2056753
  simp only [CollatzResearch.WordTrace]
  refine ⟨75015944717742621291838913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50010629811828414194559275 75015944717742621291838913)
  ·
    refine ⟨56261958538306965968879185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75015944717742621291838913 56261958538306965968879185)
    ·
      refine ⟨42196468903730224476659389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56261958538306965968879185 42196468903730224476659389)
      ·
        refine ⟨15823675838898834178747271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42196468903730224476659389 15823675838898834178747271)
        ·
          refine ⟨23735513758348251268120907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823675838898834178747271 23735513758348251268120907)
          ·
            refine ⟨35603270637522376902181361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23735513758348251268120907 35603270637522376902181361)
            ·
              refine ⟨26702452978141782676636021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35603270637522376902181361 26702452978141782676636021)
              ·
                refine ⟨2503354966700792125934627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26702452978141782676636021 2503354966700792125934627)
                ·
                  refine ⟨3755032450051188188901941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503354966700792125934627 3755032450051188188901941)
                  ·
                    refine ⟨352034292192298892709557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3755032450051188188901941 352034292192298892709557)
                    ·
                      rfl

theorem cell23_2056753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2056753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056753 prefixEnd_2056753 := by exact prefixLift 2056753
  have htrace : WordTrace (prefixWord ++ tailWord_2056753) baseStart_2056753 baseEnd_2056753 := by
    simpa [prefixWord, tailWord_2056753, baseEnd_2056753] using wordTrace_append hprefix tailTrace_2056753
  have hstable : (prefixWord ++ tailWord_2056753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056753).length < 2 ^ (prefixWord ++ tailWord_2056753).sum := by decide
  have hdescent : baseEnd_2056753 < baseStart_2056753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056760 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_2056760 : Nat := 118140960795 + 2056760 * 2 ^ 59
def prefixEnd_2056760 : Nat := 4983230072969 + 3 ^ 40 * 2056760 * 2
def baseEnd_2056760 : Nat := 1056106470941478150741139

theorem tailTrace_2056760 : CollatzResearch.WordTrace tailWord_2056760 prefixEnd_2056760 1056106470941478150741139 := by
  unfold tailWord_2056760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37508100014358630743671867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50010800019144840991562489 37508100014358630743671867)
  ·
    refine ⟨56262150021537946115507801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37508100014358630743671867 56262150021537946115507801)
    ·
      refine ⟨42196612516153459586630851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56262150021537946115507801 42196612516153459586630851)
      ·
        refine ⟨63294918774230189379946277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42196612516153459586630851 63294918774230189379946277)
        ·
          refine ⟨11867797270168160508739927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63294918774230189379946277 11867797270168160508739927)
          ·
            refine ⟨17801695905252240763109891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867797270168160508739927 17801695905252240763109891)
            ·
              refine ⟨26702543857878361144664837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17801695905252240763109891 26702543857878361144664837)
              ·
                refine ⟨5006726973352192714624657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26702543857878361144664837 5006726973352192714624657)
                ·
                  refine ⟨3755045230014144535968493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006726973352192714624657 3755045230014144535968493)
                  ·
                    refine ⟨1408141961255304200988185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3755045230014144535968493 1408141961255304200988185)
                    ·
                      refine ⟨1056106470941478150741139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408141961255304200988185 1056106470941478150741139)
                      ·
                        rfl

theorem cell23_2056760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_2056760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056760 prefixEnd_2056760 := by exact prefixLift 2056760
  have htrace : WordTrace (prefixWord ++ tailWord_2056760) baseStart_2056760 baseEnd_2056760 := by
    simpa [prefixWord, tailWord_2056760, baseEnd_2056760] using wordTrace_append hprefix tailTrace_2056760
  have hstable : (prefixWord ++ tailWord_2056760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056760).length < 2 ^ (prefixWord ++ tailWord_2056760).sum := by decide
  have hdescent : baseEnd_2056760 < baseStart_2056760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056767 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 1, 1, 3]
def baseStart_2056767 : Nat := 118140960795 + 2056767 * 2 ^ 59
def prefixEnd_2056767 : Nat := 4983230072969 + 3 ^ 40 * 2056767 * 2
def baseEnd_2056767 : Nat := 1056110065306059623353607

theorem tailTrace_2056767 : CollatzResearch.WordTrace tailWord_2056767 prefixEnd_2056767 1056110065306059623353607 := by
  unfold tailWord_2056767
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016455339691901682848555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50010970226461267788565703 75016455339691901682848555)
  ·
    refine ⟨112524683009537852524272833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75016455339691901682848555 112524683009537852524272833)
    ·
      refine ⟨84393512257153389393204625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112524683009537852524272833 84393512257153389393204625)
      ·
        refine ⟨63295134192865042044903469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84393512257153389393204625 63295134192865042044903469)
        ·
          refine ⟨23735675322324390766838801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63295134192865042044903469 23735675322324390766838801)
          ·
            refine ⟨17801756491743293075129101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23735675322324390766838801 17801756491743293075129101)
            ·
              refine ⟨6675658684403734903173413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17801756491743293075129101 6675658684403734903173413)
              ·
                refine ⟨1251686003325700294345015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6675658684403734903173413 1251686003325700294345015)
                ·
                  refine ⟨1877529004988550441517523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1251686003325700294345015 1877529004988550441517523)
                  ·
                    refine ⟨2816293507482825662276285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877529004988550441517523 2816293507482825662276285)
                    ·
                      refine ⟨1056110065306059623353607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816293507482825662276285 1056110065306059623353607)
                      ·
                        rfl

theorem cell23_2056767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_2056767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056767 prefixEnd_2056767 := by exact prefixLift 2056767
  have htrace : WordTrace (prefixWord ++ tailWord_2056767) baseStart_2056767 baseEnd_2056767 := by
    simpa [prefixWord, tailWord_2056767, baseEnd_2056767] using wordTrace_append hprefix tailTrace_2056767
  have hstable : (prefixWord ++ tailWord_2056767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056767).length < 2 ^ (prefixWord ++ tailWord_2056767).sum := by decide
  have hdescent : baseEnd_2056767 < baseStart_2056767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056773 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_2056773 : Nat := 118140960795 + 2056773 * 2 ^ 59
def prefixEnd_2056773 : Nat := 4983230072969 + 3 ^ 40 * 2056773 * 2
def baseEnd_2056773 : Nat := 1056113146189986599878579

theorem tailTrace_2056773 : CollatzResearch.WordTrace tailWord_2056773 prefixEnd_2056773 1056113146189986599878579 := by
  unfold tailWord_2056773
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016674177670164707566973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50011116118446776471711315 75016674177670164707566973)
  ·
    refine ⟨28131252816626311765337615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75016674177670164707566973 28131252816626311765337615)
    ·
      refine ⟨42196879224939467648006423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28131252816626311765337615 42196879224939467648006423)
      ·
        refine ⟨63295318837409201472009635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42196879224939467648006423 63295318837409201472009635)
        ·
          refine ⟨94942978256113802208014453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63295318837409201472009635 94942978256113802208014453)
          ·
            refine ⟨8900904211510668957001355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94942978256113802208014453 8900904211510668957001355)
            ·
              refine ⟨13351356317266003435502033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900904211510668957001355 13351356317266003435502033)
              ·
                refine ⟨10013517237949502576626525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351356317266003435502033 10013517237949502576626525)
                ·
                  refine ⟨3755068964231063466234947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10013517237949502576626525 3755068964231063466234947)
                  ·
                    refine ⟨5632603446346595199352421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755068964231063466234947 5632603446346595199352421)
                    ·
                      refine ⟨1056113146189986599878579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5632603446346595199352421 1056113146189986599878579)
                      ·
                        rfl

theorem cell23_2056773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_2056773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056773 prefixEnd_2056773 := by exact prefixLift 2056773
  have htrace : WordTrace (prefixWord ++ tailWord_2056773) baseStart_2056773 baseEnd_2056773 := by
    simpa [prefixWord, tailWord_2056773, baseEnd_2056773] using wordTrace_append hprefix tailTrace_2056773
  have hstable : (prefixWord ++ tailWord_2056773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056773).length < 2 ^ (prefixWord ++ tailWord_2056773).sum := by decide
  have hdescent : baseEnd_2056773 < baseStart_2056773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056803 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2056803 : Nat := 118140960795 + 2056803 * 2 ^ 59
def prefixEnd_2056803 : Nat := 4983230072969 + 3 ^ 40 * 2056803 * 2
def baseEnd_2056803 : Nat := 1056128550609621482503441

theorem tailTrace_2056803 : CollatzResearch.WordTrace tailWord_2056803 prefixEnd_2056803 1056128550609621482503441 := by
  unfold tailWord_2056803
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017768367561479831159063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50011845578374319887439375 75017768367561479831159063)
  ·
    refine ⟨112526652551342219746738595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75017768367561479831159063 112526652551342219746738595)
    ·
      refine ⟨168789978827013329620107893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112526652551342219746738595 168789978827013329620107893)
      ·
        refine ⟨15824060515032499651885115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168789978827013329620107893 15824060515032499651885115)
        ·
          refine ⟨23736090772548749477827673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15824060515032499651885115 23736090772548749477827673)
          ·
            refine ⟨17802068079411562108370755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23736090772548749477827673 17802068079411562108370755)
            ·
              refine ⟨26703102119117343162556133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802068079411562108370755 26703102119117343162556133)
              ·
                refine ⟨5006831647334501842979275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26703102119117343162556133 5006831647334501842979275)
                ·
                  refine ⟨7510247471001752764468913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006831647334501842979275 7510247471001752764468913)
                  ·
                    refine ⟨5632685603251314573351685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7510247471001752764468913 5632685603251314573351685)
                    ·
                      refine ⟨1056128550609621482503441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5632685603251314573351685 1056128550609621482503441)
                      ·
                        rfl

theorem cell23_2056803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2056803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056803 prefixEnd_2056803 := by exact prefixLift 2056803
  have htrace : WordTrace (prefixWord ++ tailWord_2056803) baseStart_2056803 baseEnd_2056803 := by
    simpa [prefixWord, tailWord_2056803, baseEnd_2056803] using wordTrace_append hprefix tailTrace_2056803
  have hstable : (prefixWord ++ tailWord_2056803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056803).length < 2 ^ (prefixWord ++ tailWord_2056803).sum := by decide
  have hdescent : baseEnd_2056803 < baseStart_2056803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056813 : List Nat := [1, 5, 1, 1, 3, 2, 10]
def baseStart_2056813 : Nat := 118140960795 + 2056813 * 2 ^ 59
def prefixEnd_2056813 : Nat := 4983230072969 + 3 ^ 40 * 2056813 * 2
def baseEnd_2056813 : Nat := 13038687474273659794795

theorem tailTrace_2056813 : CollatzResearch.WordTrace tailWord_2056813 prefixEnd_2056813 13038687474273659794795 := by
  unfold tailWord_2056813
  simp only [CollatzResearch.WordTrace]
  refine ⟨75018133097525251539023093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50012088731683501026015395 75018133097525251539023093)
  ·
    refine ⟨7032949977892992331783415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75018133097525251539023093 7032949977892992331783415)
    ·
      refine ⟨10549424966839488497675123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032949977892992331783415 10549424966839488497675123)
      ·
        refine ⟨15824137450259232746512685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10549424966839488497675123 15824137450259232746512685)
        ·
          refine ⟨5934051543847212279942257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15824137450259232746512685 5934051543847212279942257)
          ·
            refine ⟨4450538657885409209956693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5934051543847212279942257 4450538657885409209956693)
            ·
              refine ⟨13038687474273659794795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4450538657885409209956693 13038687474273659794795)
              ·
                rfl

theorem cell23_2056813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 10].length) (baseStart_2056813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056813 prefixEnd_2056813 := by exact prefixLift 2056813
  have htrace : WordTrace (prefixWord ++ tailWord_2056813) baseStart_2056813 baseEnd_2056813 := by
    simpa [prefixWord, tailWord_2056813, baseEnd_2056813] using wordTrace_append hprefix tailTrace_2056813
  have hstable : (prefixWord ++ tailWord_2056813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056813).length < 2 ^ (prefixWord ++ tailWord_2056813).sum := by decide
  have hdescent : baseEnd_2056813 < baseStart_2056813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056823 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_2056823 : Nat := 118140960795 + 2056823 * 2 ^ 59
def prefixEnd_2056823 : Nat := 4983230072969 + 3 ^ 40 * 2056823 * 2
def baseEnd_2056823 : Nat := 1056138820222711404253349

theorem tailTrace_2056823 : CollatzResearch.WordTrace tailWord_2056823 prefixEnd_2056823 1056138820222711404253349 := by
  unfold tailWord_2056823
  simp only [CollatzResearch.WordTrace]
  refine ⟨75018497827489023246887123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50012331884992682164591415 75018497827489023246887123)
  ·
    refine ⟨112527746741233534870330685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75018497827489023246887123 112527746741233534870330685)
    ·
      refine ⟨42197905027962575576374007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112527746741233534870330685 42197905027962575576374007)
      ·
        refine ⟨63296857541943863364561011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42197905027962575576374007 63296857541943863364561011)
        ·
          refine ⟨94945286312915795046841517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63296857541943863364561011 94945286312915795046841517)
          ·
            refine ⟨35604482367343423142565569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94945286312915795046841517 35604482367343423142565569)
            ·
              refine ⟨26703361775507567356924177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35604482367343423142565569 26703361775507567356924177)
              ·
                refine ⟨20027521331630675517693133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26703361775507567356924177 20027521331630675517693133)
                ·
                  refine ⟨7510320499361503319134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20027521331630675517693133 7510320499361503319134925)
                  ·
                    refine ⟨2816370187260563744675597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7510320499361503319134925 2816370187260563744675597)
                    ·
                      refine ⟨1056138820222711404253349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816370187260563744675597 1056138820222711404253349)
                      ·
                        rfl

theorem cell23_2056823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_2056823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056823 prefixEnd_2056823 := by exact prefixLift 2056823
  have htrace : WordTrace (prefixWord ++ tailWord_2056823) baseStart_2056823 baseEnd_2056823 := by
    simpa [prefixWord, tailWord_2056823, baseEnd_2056823] using wordTrace_append hprefix tailTrace_2056823
  have hstable : (prefixWord ++ tailWord_2056823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056823).length < 2 ^ (prefixWord ++ tailWord_2056823).sum := by decide
  have hdescent : baseEnd_2056823 < baseStart_2056823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056900 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2056900 : Nat := 118140960795 + 2056900 * 2 ^ 59
def prefixEnd_2056900 : Nat := 4983230072969 + 3 ^ 40 * 2056900 * 2
def baseEnd_2056900 : Nat := 1056178358233107602990495

theorem tailTrace_2056900 : CollatzResearch.WordTrace tailWord_2056900 prefixEnd_2056900 1056178358233107602990495 := by
  unfold tailWord_2056900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37510653124105032698720077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50014204165473376931626769 37510653124105032698720077)
  ·
    refine ⟨14066494921539387262020029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37510653124105032698720077 14066494921539387262020029)
    ·
      refine ⟨5274935595577270223257511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14066494921539387262020029 5274935595577270223257511)
      ·
        refine ⟨7912403393365905334886267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274935595577270223257511 7912403393365905334886267)
        ·
          refine ⟨11868605090048858002329401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912403393365905334886267 11868605090048858002329401)
          ·
            refine ⟨8901453817536643501747051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11868605090048858002329401 8901453817536643501747051)
            ·
              refine ⟨13352180726304965252620577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901453817536643501747051 13352180726304965252620577)
              ·
                refine ⟨10014135544728723939465433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13352180726304965252620577 10014135544728723939465433)
                ·
                  refine ⟨7510601658546542954599075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014135544728723939465433 7510601658546542954599075)
                  ·
                    refine ⟨11265902487819814431898613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510601658546542954599075 11265902487819814431898613)
                    ·
                      refine ⟨1056178358233107602990495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11265902487819814431898613 1056178358233107602990495)
                      ·
                        rfl

theorem cell23_2056900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2056900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056900 prefixEnd_2056900 := by exact prefixLift 2056900
  have htrace : WordTrace (prefixWord ++ tailWord_2056900) baseStart_2056900 baseEnd_2056900 := by
    simpa [prefixWord, tailWord_2056900, baseEnd_2056900] using wordTrace_append hprefix tailTrace_2056900
  have hstable : (prefixWord ++ tailWord_2056900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056900).length < 2 ^ (prefixWord ++ tailWord_2056900).sum := by decide
  have hdescent : baseEnd_2056900 < baseStart_2056900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056914 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2056914 : Nat := 118140960795 + 2056914 * 2 ^ 59
def prefixEnd_2056914 : Nat := 4983230072969 + 3 ^ 40 * 2056914 * 2
def baseEnd_2056914 : Nat := 1056185546962270548215431

theorem tailTrace_2056914 : CollatzResearch.WordTrace tailWord_2056914 prefixEnd_2056914 1056185546962270548215431 := by
  unfold tailWord_2056914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755454217539836447112449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50014544580106230525633197 18755454217539836447112449)
  ·
    refine ⟨14066590663154877335334337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18755454217539836447112449 14066590663154877335334337)
    ·
      refine ⟨10549942997366158001500753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14066590663154877335334337 10549942997366158001500753)
      ·
        refine ⟨7912457248024618501125565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10549942997366158001500753 7912457248024618501125565)
        ·
          refine ⟨2967171468009231937922087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7912457248024618501125565 2967171468009231937922087)
          ·
            refine ⟨4450757202013847906883131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967171468009231937922087 4450757202013847906883131)
            ·
              refine ⟨6676135803020771860324697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450757202013847906883131 6676135803020771860324697)
              ·
                refine ⟨5007101852265578895243523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6676135803020771860324697 5007101852265578895243523)
                ·
                  refine ⟨7510652778398368342865285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007101852265578895243523 7510652778398368342865285)
                  ·
                    refine ⟨1408247395949694064287241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7510652778398368342865285 1408247395949694064287241)
                    ·
                      refine ⟨1056185546962270548215431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408247395949694064287241 1056185546962270548215431)
                      ·
                        rfl

theorem cell23_2056914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2056914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056914 prefixEnd_2056914 := by exact prefixLift 2056914
  have htrace : WordTrace (prefixWord ++ tailWord_2056914) baseStart_2056914 baseEnd_2056914 := by
    simpa [prefixWord, tailWord_2056914, baseEnd_2056914] using wordTrace_append hprefix tailTrace_2056914
  have hstable : (prefixWord ++ tailWord_2056914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056914).length < 2 ^ (prefixWord ++ tailWord_2056914).sum := by decide
  have hdescent : baseEnd_2056914 < baseStart_2056914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056931 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2056931 : Nat := 118140960795 + 2056931 * 2 ^ 59
def prefixEnd_2056931 : Nat := 4983230072969 + 3 ^ 40 * 2056931 * 2
def baseEnd_2056931 : Nat := 1056194276133396981702853

theorem tailTrace_2056931 : CollatzResearch.WordTrace tailWord_2056931 prefixEnd_2056931 1056194276133396981702853 := by
  unfold tailWord_2056931
  simp only [CollatzResearch.WordTrace]
  refine ⟨75022436911097757691818647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50014957940731838461212431 75022436911097757691818647)
  ·
    refine ⟨112533655366646636537727971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75022436911097757691818647 112533655366646636537727971)
    ·
      refine ⟨168800483049969954806591957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112533655366646636537727971 168800483049969954806591957)
      ·
        refine ⟨3956261321483670815779499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168800483049969954806591957 3956261321483670815779499)
        ·
          refine ⟨5934391982225506223669249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956261321483670815779499 5934391982225506223669249)
          ·
            refine ⟨4450793986669129667751937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5934391982225506223669249 4450793986669129667751937)
            ·
              refine ⟨3338095490001847250813953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450793986669129667751937 3338095490001847250813953)
              ·
                refine ⟨2503571617501385438110465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338095490001847250813953 2503571617501385438110465)
                ·
                  refine ⟨1877678713126039078582849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503571617501385438110465 1877678713126039078582849)
                  ·
                    refine ⟨1408259034844529308937137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1877678713126039078582849 1408259034844529308937137)
                    ·
                      refine ⟨1056194276133396981702853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408259034844529308937137 1056194276133396981702853)
                      ·
                        rfl

theorem cell23_2056931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2056931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056931 prefixEnd_2056931 := by exact prefixLift 2056931
  have htrace : WordTrace (prefixWord ++ tailWord_2056931) baseStart_2056931 baseEnd_2056931 := by
    simpa [prefixWord, tailWord_2056931, baseEnd_2056931] using wordTrace_append hprefix tailTrace_2056931
  have hstable : (prefixWord ++ tailWord_2056931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056931).length < 2 ^ (prefixWord ++ tailWord_2056931).sum := by decide
  have hdescent : baseEnd_2056931 < baseStart_2056931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056937 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 5]
def baseStart_2056937 : Nat := 118140960795 + 2056937 * 2 ^ 59
def prefixEnd_2056937 : Nat := 4983230072969 + 3 ^ 40 * 2056937 * 2
def baseEnd_2056937 : Nat := 117355261890813773136425

theorem tailTrace_2056937 : CollatzResearch.WordTrace tailWord_2056937 prefixEnd_2056937 117355261890813773136425 := by
  unfold tailWord_2056937
  simp only [CollatzResearch.WordTrace]
  refine ⟨75022655749076020716537065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50015103832717347144358043 75022655749076020716537065)
  ·
    refine ⟨56266991811807015537402799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75022655749076020716537065 56266991811807015537402799)
    ·
      refine ⟨84400487717710523306104199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56266991811807015537402799 84400487717710523306104199)
      ·
        refine ⟨126600731576565784959156299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84400487717710523306104199 126600731576565784959156299)
        ·
          refine ⟨189901097364848677438734449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126600731576565784959156299 189901097364848677438734449)
          ·
            refine ⟨142425823023636508079050837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189901097364848677438734449 142425823023636508079050837)
            ·
              refine ⟨1669052613558240329051377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 142425823023636508079050837 1669052613558240329051377)
              ·
                refine ⟨1251789460168680246788533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669052613558240329051377 1251789460168680246788533)
                ·
                  refine ⟨117355261890813773136425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1251789460168680246788533 117355261890813773136425)
                  ·
                    rfl

theorem cell23_2056937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 5].length) (baseStart_2056937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056937 prefixEnd_2056937 := by exact prefixLift 2056937
  have htrace : WordTrace (prefixWord ++ tailWord_2056937) baseStart_2056937 baseEnd_2056937 := by
    simpa [prefixWord, tailWord_2056937, baseEnd_2056937] using wordTrace_append hprefix tailTrace_2056937
  have hstable : (prefixWord ++ tailWord_2056937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056937).length < 2 ^ (prefixWord ++ tailWord_2056937).sum := by decide
  have hdescent : baseEnd_2056937 < baseStart_2056937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056948 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2056948 : Nat := 118140960795 + 2056948 * 2 ^ 59
def prefixEnd_2056948 : Nat := 4983230072969 + 3 ^ 40 * 2056948 * 2
def baseEnd_2056948 : Nat := 1056203005304523415190275

theorem tailTrace_2056948 : CollatzResearch.WordTrace tailWord_2056948 prefixEnd_2056948 1056203005304523415190275 := by
  unfold tailWord_2056948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37511528476018084797593749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50015371301357446396791665 37511528476018084797593749)
  ·
    refine ⟨1758352897313347724887207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37511528476018084797593749 1758352897313347724887207)
    ·
      refine ⟨2637529345970021587330811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1758352897313347724887207 2637529345970021587330811)
      ·
        refine ⟨3956294018955032380996217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2637529345970021587330811 3956294018955032380996217)
        ·
          refine ⟨2967220514216274285747163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3956294018955032380996217 2967220514216274285747163)
          ·
            refine ⟨4450830771324411428620745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967220514216274285747163 4450830771324411428620745)
            ·
              refine ⟨3338123078493308571465559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450830771324411428620745 3338123078493308571465559)
              ·
                refine ⟨5007184617739962857198339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338123078493308571465559 5007184617739962857198339)
                ·
                  refine ⟨7510776926609944285797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007184617739962857198339 7510776926609944285797509)
                  ·
                    refine ⟨1408270673739364553587033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7510776926609944285797509 1408270673739364553587033)
                    ·
                      refine ⟨1056203005304523415190275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408270673739364553587033 1056203005304523415190275)
                      ·
                        rfl

theorem cell23_2056948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2056948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056948 prefixEnd_2056948 := by exact prefixLift 2056948
  have htrace : WordTrace (prefixWord ++ tailWord_2056948) baseStart_2056948 baseEnd_2056948 := by
    simpa [prefixWord, tailWord_2056948, baseEnd_2056948] using wordTrace_append hprefix tailTrace_2056948
  have hstable : (prefixWord ++ tailWord_2056948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056948).length < 2 ^ (prefixWord ++ tailWord_2056948).sum := by decide
  have hdescent : baseEnd_2056948 < baseStart_2056948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056950 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2056950 : Nat := 118140960795 + 2056950 * 2 ^ 59
def prefixEnd_2056950 : Nat := 4983230072969 + 3 ^ 40 * 2056950 * 2
def baseEnd_2056950 : Nat := 352068010755277469121755

theorem tailTrace_2056950 : CollatzResearch.WordTrace tailWord_2056950 prefixEnd_2056950 352068010755277469121755 := by
  unfold tailWord_2056950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688945618626807746047519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50015419932019282624506869 4688945618626807746047519)
  ·
    refine ⟨7033418427940211619071279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688945618626807746047519 7033418427940211619071279)
    ·
      refine ⟨10550127641910317428606919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7033418427940211619071279 10550127641910317428606919)
      ·
        refine ⟨15825191462865476142910379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550127641910317428606919 15825191462865476142910379)
        ·
          refine ⟨23737787194298214214365569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825191462865476142910379 23737787194298214214365569)
          ·
            refine ⟨17803340395723660660774177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23737787194298214214365569 17803340395723660660774177)
            ·
              refine ⟨13352505296792745495580633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17803340395723660660774177 13352505296792745495580633)
              ·
                refine ⟨10014378972594559121685475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13352505296792745495580633 10014378972594559121685475)
                ·
                  refine ⟨15021568458891838682528213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014378972594559121685475 15021568458891838682528213)
                  ·
                    refine ⟨352068010755277469121755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15021568458891838682528213 352068010755277469121755)
                    ·
                      rfl

theorem cell23_2056950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2056950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056950 prefixEnd_2056950 := by exact prefixLift 2056950
  have htrace : WordTrace (prefixWord ++ tailWord_2056950) baseStart_2056950 baseEnd_2056950 := by
    simpa [prefixWord, tailWord_2056950, baseEnd_2056950] using wordTrace_append hprefix tailTrace_2056950
  have hstable : (prefixWord ++ tailWord_2056950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056950).length < 2 ^ (prefixWord ++ tailWord_2056950).sum := by decide
  have hdescent : baseEnd_2056950 < baseStart_2056950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056967 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 2, 5]
def baseStart_2056967 : Nat := 118140960795 + 2056967 * 2 ^ 59
def prefixEnd_2056967 : Nat := 4983230072969 + 3 ^ 40 * 2056967 * 2
def baseEnd_2056967 : Nat := 352070920478986280284229

theorem tailTrace_2056967 : CollatzResearch.WordTrace tailWord_2056967 prefixEnd_2056967 352070920478986280284229 := by
  unfold tailWord_2056967
  simp only [CollatzResearch.WordTrace]
  refine ⟨75023749938967335840129155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50015833292644890560086103 75023749938967335840129155)
  ·
    refine ⟨112535624908451003760193733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75023749938967335840129155 112535624908451003760193733)
    ·
      refine ⟨21100429670334563205036325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112535624908451003760193733 21100429670334563205036325)
      ·
        refine ⟨3956330563187730600944311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21100429670334563205036325 3956330563187730600944311)
        ·
          refine ⟨5934495844781595901416467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956330563187730600944311 5934495844781595901416467)
          ·
            refine ⟨8901743767172393852124701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934495844781595901416467 8901743767172393852124701)
            ·
              refine ⟨3338153912689647694546763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8901743767172393852124701 3338153912689647694546763)
              ·
                refine ⟨5007230869034471541820145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338153912689647694546763 5007230869034471541820145)
                ·
                  refine ⟨3755423151775853656365109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5007230869034471541820145 3755423151775853656365109)
                  ·
                    refine ⟨352070920478986280284229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3755423151775853656365109 352070920478986280284229)
                    ·
                      rfl

theorem cell23_2056967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_2056967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056967 prefixEnd_2056967 := by exact prefixLift 2056967
  have htrace : WordTrace (prefixWord ++ tailWord_2056967) baseStart_2056967 baseEnd_2056967 := by
    simpa [prefixWord, tailWord_2056967, baseEnd_2056967] using wordTrace_append hprefix tailTrace_2056967
  have hstable : (prefixWord ++ tailWord_2056967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056967).length < 2 ^ (prefixWord ++ tailWord_2056967).sum := by decide
  have hdescent : baseEnd_2056967 < baseStart_2056967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056970 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2056970 : Nat := 118140960795 + 2056970 * 2 ^ 59
def prefixEnd_2056970 : Nat := 4983230072969 + 3 ^ 40 * 2056970 * 2
def baseEnd_2056970 : Nat := 1056214301878922329115173

theorem tailTrace_2056970 : CollatzResearch.WordTrace tailWord_2056970 prefixEnd_2056970 1056214301878922329115173 := by
  unfold tailWord_2056970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755964839489116838122091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50015906238637644901658909 18755964839489116838122091)
  ·
    refine ⟨28133947259233675257183137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18755964839489116838122091 28133947259233675257183137)
    ·
      refine ⟨21100460444425256442887353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28133947259233675257183137 21100460444425256442887353)
      ·
        refine ⟨15825345333318942332165515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21100460444425256442887353 15825345333318942332165515)
        ·
          refine ⟨23738017999978413498248273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825345333318942332165515 23738017999978413498248273)
          ·
            refine ⟨17803513499983810123686205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23738017999978413498248273 17803513499983810123686205)
            ·
              refine ⟨6676317562493928796382327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17803513499983810123686205 6676317562493928796382327)
              ·
                refine ⟨10014476343740893194573491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676317562493928796382327 10014476343740893194573491)
                ·
                  refine ⟨15021714515611339791860237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014476343740893194573491 15021714515611339791860237)
                  ·
                    refine ⟨5633142943354252421947589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15021714515611339791860237 5633142943354252421947589)
                    ·
                      refine ⟨1056214301878922329115173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5633142943354252421947589 1056214301878922329115173)
                      ·
                        rfl

theorem cell23_2056970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2056970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056970 prefixEnd_2056970 := by exact prefixLift 2056970
  have htrace : WordTrace (prefixWord ++ tailWord_2056970) baseStart_2056970 baseEnd_2056970 := by
    simpa [prefixWord, tailWord_2056970, baseEnd_2056970] using wordTrace_append hprefix tailTrace_2056970
  have hstable : (prefixWord ++ tailWord_2056970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056970).length < 2 ^ (prefixWord ++ tailWord_2056970).sum := by decide
  have hdescent : baseEnd_2056970 < baseStart_2056970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056997 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_2056997 : Nat := 118140960795 + 2056997 * 2 ^ 59
def prefixEnd_2056997 : Nat := 4983230072969 + 3 ^ 40 * 2056997 * 2
def baseEnd_2056997 : Nat := 352076055285531241159183

theorem tailTrace_2056997 : CollatzResearch.WordTrace tailWord_2056997 prefixEnd_2056997 352076055285531241159183 := by
  unfold tailWord_2056997
  simp only [CollatzResearch.WordTrace]
  refine ⟨75024844128858650963721245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50016562752572433975814163 75024844128858650963721245)
  ·
    refine ⟨28134316548321994111395467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75024844128858650963721245 28134316548321994111395467)
    ·
      refine ⟨42201474822482991167093201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28134316548321994111395467 42201474822482991167093201)
      ·
        refine ⟨31651106116862243375319901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42201474822482991167093201 31651106116862243375319901)
        ·
          refine ⟨11869164793823341265744963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31651106116862243375319901 11869164793823341265744963)
          ·
            refine ⟨17803747190735011898617445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869164793823341265744963 17803747190735011898617445)
            ·
              refine ⟨3338202598262814730990771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17803747190735011898617445 3338202598262814730990771)
              ·
                refine ⟨5007303897394222096486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338202598262814730990771 5007303897394222096486157)
                ·
                  refine ⟨1877738961522833286182309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5007303897394222096486157 1877738961522833286182309)
                  ·
                    refine ⟨352076055285531241159183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1877738961522833286182309 352076055285531241159183)
                    ·
                      rfl

theorem cell23_2056997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_2056997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2056997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2056997 prefixEnd_2056997 := by exact prefixLift 2056997
  have htrace : WordTrace (prefixWord ++ tailWord_2056997) baseStart_2056997 baseEnd_2056997 := by
    simpa [prefixWord, tailWord_2056997, baseEnd_2056997] using wordTrace_append hprefix tailTrace_2056997
  have hstable : (prefixWord ++ tailWord_2056997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056997).length < 2 ^ (prefixWord ++ tailWord_2056997).sum := by decide
  have hdescent : baseEnd_2056997 < baseStart_2056997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057000 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2057000 : Nat := 118140960795 + 2057000 * 2 ^ 59
def prefixEnd_2057000 : Nat := 4983230072969 + 3 ^ 40 * 2057000 * 2
def baseEnd_2057000 : Nat := 1056229706298557211740035

theorem tailTrace_2057000 : CollatzResearch.WordTrace tailWord_2057000 prefixEnd_2057000 1056229706298557211740035 := by
  unfold tailWord_2057000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37512476773923891238040227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50016635698565188317386969 37512476773923891238040227)
  ·
    refine ⟨56268715160885836857060341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37512476773923891238040227 56268715160885836857060341)
    ·
      refine ⟨5275192046333047205349407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56268715160885836857060341 5275192046333047205349407)
      ·
        refine ⟨7912788069499570808024111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275192046333047205349407 7912788069499570808024111)
        ·
          refine ⟨11869182104249356212036167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7912788069499570808024111 11869182104249356212036167)
          ·
            refine ⟨17803773156374034318054251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869182104249356212036167 17803773156374034318054251)
            ·
              refine ⟨26705659734561051477081377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17803773156374034318054251 26705659734561051477081377)
              ·
                refine ⟨20029244800920788607811033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26705659734561051477081377 20029244800920788607811033)
                ·
                  refine ⟨15021933600690591455858275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20029244800920788607811033 15021933600690591455858275)
                  ·
                    refine ⟨22532900401035887183787413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15021933600690591455858275 22532900401035887183787413)
                    ·
                      refine ⟨1056229706298557211740035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22532900401035887183787413 1056229706298557211740035)
                      ·
                        rfl

theorem cell23_2057000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2057000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057000 prefixEnd_2057000 := by exact prefixLift 2057000
  have htrace : WordTrace (prefixWord ++ tailWord_2057000) baseStart_2057000 baseEnd_2057000 := by
    simpa [prefixWord, tailWord_2057000, baseEnd_2057000] using wordTrace_append hprefix tailTrace_2057000
  have hstable : (prefixWord ++ tailWord_2057000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057000).length < 2 ^ (prefixWord ++ tailWord_2057000).sum := by decide
  have hdescent : baseEnd_2057000 < baseStart_2057000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057020 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_2057020 : Nat := 118140960795 + 2057020 * 2 ^ 59
def prefixEnd_2057020 : Nat := 4983230072969 + 3 ^ 40 * 2057020 * 2
def baseEnd_2057020 : Nat := 1056239975911647133489943

theorem tailTrace_2057020 : CollatzResearch.WordTrace tailWord_2057020 prefixEnd_2057020 1056239975911647133489943 := by
  unfold tailWord_2057020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37512841503887662945904257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50017122005183550594539009 37512841503887662945904257)
  ·
    refine ⟨28134631127915747209428193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37512841503887662945904257 28134631127915747209428193)
    ·
      refine ⟨21100973345936810407071145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28134631127915747209428193 21100973345936810407071145)
      ·
        refine ⟨15825730009452607805303359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21100973345936810407071145 15825730009452607805303359)
        ·
          refine ⟨23738595014178911707955039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825730009452607805303359 23738595014178911707955039)
          ·
            refine ⟨35607892521268367561932559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738595014178911707955039 35607892521268367561932559)
            ·
              refine ⟨53411838781902551342898839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35607892521268367561932559 53411838781902551342898839)
              ·
                refine ⟨80117758172853827014348259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53411838781902551342898839 80117758172853827014348259)
                ·
                  refine ⟨120176637259280740521522389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80117758172853827014348259 120176637259280740521522389)
                  ·
                    refine ⟨2816639935764392355973181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 120176637259280740521522389 2816639935764392355973181)
                    ·
                      refine ⟨1056239975911647133489943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816639935764392355973181 1056239975911647133489943)
                      ·
                        rfl

theorem cell23_2057020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_2057020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057020 prefixEnd_2057020 := by exact prefixLift 2057020
  have htrace : WordTrace (prefixWord ++ tailWord_2057020) baseStart_2057020 baseEnd_2057020 := by
    simpa [prefixWord, tailWord_2057020, baseEnd_2057020] using wordTrace_append hprefix tailTrace_2057020
  have hstable : (prefixWord ++ tailWord_2057020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057020).length < 2 ^ (prefixWord ++ tailWord_2057020).sum := by decide
  have hdescent : baseEnd_2057020 < baseStart_2057020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057097 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_2057097 : Nat := 118140960795 + 2057097 * 2 ^ 59
def prefixEnd_2057097 : Nat := 4983230072969 + 3 ^ 40 * 2057097 * 2
def baseEnd_2057097 : Nat := 1056279513922043332227089

theorem tailTrace_2057097 : CollatzResearch.WordTrace tailWord_2057097 prefixEnd_2057097 1056279513922043332227089 := by
  unfold tailWord_2057097
  simp only [CollatzResearch.WordTrace]
  refine ⟨75028491428496368042361545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50018994285664245361574363 75028491428496368042361545)
  ·
    refine ⟨56271368571372276031771159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75028491428496368042361545 56271368571372276031771159)
    ·
      refine ⟨84407052857058414047656739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56271368571372276031771159 84407052857058414047656739)
      ·
        refine ⟨126610579285587621071485109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84407052857058414047656739 126610579285587621071485109)
        ·
          refine ⟨11869741808023839475451729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126610579285587621071485109 11869741808023839475451729)
          ·
            refine ⟨8902306356017879606588797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11869741808023839475451729 8902306356017879606588797)
            ·
              refine ⟨3338364883506704852470799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8902306356017879606588797 3338364883506704852470799)
              ·
                refine ⟨5007547325260057278706199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338364883506704852470799 5007547325260057278706199)
                ·
                  refine ⟨7511320987890085918059299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5007547325260057278706199 7511320987890085918059299)
                  ·
                    refine ⟨11266981481835128877088949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511320987890085918059299 11266981481835128877088949)
                    ·
                      refine ⟨1056279513922043332227089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11266981481835128877088949 1056279513922043332227089)
                      ·
                        rfl

theorem cell23_2057097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_2057097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057097 prefixEnd_2057097 := by exact prefixLift 2057097
  have htrace : WordTrace (prefixWord ++ tailWord_2057097) baseStart_2057097 baseEnd_2057097 := by
    simpa [prefixWord, tailWord_2057097, baseEnd_2057097] using wordTrace_append hprefix tailTrace_2057097
  have hstable : (prefixWord ++ tailWord_2057097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057097).length < 2 ^ (prefixWord ++ tailWord_2057097).sum := by decide
  have hdescent : baseEnd_2057097 < baseStart_2057097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057120 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2057120 : Nat := 118140960795 + 2057120 * 2 ^ 59
def prefixEnd_2057120 : Nat := 4983230072969 + 3 ^ 40 * 2057120 * 2
def baseEnd_2057120 : Nat := 1056291323977096742239483

theorem tailTrace_2057120 : CollatzResearch.WordTrace tailWord_2057120 prefixEnd_2057120 1056291323977096742239483 := by
  unfold tailWord_2057120
  simp only [CollatzResearch.WordTrace]
  refine ⟨37514665153706521485224407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50019553538275361980299209 37514665153706521485224407)
  ·
    refine ⟨56271997730559782227836611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37514665153706521485224407 56271997730559782227836611)
    ·
      refine ⟨84407996595839673341754917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56271997730559782227836611 84407996595839673341754917)
      ·
        refine ⟨15826499361719938751579047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84407996595839673341754917 15826499361719938751579047)
        ·
          refine ⟨23739749042579908127368571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15826499361719938751579047 23739749042579908127368571)
          ·
            refine ⟨35609623563869862191052857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739749042579908127368571 35609623563869862191052857)
            ·
              refine ⟨26707217672902396643289643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35609623563869862191052857 26707217672902396643289643)
              ·
                refine ⟨40060826509353594964934465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26707217672902396643289643 40060826509353594964934465)
                ·
                  refine ⟨30045619882015196223700849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40060826509353594964934465 30045619882015196223700849)
                  ·
                    refine ⟨22534214911511397167775637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30045619882015196223700849 22534214911511397167775637)
                    ·
                      refine ⟨1056291323977096742239483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22534214911511397167775637 1056291323977096742239483)
                      ·
                        rfl

theorem cell23_2057120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2057120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057120 prefixEnd_2057120 := by exact prefixLift 2057120
  have htrace : WordTrace (prefixWord ++ tailWord_2057120) baseStart_2057120 baseEnd_2057120 := by
    simpa [prefixWord, tailWord_2057120, baseEnd_2057120] using wordTrace_append hprefix tailTrace_2057120
  have hstable : (prefixWord ++ tailWord_2057120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057120).length < 2 ^ (prefixWord ++ tailWord_2057120).sum := by decide
  have hdescent : baseEnd_2057120 < baseStart_2057120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057142 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2057142 : Nat := 118140960795 + 2057142 * 2 ^ 59
def prefixEnd_2057142 : Nat := 4983230072969 + 3 ^ 40 * 2057142 * 2
def baseEnd_2057142 : Nat := 352100873517165218721461

theorem tailTrace_2057142 : CollatzResearch.WordTrace tailWord_2057142 prefixEnd_2057142 352100873517165218721461 := by
  unfold tailWord_2057142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689383294583333795484355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50020088475555560485166453 4689383294583333795484355)
  ·
    refine ⟨7034074941875000693226533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689383294583333795484355 7034074941875000693226533)
    ·
      refine ⟨1318889051601562629979975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7034074941875000693226533 1318889051601562629979975)
      ·
        refine ⟨1978333577402343944969963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318889051601562629979975 1978333577402343944969963)
        ·
          refine ⟨2967500366103515917454945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978333577402343944969963 2967500366103515917454945)
          ·
            refine ⟨2225625274577636938091209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967500366103515917454945 2225625274577636938091209)
            ·
              refine ⟨1669218955933227703568407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225625274577636938091209 1669218955933227703568407)
              ·
                refine ⟨2503828433899841555352611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669218955933227703568407 2503828433899841555352611)
                ·
                  refine ⟨3755742650849762333028917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503828433899841555352611 3755742650849762333028917)
                  ·
                    refine ⟨352100873517165218721461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3755742650849762333028917 352100873517165218721461)
                    ·
                      rfl

theorem cell23_2057142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2057142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057142 prefixEnd_2057142 := by exact prefixLift 2057142
  have htrace : WordTrace (prefixWord ++ tailWord_2057142) baseStart_2057142 baseEnd_2057142 := by
    simpa [prefixWord, tailWord_2057142, baseEnd_2057142] using wordTrace_append hprefix tailTrace_2057142
  have hstable : (prefixWord ++ tailWord_2057142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057142).length < 2 ^ (prefixWord ++ tailWord_2057142).sum := by decide
  have hdescent : baseEnd_2057142 < baseStart_2057142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057177 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_2057177 : Nat := 118140960795 + 2057177 * 2 ^ 59
def prefixEnd_2057177 : Nat := 4983230072969 + 3 ^ 40 * 2057177 * 2
def baseEnd_2057177 : Nat := 352106864124801006408907

theorem tailTrace_2057177 : CollatzResearch.WordTrace tailWord_2057177 prefixEnd_2057177 352106864124801006408907 := by
  unfold tailWord_2057177
  simp only [CollatzResearch.WordTrace]
  refine ⟨75031409268206541705273785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50020939512137694470182523 75031409268206541705273785)
  ·
    refine ⟨56273556951154906278955339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75031409268206541705273785 56273556951154906278955339)
    ·
      refine ⟨84410335426732359418433009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56273556951154906278955339 84410335426732359418433009)
      ·
        refine ⟨63307751570049269563824757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84410335426732359418433009 63307751570049269563824757)
        ·
          refine ⟨5935101709692119021608571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63307751570049269563824757 5935101709692119021608571)
          ·
            refine ⟨8902652564538178532412857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935101709692119021608571 8902652564538178532412857)
            ·
              refine ⟨6676989423403633899309643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8902652564538178532412857 6676989423403633899309643)
              ·
                refine ⟨10015484135105450848964465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676989423403633899309643 10015484135105450848964465)
                ·
                  refine ⟨7511613101329088136723349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015484135105450848964465 7511613101329088136723349)
                  ·
                    refine ⟨352106864124801006408907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7511613101329088136723349 352106864124801006408907)
                    ·
                      rfl

theorem cell23_2057177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_2057177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057177 prefixEnd_2057177 := by exact prefixLift 2057177
  have htrace : WordTrace (prefixWord ++ tailWord_2057177) baseStart_2057177 baseEnd_2057177 := by
    simpa [prefixWord, tailWord_2057177, baseEnd_2057177] using wordTrace_append hprefix tailTrace_2057177
  have hstable : (prefixWord ++ tailWord_2057177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057177).length < 2 ^ (prefixWord ++ tailWord_2057177).sum := by decide
  have hdescent : baseEnd_2057177 < baseStart_2057177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057178 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_2057178 : Nat := 118140960795 + 2057178 * 2 ^ 59
def prefixEnd_2057178 : Nat := 4983230072969 + 3 ^ 40 * 2057178 * 2
def baseEnd_2057178 : Nat := 1056321105855057515314217

theorem tailTrace_2057178 : CollatzResearch.WordTrace tailWord_2057178 prefixEnd_2057178 1056321105855057515314217 := by
  unfold tailWord_2057178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18757861435300729719015047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50020963827468612584040125 18757861435300729719015047)
  ·
    refine ⟨28136792152951094578522571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18757861435300729719015047 28136792152951094578522571)
    ·
      refine ⟨42205188229426641867783857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28136792152951094578522571 42205188229426641867783857)
      ·
        refine ⟨31653891172069981400837893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42205188229426641867783857 31653891172069981400837893)
        ·
          refine ⟨5935104594763121512657105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31653891172069981400837893 5935104594763121512657105)
          ·
            refine ⟨4451328446072341134492829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5935104594763121512657105 4451328446072341134492829)
            ·
              refine ⟨1669248167277127925434811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4451328446072341134492829 1669248167277127925434811)
              ·
                refine ⟨2503872250915691888152217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669248167277127925434811 2503872250915691888152217)
                ·
                  refine ⟨1877904188186768916114163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2503872250915691888152217 1877904188186768916114163)
                  ·
                    refine ⟨2816856282280153374171245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1877904188186768916114163 2816856282280153374171245)
                    ·
                      refine ⟨1056321105855057515314217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2816856282280153374171245 1056321105855057515314217)
                      ·
                        rfl

theorem cell23_2057178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_2057178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057178 prefixEnd_2057178 := by exact prefixLift 2057178
  have htrace : WordTrace (prefixWord ++ tailWord_2057178) baseStart_2057178 baseEnd_2057178 := by
    simpa [prefixWord, tailWord_2057178, baseEnd_2057178] using wordTrace_append hprefix tailTrace_2057178
  have hstable : (prefixWord ++ tailWord_2057178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057178).length < 2 ^ (prefixWord ++ tailWord_2057178).sum := by decide
  have hdescent : baseEnd_2057178 < baseStart_2057178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057187 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2057187 : Nat := 118140960795 + 2057187 * 2 ^ 59
def prefixEnd_2057187 : Nat := 4983230072969 + 3 ^ 40 * 2057187 * 2
def baseEnd_2057187 : Nat := 1056325727180947980101675

theorem tailTrace_2057187 : CollatzResearch.WordTrace tailWord_2057187 prefixEnd_2057187 1056325727180947980101675 := by
  unfold tailWord_2057187
  simp only [CollatzResearch.WordTrace]
  refine ⟨75031773998170313413137815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50021182665446875608758543 75031773998170313413137815)
  ·
    refine ⟨112547660997255470119706723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75031773998170313413137815 112547660997255470119706723)
    ·
      refine ⟨168821491495883205179560085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112547660997255470119706723 168821491495883205179560085)
      ·
        refine ⟨7913507413869525242791879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168821491495883205179560085 7913507413869525242791879)
        ·
          refine ⟨11870261120804287864187819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7913507413869525242791879 11870261120804287864187819)
          ·
            refine ⟨17805391681206431796281729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11870261120804287864187819 17805391681206431796281729)
            ·
              refine ⟨13354043760904823847211297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17805391681206431796281729 13354043760904823847211297)
              ·
                refine ⟨10015532820678617885408473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13354043760904823847211297 10015532820678617885408473)
                ·
                  refine ⟨7511649615508963414056355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10015532820678617885408473 7511649615508963414056355)
                  ·
                    refine ⟨11267474423263445121084533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511649615508963414056355 11267474423263445121084533)
                    ·
                      refine ⟨1056325727180947980101675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11267474423263445121084533 1056325727180947980101675)
                      ·
                        rfl

theorem cell23_2057187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2057187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057187 prefixEnd_2057187 := by exact prefixLift 2057187
  have htrace : WordTrace (prefixWord ++ tailWord_2057187) baseStart_2057187 baseEnd_2057187 := by
    simpa [prefixWord, tailWord_2057187, baseEnd_2057187] using wordTrace_append hprefix tailTrace_2057187
  have hstable : (prefixWord ++ tailWord_2057187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057187).length < 2 ^ (prefixWord ++ tailWord_2057187).sum := by decide
  have hdescent : baseEnd_2057187 < baseStart_2057187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057201 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_2057201 : Nat := 118140960795 + 2057201 * 2 ^ 59
def prefixEnd_2057201 : Nat := 4983230072969 + 3 ^ 40 * 2057201 * 2
def baseEnd_2057201 : Nat := 1056332915910110925326611

theorem tailTrace_2057201 : CollatzResearch.WordTrace tailWord_2057201 prefixEnd_2057201 1056332915910110925326611 := by
  unfold tailWord_2057201
  simp only [CollatzResearch.WordTrace]
  refine ⟨75032284620119593804147457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50021523080079729202764971 75032284620119593804147457)
  ·
    refine ⟨56274213465089695353110593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75032284620119593804147457 56274213465089695353110593)
    ·
      refine ⟨42205660098817271514832945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56274213465089695353110593 42205660098817271514832945)
      ·
        refine ⟨31654245074112953636124709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42205660098817271514832945 31654245074112953636124709)
        ·
          refine ⟨5935170951396178806773383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31654245074112953636124709 5935170951396178806773383)
          ·
            refine ⟨8902756427094268210160075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935170951396178806773383 8902756427094268210160075)
            ·
              refine ⟨13354134640641402315240113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902756427094268210160075 13354134640641402315240113)
              ·
                refine ⟨10015600980481051736430085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13354134640641402315240113 10015600980481051736430085)
                ·
                  refine ⟨1877925183840197200580641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10015600980481051736430085 1877925183840197200580641)
                  ·
                    refine ⟨1408443887880147900435481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1877925183840197200580641 1408443887880147900435481)
                    ·
                      refine ⟨1056332915910110925326611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408443887880147900435481 1056332915910110925326611)
                      ·
                        rfl

theorem cell23_2057201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_2057201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057201 prefixEnd_2057201 := by exact prefixLift 2057201
  have htrace : WordTrace (prefixWord ++ tailWord_2057201) baseStart_2057201 baseEnd_2057201 := by
    simpa [prefixWord, tailWord_2057201, baseEnd_2057201] using wordTrace_append hprefix tailTrace_2057201
  have hstable : (prefixWord ++ tailWord_2057201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057201).length < 2 ^ (prefixWord ++ tailWord_2057201).sum := by decide
  have hdescent : baseEnd_2057201 < baseStart_2057201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057224 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 7]
def baseStart_2057224 : Nat := 118140960795 + 2057224 * 2 ^ 59
def prefixEnd_2057224 : Nat := 4983230072969 + 3 ^ 40 * 2057224 * 2
def baseEnd_2057224 : Nat := 117371636218351592815445

theorem tailTrace_2057224 : CollatzResearch.WordTrace tailWord_2057224 prefixEnd_2057224 117371636218351592815445 := by
  unfold tailWord_2057224
  simp only [CollatzResearch.WordTrace]
  refine ⟨37516561749518134366117363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50022082332690845821489817 37516561749518134366117363)
  ·
    refine ⟨56274842624277201549176045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37516561749518134366117363 56274842624277201549176045)
    ·
      refine ⟨21103065984103950580941017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56274842624277201549176045 21103065984103950580941017)
      ·
        refine ⟨15827299488077962935705763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21103065984103950580941017 15827299488077962935705763)
        ·
          refine ⟨23740949232116944403558645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15827299488077962935705763 23740949232116944403558645)
          ·
            refine ⟨2225713990510963537833623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23740949232116944403558645 2225713990510963537833623)
            ·
              refine ⟨3338570985766445306750435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2225713990510963537833623 3338570985766445306750435)
              ·
                refine ⟨5007856478649667960125653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338570985766445306750435 5007856478649667960125653)
                ·
                  refine ⟨117371636218351592815445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5007856478649667960125653 117371636218351592815445)
                  ·
                    rfl

theorem cell23_2057224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_2057224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057224 prefixEnd_2057224 := by exact prefixLift 2057224
  have htrace : WordTrace (prefixWord ++ tailWord_2057224) baseStart_2057224 baseEnd_2057224 := by
    simpa [prefixWord, tailWord_2057224, baseEnd_2057224] using wordTrace_append hprefix tailTrace_2057224
  have hstable : (prefixWord ++ tailWord_2057224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057224).length < 2 ^ (prefixWord ++ tailWord_2057224).sum := by decide
  have hdescent : baseEnd_2057224 < baseStart_2057224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057274 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_2057274 : Nat := 118140960795 + 2057274 * 2 ^ 59
def prefixEnd_2057274 : Nat := 4983230072969 + 3 ^ 40 * 2057274 * 2
def baseEnd_2057274 : Nat := 1056370399997889139713775

theorem tailTrace_2057274 : CollatzResearch.WordTrace tailWord_2057274 prefixEnd_2057274 1056370399997889139713775 := by
  unfold tailWord_2057274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758736787213781817888719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50023298099236751514369917 18758736787213781817888719)
  ·
    refine ⟨28138105180820672726833079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18758736787213781817888719 28138105180820672726833079)
    ·
      refine ⟨42207157771231009090249619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28138105180820672726833079 42207157771231009090249619)
      ·
        refine ⟨63310736656846513635374429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42207157771231009090249619 63310736656846513635374429)
        ·
          refine ⟨23741526246317442613265411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63310736656846513635374429 23741526246317442613265411)
          ·
            refine ⟨35612289369476163919898117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23741526246317442613265411 35612289369476163919898117)
            ·
              refine ⟨6677304256776780734980897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35612289369476163919898117 6677304256776780734980897)
              ·
                refine ⟨5007978192582585551235673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677304256776780734980897 5007978192582585551235673)
                ·
                  refine ⟨3755983644436939163426755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5007978192582585551235673 3755983644436939163426755)
                  ·
                    refine ⟨5633975466655408745140133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755983644436939163426755 5633975466655408745140133)
                    ·
                      refine ⟨1056370399997889139713775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5633975466655408745140133 1056370399997889139713775)
                      ·
                        rfl

theorem cell23_2057274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_2057274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057274 prefixEnd_2057274 := by exact prefixLift 2057274
  have htrace : WordTrace (prefixWord ++ tailWord_2057274) baseStart_2057274 baseEnd_2057274 := by
    simpa [prefixWord, tailWord_2057274, baseEnd_2057274] using wordTrace_append hprefix tailTrace_2057274
  have hstable : (prefixWord ++ tailWord_2057274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057274).length < 2 ^ (prefixWord ++ tailWord_2057274).sum := by decide
  have hdescent : baseEnd_2057274 < baseStart_2057274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057294 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_2057294 : Nat := 118140960795 + 2057294 * 2 ^ 59
def prefixEnd_2057294 : Nat := 4983230072969 + 3 ^ 40 * 2057294 * 2
def baseEnd_2057294 : Nat := 1056380669610979061463683

theorem tailTrace_2057294 : CollatzResearch.WordTrace tailWord_2057294 prefixEnd_2057294 1056380669610979061463683 := by
  unfold tailWord_2057294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379459576097833835910367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50023784405855113791521957 9379459576097833835910367)
  ·
    refine ⟨14069189364146750753865551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9379459576097833835910367 14069189364146750753865551)
    ·
      refine ⟨21103784046220126130798327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14069189364146750753865551 21103784046220126130798327)
      ·
        refine ⟨31655676069330189196197491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103784046220126130798327 31655676069330189196197491)
        ·
          refine ⟨47483514103995283794296237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31655676069330189196197491 47483514103995283794296237)
          ·
            refine ⟨17806317788998231422861089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47483514103995283794296237 17806317788998231422861089)
            ·
              refine ⟨13354738341748673567145817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17806317788998231422861089 13354738341748673567145817)
              ·
                refine ⟨10016053756311505175359363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13354738341748673567145817 10016053756311505175359363)
                ·
                  refine ⟨15024080634467257763039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016053756311505175359363 15024080634467257763039045)
                  ·
                    refine ⟨2817015118962610830569821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15024080634467257763039045 2817015118962610830569821)
                    ·
                      refine ⟨1056380669610979061463683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817015118962610830569821 1056380669610979061463683)
                      ·
                        rfl

theorem cell23_2057294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_2057294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057294 prefixEnd_2057294 := by exact prefixLift 2057294
  have htrace : WordTrace (prefixWord ++ tailWord_2057294) baseStart_2057294 baseEnd_2057294 := by
    simpa [prefixWord, tailWord_2057294, baseEnd_2057294] using wordTrace_append hprefix tailTrace_2057294
  have hstable : (prefixWord ++ tailWord_2057294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057294).length < 2 ^ (prefixWord ++ tailWord_2057294).sum := by decide
  have hdescent : baseEnd_2057294 < baseStart_2057294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057334 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2057334 : Nat := 118140960795 + 2057334 * 2 ^ 59
def prefixEnd_2057334 : Nat := 4983230072969 + 3 ^ 40 * 2057334 * 2
def baseEnd_2057334 : Nat := 1056401208837158904963499

theorem tailTrace_2057334 : CollatzResearch.WordTrace tailWord_2057334 prefixEnd_2057334 1056401208837158904963499 := by
  unfold tailWord_2057334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689820970539859844921191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50024757019091838345826037 4689820970539859844921191)
  ·
    refine ⟨7034731455809789767381787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4689820970539859844921191 7034731455809789767381787)
    ·
      refine ⟨10552097183714684651072681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7034731455809789767381787 10552097183714684651072681)
      ·
        refine ⟨7914072887786013488304511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10552097183714684651072681 7914072887786013488304511)
        ·
          refine ⟨11871109331679020232456767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7914072887786013488304511 11871109331679020232456767)
          ·
            refine ⟨17806663997518530348685151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11871109331679020232456767 17806663997518530348685151)
            ·
              refine ⟨26709995996277795523027727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17806663997518530348685151 26709995996277795523027727)
              ·
                refine ⟨40064993994416693284541591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26709995996277795523027727 40064993994416693284541591)
                ·
                  refine ⟨60097490991625039926812387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40064993994416693284541591 60097490991625039926812387)
                  ·
                    refine ⟨90146236487437559890218581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60097490991625039926812387 90146236487437559890218581)
                    ·
                      refine ⟨1056401208837158904963499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90146236487437559890218581 1056401208837158904963499)
                      ·
                        rfl

theorem cell23_2057334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2057334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057334 prefixEnd_2057334 := by exact prefixLift 2057334
  have htrace : WordTrace (prefixWord ++ tailWord_2057334) baseStart_2057334 baseEnd_2057334 := by
    simpa [prefixWord, tailWord_2057334, baseEnd_2057334] using wordTrace_append hprefix tailTrace_2057334
  have hstable : (prefixWord ++ tailWord_2057334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057334).length < 2 ^ (prefixWord ++ tailWord_2057334).sum := by decide
  have hdescent : baseEnd_2057334 < baseStart_2057334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057358 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2057358 : Nat := 118140960795 + 2057358 * 2 ^ 59
def prefixEnd_2057358 : Nat := 4983230072969 + 3 ^ 40 * 2057358 * 2
def baseEnd_2057358 : Nat := 1056413532372866811063389

theorem tailTrace_2057358 : CollatzResearch.WordTrace tailWord_2057358 prefixEnd_2057358 1056413532372866811063389 := by
  unfold tailWord_2057358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9379751360068851202201591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50025340587033873078408485 9379751360068851202201591)
  ·
    refine ⟨14069627040103276803302387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9379751360068851202201591 14069627040103276803302387)
    ·
      refine ⟨21104440560154915204953581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14069627040103276803302387 21104440560154915204953581)
      ·
        refine ⟨7914165210058093201857593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21104440560154915204953581 7914165210058093201857593)
        ·
          refine ⟨5935623907543569901393195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7914165210058093201857593 5935623907543569901393195)
          ·
            refine ⟨8903435861315354852089793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935623907543569901393195 8903435861315354852089793)
            ·
              refine ⟨6677576895986516139067345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903435861315354852089793 6677576895986516139067345)
              ·
                refine ⟨5008182671989887104300509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677576895986516139067345 5008182671989887104300509)
                ·
                  refine ⟨1878068501996207664112691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5008182671989887104300509 1878068501996207664112691)
                  ·
                    refine ⟨2817102752994311496169037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1878068501996207664112691 2817102752994311496169037)
                    ·
                      refine ⟨1056413532372866811063389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817102752994311496169037 1056413532372866811063389)
                      ·
                        rfl

theorem cell23_2057358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2057358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057358 prefixEnd_2057358 := by exact prefixLift 2057358
  have htrace : WordTrace (prefixWord ++ tailWord_2057358) baseStart_2057358 baseEnd_2057358 := by
    simpa [prefixWord, tailWord_2057358, baseEnd_2057358] using wordTrace_append hprefix tailTrace_2057358
  have hstable : (prefixWord ++ tailWord_2057358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057358).length < 2 ^ (prefixWord ++ tailWord_2057358).sum := by decide
  have hdescent : baseEnd_2057358 < baseStart_2057358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057381 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_2057381 : Nat := 118140960795 + 2057381 * 2 ^ 59
def prefixEnd_2057381 : Nat := 4983230072969 + 3 ^ 40 * 2057381 * 2
def baseEnd_2057381 : Nat := 1056425342427920221075783

theorem tailTrace_2057381 : CollatzResearch.WordTrace tailWord_2057381 prefixEnd_2057381 1056425342427920221075783 := by
  unfold tailWord_2057381
  simp only [CollatzResearch.WordTrace]
  refine ⟨75038849759467484545699997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50025899839644989697133331 75038849759467484545699997)
  ·
    refine ⟨28139568659800306704637499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75038849759467484545699997 28139568659800306704637499)
    ·
      refine ⟨42209352989700460056956249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28139568659800306704637499 42209352989700460056956249)
      ·
        refine ⟨31657014742275345042717187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42209352989700460056956249 31657014742275345042717187)
        ·
          refine ⟨47485522113413017564075781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31657014742275345042717187 47485522113413017564075781)
          ·
            refine ⟨8903535396264940793264209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47485522113413017564075781 8903535396264940793264209)
            ·
              refine ⟨6677651547198705594948157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903535396264940793264209 6677651547198705594948157)
              ·
                refine ⟨2504119330199514598105559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6677651547198705594948157 2504119330199514598105559)
                ·
                  refine ⟨3756178995299271897158339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504119330199514598105559 3756178995299271897158339)
                  ·
                    refine ⟨5634268492948907845737509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3756178995299271897158339 5634268492948907845737509)
                    ·
                      refine ⟨1056425342427920221075783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5634268492948907845737509 1056425342427920221075783)
                      ·
                        rfl

theorem cell23_2057381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_2057381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057381 prefixEnd_2057381 := by exact prefixLift 2057381
  have htrace : WordTrace (prefixWord ++ tailWord_2057381) baseStart_2057381 baseEnd_2057381 := by
    simpa [prefixWord, tailWord_2057381, baseEnd_2057381] using wordTrace_append hprefix tailTrace_2057381
  have hstable : (prefixWord ++ tailWord_2057381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057381).length < 2 ^ (prefixWord ++ tailWord_2057381).sum := by decide
  have hdescent : baseEnd_2057381 < baseStart_2057381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057394 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2057394 : Nat := 118140960795 + 2057394 * 2 ^ 59
def prefixEnd_2057394 : Nat := 4983230072969 + 3 ^ 40 * 2057394 * 2
def baseEnd_2057394 : Nat := 1056432017676428670213223

theorem tailTrace_2057394 : CollatzResearch.WordTrace tailWord_2057394 prefixEnd_2057394 1056432017676428670213223 := by
  unfold tailWord_2057394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18759830977105096941480809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50026215938946925177282157 18759830977105096941480809)
  ·
    refine ⟨14069873232828822706110607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18759830977105096941480809 14069873232828822706110607)
    ·
      refine ⟨21104809849243234059165911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14069873232828822706110607 21104809849243234059165911)
      ·
        refine ⟨31657214773864851088748867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21104809849243234059165911 31657214773864851088748867)
        ·
          refine ⟨47485822160797276633123301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31657214773864851088748867 47485822160797276633123301)
          ·
            refine ⟨8903591655149489368710619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47485822160797276633123301 8903591655149489368710619)
            ·
              refine ⟨13355387482724234053065929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903591655149489368710619 13355387482724234053065929)
              ·
                refine ⟨10016540612043175539799447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13355387482724234053065929 10016540612043175539799447)
                ·
                  refine ⟨15024810918064763309699171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10016540612043175539799447 15024810918064763309699171)
                  ·
                    refine ⟨22537216377097144964548757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15024810918064763309699171 22537216377097144964548757)
                    ·
                      refine ⟨1056432017676428670213223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22537216377097144964548757 1056432017676428670213223)
                      ·
                        rfl

theorem cell23_2057394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2057394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057394 prefixEnd_2057394 := by exact prefixLift 2057394
  have htrace : WordTrace (prefixWord ++ tailWord_2057394) baseStart_2057394 baseEnd_2057394 := by
    simpa [prefixWord, tailWord_2057394, baseEnd_2057394] using wordTrace_append hprefix tailTrace_2057394
  have hstable : (prefixWord ++ tailWord_2057394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057394).length < 2 ^ (prefixWord ++ tailWord_2057394).sum := by decide
  have hdescent : baseEnd_2057394 < baseStart_2057394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057404 : List Nat := [2, 2, 2, 3, 2, 1, 1, 10]
def baseStart_2057404 : Nat := 118140960795 + 2057404 * 2 ^ 59
def prefixEnd_2057404 : Nat := 4983230072969 + 3 ^ 40 * 2057404 * 2
def baseEnd_2057404 : Nat := 39127301943813838188451

theorem tailTrace_2057404 : CollatzResearch.WordTrace tailWord_2057404 prefixEnd_2057404 39127301943813838188451 := by
  unfold tailWord_2057404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519844319192079736893633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50026459092256106315858177 37519844319192079736893633)
  ·
    refine ⟨28139883239394059802670225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37519844319192079736893633 28139883239394059802670225)
    ·
      refine ⟨21104912429545544852002669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28139883239394059802670225 21104912429545544852002669)
      ·
        refine ⟨7914342161079579319501001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21104912429545544852002669 7914342161079579319501001)
        ·
          refine ⟨5935756620809684489625751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7914342161079579319501001 5935756620809684489625751)
          ·
            refine ⟨8903634931214526734438627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5935756620809684489625751 8903634931214526734438627)
            ·
              refine ⟨13355452396821790101657941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903634931214526734438627 13355452396821790101657941)
              ·
                refine ⟨39127301943813838188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13355452396821790101657941 39127301943813838188451)
                ·
                  rfl

theorem cell23_2057404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 10].length) (baseStart_2057404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057404 prefixEnd_2057404 := by exact prefixLift 2057404
  have htrace : WordTrace (prefixWord ++ tailWord_2057404) baseStart_2057404 baseEnd_2057404 := by
    simpa [prefixWord, tailWord_2057404, baseEnd_2057404] using wordTrace_append hprefix tailTrace_2057404
  have hstable : (prefixWord ++ tailWord_2057404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057404).length < 2 ^ (prefixWord ++ tailWord_2057404).sum := by decide
  have hdescent : baseEnd_2057404 < baseStart_2057404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057408 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_2057408 : Nat := 118140960795 + 2057408 * 2 ^ 59
def prefixEnd_2057408 : Nat := 4983230072969 + 3 ^ 40 * 2057408 * 2
def baseEnd_2057408 : Nat := 352146402135197205146053

theorem tailTrace_2057408 : CollatzResearch.WordTrace tailWord_2057408 prefixEnd_2057408 352146402135197205146053 := by
  unfold tailWord_2057408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37519917265184834078466439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50026556353579778771288585 37519917265184834078466439)
  ·
    refine ⟨56279875897777251117699659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37519917265184834078466439 56279875897777251117699659)
    ·
      refine ⟨84419813846665876676549489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56279875897777251117699659 84419813846665876676549489)
      ·
        refine ⟨63314860384999407507412117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84419813846665876676549489 63314860384999407507412117)
        ·
          refine ⟨2967884080546847226909943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63314860384999407507412117 2967884080546847226909943)
          ·
            refine ⟨4451826120820270840364915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967884080546847226909943 4451826120820270840364915)
            ·
              refine ⟨6677739181230406260547373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451826120820270840364915 6677739181230406260547373)
              ·
                refine ⟨2504152192961402347705265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6677739181230406260547373 2504152192961402347705265)
                ·
                  refine ⟨1878114144721051760778949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2504152192961402347705265 1878114144721051760778949)
                  ·
                    refine ⟨352146402135197205146053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878114144721051760778949 352146402135197205146053)
                    ·
                      rfl

theorem cell23_2057408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_2057408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057408 prefixEnd_2057408 := by exact prefixLift 2057408
  have htrace : WordTrace (prefixWord ++ tailWord_2057408) baseStart_2057408 baseEnd_2057408 := by
    simpa [prefixWord, tailWord_2057408, baseEnd_2057408] using wordTrace_append hprefix tailTrace_2057408
  have hstable : (prefixWord ++ tailWord_2057408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057408).length < 2 ^ (prefixWord ++ tailWord_2057408).sum := by decide
  have hdescent : baseEnd_2057408 < baseStart_2057408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057418 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2057418 : Nat := 118140960795 + 2057418 * 2 ^ 59
def prefixEnd_2057418 : Nat := 4983230072969 + 3 ^ 40 * 2057418 * 2
def baseEnd_2057418 : Nat := 1056444341212136576313113

theorem tailTrace_2057418 : CollatzResearch.WordTrace tailWord_2057418 prefixEnd_2057418 1056444341212136576313113 := by
  unfold tailWord_2057418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18760049815083359966199227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50026799506888959909864605 18760049815083359966199227)
  ·
    refine ⟨28140074722625039949298841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18760049815083359966199227 28140074722625039949298841)
    ·
      refine ⟨21105056041968779961974131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28140074722625039949298841 21105056041968779961974131)
      ·
        refine ⟨31657584062953169942961197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105056041968779961974131 31657584062953169942961197)
        ·
          refine ⟨11871594023607438728610449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31657584062953169942961197 11871594023607438728610449)
          ·
            refine ⟨8903695517705579046457837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11871594023607438728610449 8903695517705579046457837)
            ·
              refine ⟨3338885819139592142421689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8903695517705579046457837 3338885819139592142421689)
              ·
                refine ⟨2504164364354694106816267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338885819139592142421689 2504164364354694106816267)
                ·
                  refine ⟨3756246546532041160224401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504164364354694106816267 3756246546532041160224401)
                  ·
                    refine ⟨2817184909899030870168301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3756246546532041160224401 2817184909899030870168301)
                    ·
                      refine ⟨1056444341212136576313113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817184909899030870168301 1056444341212136576313113)
                      ·
                        rfl

theorem cell23_2057418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2057418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057418 prefixEnd_2057418 := by exact prefixLift 2057418
  have htrace : WordTrace (prefixWord ++ tailWord_2057418) baseStart_2057418 baseEnd_2057418 := by
    simpa [prefixWord, tailWord_2057418, baseEnd_2057418] using wordTrace_append hprefix tailTrace_2057418
  have hstable : (prefixWord ++ tailWord_2057418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057418).length < 2 ^ (prefixWord ++ tailWord_2057418).sum := by decide
  have hdescent : baseEnd_2057418 < baseStart_2057418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057431 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_2057431 : Nat := 118140960795 + 2057431 * 2 ^ 59
def prefixEnd_2057431 : Nat := 4983230072969 + 3 ^ 40 * 2057431 * 2
def baseEnd_2057431 : Nat := 1056451016460645025450553

theorem tailTrace_2057431 : CollatzResearch.WordTrace tailWord_2057431 prefixEnd_2057431 1056451016460645025450553 := by
  unfold tailWord_2057431
  simp only [CollatzResearch.WordTrace]
  refine ⟨75040673409286343085020147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50027115606190895390013431 75040673409286343085020147)
  ·
    refine ⟨112561010113929514627530221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75040673409286343085020147 112561010113929514627530221)
    ·
      refine ⟨42210378792723567985323833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112561010113929514627530221 42210378792723567985323833)
      ·
        refine ⟨31657784094542675988992875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42210378792723567985323833 31657784094542675988992875)
        ·
          refine ⟨47486676141814013983489313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31657784094542675988992875 47486676141814013983489313)
          ·
            refine ⟨35615007106360510487616985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47486676141814013983489313 35615007106360510487616985)
            ·
              refine ⟨26711255329770382865712739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35615007106360510487616985 26711255329770382865712739)
              ·
                refine ⟨40066882994655574298569109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26711255329770382865712739 40066882994655574298569109)
                ·
                  refine ⟨1878135140374480045245427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40066882994655574298569109 1878135140374480045245427)
                  ·
                    refine ⟨2817202710561720067868141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1878135140374480045245427 2817202710561720067868141)
                    ·
                      refine ⟨1056451016460645025450553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817202710561720067868141 1056451016460645025450553)
                      ·
                        rfl

theorem cell23_2057431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_2057431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057431 prefixEnd_2057431 := by exact prefixLift 2057431
  have htrace : WordTrace (prefixWord ++ tailWord_2057431) baseStart_2057431 baseEnd_2057431 := by
    simpa [prefixWord, tailWord_2057431, baseEnd_2057431] using wordTrace_append hprefix tailTrace_2057431
  have hstable : (prefixWord ++ tailWord_2057431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057431).length < 2 ^ (prefixWord ++ tailWord_2057431).sum := by decide
  have hdescent : baseEnd_2057431 < baseStart_2057431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057444 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2057444 : Nat := 118140960795 + 2057444 * 2 ^ 59
def prefixEnd_2057444 : Nat := 4983230072969 + 3 ^ 40 * 2057444 * 2
def baseEnd_2057444 : Nat := 1056457691709153474587993

theorem tailTrace_2057444 : CollatzResearch.WordTrace tailWord_2057444 prefixEnd_2057444 1056457691709153474587993 := by
  unfold tailWord_2057444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37520573779119623152621693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50027431705492830870162257 37520573779119623152621693)
  ·
    refine ⟨14070215167169858682233135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37520573779119623152621693 14070215167169858682233135)
    ·
      refine ⟨21105322750754788023349703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14070215167169858682233135 21105322750754788023349703)
      ·
        refine ⟨31657984126132182035024555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21105322750754788023349703 31657984126132182035024555)
        ·
          refine ⟨47486976189198273052536833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31657984126132182035024555 47486976189198273052536833)
          ·
            refine ⟨35615232141898704789402625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47486976189198273052536833 35615232141898704789402625)
            ·
              refine ⟨26711424106424028592051969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35615232141898704789402625 26711424106424028592051969)
              ·
                refine ⟨20033568079818021444038977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26711424106424028592051969 20033568079818021444038977)
                ·
                  refine ⟨15025176059863516083029233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20033568079818021444038977 15025176059863516083029233)
                  ·
                    refine ⟨11268882044897637062271925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15025176059863516083029233 11268882044897637062271925)
                    ·
                      refine ⟨1056457691709153474587993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11268882044897637062271925 1056457691709153474587993)
                      ·
                        rfl

theorem cell23_2057444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2057444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057444 prefixEnd_2057444 := by exact prefixLift 2057444
  have htrace : WordTrace (prefixWord ++ tailWord_2057444) baseStart_2057444 baseEnd_2057444 := by
    simpa [prefixWord, tailWord_2057444, baseEnd_2057444] using wordTrace_append hprefix tailTrace_2057444
  have hstable : (prefixWord ++ tailWord_2057444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057444).length < 2 ^ (prefixWord ++ tailWord_2057444).sum := by decide
  have hdescent : baseEnd_2057444 < baseStart_2057444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057531 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 7, 2]
def baseStart_2057531 : Nat := 118140960795 + 2057531 * 2 ^ 59
def prefixEnd_2057531 : Nat := 4983230072969 + 3 ^ 40 * 2057531 * 2
def baseEnd_2057531 : Nat := 1056502364526094634200093

theorem tailTrace_2057531 : CollatzResearch.WordTrace tailWord_2057531 prefixEnd_2057531 1056502364526094634200093 := by
  unfold tailWord_2057531
  simp only [CollatzResearch.WordTrace]
  refine ⟨75044320708924060163660447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50029547139282706775773631 75044320708924060163660447)
  ·
    refine ⟨112566481063386090245490671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75044320708924060163660447 112566481063386090245490671)
    ·
      refine ⟨168849721595079135368236007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112566481063386090245490671 168849721595079135368236007)
      ·
        refine ⟨253274582392618703052354011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168849721595079135368236007 253274582392618703052354011)
        ·
          refine ⟨379911873588928054578531017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253274582392618703052354011 379911873588928054578531017)
          ·
            refine ⟨284933905191696040933898263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379911873588928054578531017 284933905191696040933898263)
            ·
              refine ⟨427400857787544061400847395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284933905191696040933898263 427400857787544061400847395)
              ·
                refine ⟨641101286681316092101271093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427400857787544061400847395 641101286681316092101271093)
                ·
                  refine ⟨60103245626373383634494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641101286681316092101271093 60103245626373383634494165)
                  ·
                    refine ⟨1408669819368126178933457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60103245626373383634494165 1408669819368126178933457)
                    ·
                      refine ⟨1056502364526094634200093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408669819368126178933457 1056502364526094634200093)
                      ·
                        rfl

theorem cell23_2057531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 7, 2].length) (baseStart_2057531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057531 prefixEnd_2057531 := by exact prefixLift 2057531
  have htrace : WordTrace (prefixWord ++ tailWord_2057531) baseStart_2057531 baseEnd_2057531 := by
    simpa [prefixWord, tailWord_2057531, baseEnd_2057531] using wordTrace_append hprefix tailTrace_2057531
  have hstable : (prefixWord ++ tailWord_2057531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057531).length < 2 ^ (prefixWord ++ tailWord_2057531).sum := by decide
  have hdescent : baseEnd_2057531 < baseStart_2057531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057542 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2057542 : Nat := 118140960795 + 2057542 * 2 ^ 59
def prefixEnd_2057542 : Nat := 4983230072969 + 3 ^ 40 * 2057542 * 2
def baseEnd_2057542 : Nat := 1056508012813294091162543

theorem tailTrace_2057542 : CollatzResearch.WordTrace tailWord_2057542 prefixEnd_2057542 1056508012813294091162543 := by
  unfold tailWord_2057542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345147559746381532572215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50029814607922806028207253 2345147559746381532572215)
  ·
    refine ⟨3517721339619572298858323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2345147559746381532572215 3517721339619572298858323)
    ·
      refine ⟨5276582009429358448287485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517721339619572298858323 5276582009429358448287485)
      ·
        refine ⟨1978718253536009418107807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5276582009429358448287485 1978718253536009418107807)
        ·
          refine ⟨2968077380304014127161711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978718253536009418107807 2968077380304014127161711)
          ·
            refine ⟨4452116070456021190742567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968077380304014127161711 4452116070456021190742567)
            ·
              refine ⟨6678174105684031786113851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452116070456021190742567 6678174105684031786113851)
              ·
                refine ⟨10017261158526047679170777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678174105684031786113851 10017261158526047679170777)
                ·
                  refine ⟨7512945868894535759378083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10017261158526047679170777 7512945868894535759378083)
                  ·
                    refine ⟨11269418803341803639067125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7512945868894535759378083 11269418803341803639067125)
                    ·
                      refine ⟨1056508012813294091162543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11269418803341803639067125 1056508012813294091162543)
                      ·
                        rfl

theorem cell23_2057542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2057542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057542 prefixEnd_2057542 := by exact prefixLift 2057542
  have htrace : WordTrace (prefixWord ++ tailWord_2057542) baseStart_2057542 baseEnd_2057542 := by
    simpa [prefixWord, tailWord_2057542, baseEnd_2057542] using wordTrace_append hprefix tailTrace_2057542
  have hstable : (prefixWord ++ tailWord_2057542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057542).length < 2 ^ (prefixWord ++ tailWord_2057542).sum := by decide
  have hdescent : baseEnd_2057542 < baseStart_2057542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057561 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_2057561 : Nat := 118140960795 + 2057561 * 2 ^ 59
def prefixEnd_2057561 : Nat := 4983230072969 + 3 ^ 40 * 2057561 * 2
def baseEnd_2057561 : Nat := 1056517768945729516824955

theorem tailTrace_2057561 : CollatzResearch.WordTrace tailWord_2057561 prefixEnd_2057561 1056517768945729516824955 := by
  unfold tailWord_2057561
  simp only [CollatzResearch.WordTrace]
  refine ⟨75045414898815375287252537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50030276599210250191501691 75045414898815375287252537)
  ·
    refine ⟨56284061174111531465439403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75045414898815375287252537 56284061174111531465439403)
    ·
      refine ⟨84426091761167297198159105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56284061174111531465439403 84426091761167297198159105)
      ·
        refine ⟨63319568820875472898619329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84426091761167297198159105 63319568820875472898619329)
        ·
          refine ⟨47489676615656604673964497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63319568820875472898619329 47489676615656604673964497)
          ·
            refine ⟨35617257461742453505473373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47489676615656604673964497 35617257461742453505473373)
            ·
              refine ⟨13356471548153420064552515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35617257461742453505473373 13356471548153420064552515)
              ·
                refine ⟨20034707322230130096828773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13356471548153420064552515 20034707322230130096828773)
                ·
                  refine ⟨3756507622918149393155395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20034707322230130096828773 3756507622918149393155395)
                  ·
                    refine ⟨5634761434377224089733093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3756507622918149393155395 5634761434377224089733093)
                    ·
                      refine ⟨1056517768945729516824955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5634761434377224089733093 1056517768945729516824955)
                      ·
                        rfl

theorem cell23_2057561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_2057561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057561 prefixEnd_2057561 := by exact prefixLift 2057561
  have htrace : WordTrace (prefixWord ++ tailWord_2057561) baseStart_2057561 baseEnd_2057561 := by
    simpa [prefixWord, tailWord_2057561, baseEnd_2057561] using wordTrace_append hprefix tailTrace_2057561
  have hstable : (prefixWord ++ tailWord_2057561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057561).length < 2 ^ (prefixWord ++ tailWord_2057561).sum := by decide
  have hdescent : baseEnd_2057561 < baseStart_2057561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057681 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_2057681 : Nat := 118140960795 + 2057681 * 2 ^ 59
def prefixEnd_2057681 : Nat := 4983230072969 + 3 ^ 40 * 2057681 * 2
def baseEnd_2057681 : Nat := 1056579386624269047324403

theorem tailTrace_2057681 : CollatzResearch.WordTrace tailWord_2057681 prefixEnd_2057681 1056579386624269047324403 := by
  unfold tailWord_2057681
  simp only [CollatzResearch.WordTrace]
  refine ⟨75049791658380635781620897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50033194438920423854413931 75049791658380635781620897)
  ·
    refine ⟨56287343743785476836215673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75049791658380635781620897 56287343743785476836215673)
    ·
      refine ⟨42215507807839107627161755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56287343743785476836215673 42215507807839107627161755)
      ·
        refine ⟨63323261711758661440742633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42215507807839107627161755 63323261711758661440742633)
        ·
          refine ⟨47492446283818996080556975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63323261711758661440742633 47492446283818996080556975)
          ·
            refine ⟨71238669425728494120835463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47492446283818996080556975 71238669425728494120835463)
            ·
              refine ⟨106858004138592741181253195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71238669425728494120835463 106858004138592741181253195)
              ·
                refine ⟨160287006207889111771879793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106858004138592741181253195 160287006207889111771879793)
                ·
                  refine ⟨120215254655916833828909845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160287006207889111771879793 120215254655916833828909845)
                  ·
                    refine ⟨5635090061996101585730149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120215254655916833828909845 5635090061996101585730149)
                    ·
                      refine ⟨1056579386624269047324403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5635090061996101585730149 1056579386624269047324403)
                      ·
                        rfl

theorem cell23_2057681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_2057681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057681 prefixEnd_2057681 := by exact prefixLift 2057681
  have htrace : WordTrace (prefixWord ++ tailWord_2057681) baseStart_2057681 baseEnd_2057681 := by
    simpa [prefixWord, tailWord_2057681, baseEnd_2057681] using wordTrace_append hprefix tailTrace_2057681
  have hstable : (prefixWord ++ tailWord_2057681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057681).length < 2 ^ (prefixWord ++ tailWord_2057681).sum := by decide
  have hdescent : baseEnd_2057681 < baseStart_2057681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057688 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2057688 : Nat := 118140960795 + 2057688 * 2 ^ 59
def prefixEnd_2057688 : Nat := 4983230072969 + 3 ^ 40 * 2057688 * 2
def baseEnd_2057688 : Nat := 1056582980988850519936871

theorem tailTrace_2057688 : CollatzResearch.WordTrace tailWord_2057688 prefixEnd_2057688 1056582980988850519936871 := by
  unfold tailWord_2057688
  simp only [CollatzResearch.WordTrace]
  refine ⟨37525023484677637988562859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50033364646236850651417145 37525023484677637988562859)
  ·
    refine ⟨56287535227016456982844289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37525023484677637988562859 56287535227016456982844289)
    ·
      refine ⟨42215651420262342737133217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56287535227016456982844289 42215651420262342737133217)
      ·
        refine ⟨31661738565196757052849913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42215651420262342737133217 31661738565196757052849913)
        ·
          refine ⟨23746303923897567789637435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31661738565196757052849913 23746303923897567789637435)
          ·
            refine ⟨35619455885846351684456153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23746303923897567789637435 35619455885846351684456153)
            ·
              refine ⟨26714591914384763763342115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35619455885846351684456153 26714591914384763763342115)
              ·
                refine ⟨40071887871577145645013173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26714591914384763763342115 40071887871577145645013173)
                ·
                  refine ⟨3756739487960357404219985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40071887871577145645013173 3756739487960357404219985)
                  ·
                    refine ⟨2817554615970268053164989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3756739487960357404219985 2817554615970268053164989)
                    ·
                      refine ⟨1056582980988850519936871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817554615970268053164989 1056582980988850519936871)
                      ·
                        rfl

theorem cell23_2057688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2057688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057688 prefixEnd_2057688 := by exact prefixLift 2057688
  have htrace : WordTrace (prefixWord ++ tailWord_2057688) baseStart_2057688 baseEnd_2057688 := by
    simpa [prefixWord, tailWord_2057688, baseEnd_2057688] using wordTrace_append hprefix tailTrace_2057688
  have hstable : (prefixWord ++ tailWord_2057688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057688).length < 2 ^ (prefixWord ++ tailWord_2057688).sum := by decide
  have hdescent : baseEnd_2057688 < baseStart_2057688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057721 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_2057721 : Nat := 118140960795 + 2057721 * 2 ^ 59
def prefixEnd_2057721 : Nat := 4983230072969 + 3 ^ 40 * 2057721 * 2
def baseEnd_2057721 : Nat := 352199975283482963608073

theorem tailTrace_2057721 : CollatzResearch.WordTrace tailWord_2057721 prefixEnd_2057721 352199975283482963608073 := by
  unfold tailWord_2057721
  simp only [CollatzResearch.WordTrace]
  refine ⟨75051250578235722613077017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50034167052157148408718011 75051250578235722613077017)
  ·
    refine ⟨56288437933676791959807763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75051250578235722613077017 56288437933676791959807763)
    ·
      refine ⟨84432656900515187939711645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56288437933676791959807763 84432656900515187939711645)
      ·
        refine ⟨31662246337693195477391867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84432656900515187939711645 31662246337693195477391867)
        ·
          refine ⟨47493369506539793216087801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31662246337693195477391867 47493369506539793216087801)
          ·
            refine ⟨35620027129904844912065851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47493369506539793216087801 35620027129904844912065851)
            ·
              refine ⟨53430040694857267368098777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35620027129904844912065851 53430040694857267368098777)
              ·
                refine ⟨40072530521142950526074083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53430040694857267368098777 40072530521142950526074083)
                ·
                  refine ⟨60108795781714425789111125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40072530521142950526074083 60108795781714425789111125)
                  ·
                    refine ⟨352199975283482963608073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60108795781714425789111125 352199975283482963608073)
                    ·
                      rfl

theorem cell23_2057721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_2057721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057721 prefixEnd_2057721 := by exact prefixLift 2057721
  have htrace : WordTrace (prefixWord ++ tailWord_2057721) baseStart_2057721 baseEnd_2057721 := by
    simpa [prefixWord, tailWord_2057721, baseEnd_2057721] using wordTrace_append hprefix tailTrace_2057721
  have hstable : (prefixWord ++ tailWord_2057721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057721).length < 2 ^ (prefixWord ++ tailWord_2057721).sum := by decide
  have hdescent : baseEnd_2057721 < baseStart_2057721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057745 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_2057745 : Nat := 118140960795 + 2057745 * 2 ^ 59
def prefixEnd_2057745 : Nat := 4983230072969 + 3 ^ 40 * 2057745 * 2
def baseEnd_2057745 : Nat := 1056612249386156796924109

theorem tailTrace_2057745 : CollatzResearch.WordTrace tailWord_2057745 prefixEnd_2057745 1056612249386156796924109 := by
  unfold tailWord_2057745
  simp only [CollatzResearch.WordTrace]
  refine ⟨75052125930148774711950689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50034750620099183141300459 75052125930148774711950689)
  ·
    refine ⟨56289094447611581033963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75052125930148774711950689 56289094447611581033963017)
    ·
      refine ⟨42216820835708685775472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56289094447611581033963017 42216820835708685775472263)
      ·
        refine ⟨63325231253563028663208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42216820835708685775472263 63325231253563028663208395)
        ·
          refine ⟨94987846880344542994812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63325231253563028663208395 94987846880344542994812593)
          ·
            refine ⟨71240885160258407246109445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94987846880344542994812593 71240885160258407246109445)
            ·
              refine ⟨13357665967548451358645521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71240885160258407246109445 13357665967548451358645521)
              ·
                refine ⟨10018249475661338518984141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13357665967548451358645521 10018249475661338518984141)
                ·
                  refine ⟨3756843553373001944619053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10018249475661338518984141 3756843553373001944619053)
                  ·
                    refine ⟨1408816332514875729232145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756843553373001944619053 1408816332514875729232145)
                    ·
                      refine ⟨1056612249386156796924109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408816332514875729232145 1056612249386156796924109)
                      ·
                        rfl

theorem cell23_2057745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_2057745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057745 prefixEnd_2057745 := by exact prefixLift 2057745
  have htrace : WordTrace (prefixWord ++ tailWord_2057745) baseStart_2057745 baseEnd_2057745 := by
    simpa [prefixWord, tailWord_2057745, baseEnd_2057745] using wordTrace_append hprefix tailTrace_2057745
  have hstable : (prefixWord ++ tailWord_2057745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057745).length < 2 ^ (prefixWord ++ tailWord_2057745).sum := by decide
  have hdescent : baseEnd_2057745 < baseStart_2057745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057779 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 1, 3, 2]
def baseStart_2057779 : Nat := 118140960795 + 2057779 * 2 ^ 59
def prefixEnd_2057779 : Nat := 4983230072969 + 3 ^ 40 * 2057779 * 2
def baseEnd_2057779 : Nat := 1056629707728409663898953

theorem tailTrace_2057779 : CollatzResearch.WordTrace tailWord_2057779 prefixEnd_2057779 1056629707728409663898953 := by
  unfold tailWord_2057779
  simp only [CollatzResearch.WordTrace]
  refine ⟨75053366012025598518688391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50035577341350399012458927 75053366012025598518688391)
  ·
    refine ⟨112580049018038397778032587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75053366012025598518688391 112580049018038397778032587)
    ·
      refine ⟨168870073527057596667048881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112580049018038397778032587 168870073527057596667048881)
      ·
        refine ⟨126652555145293197500286661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168870073527057596667048881 126652555145293197500286661)
        ·
          refine ⟨23747354089742474531303749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126652555145293197500286661 23747354089742474531303749)
          ·
            refine ⟨4452628891826713974619453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23747354089742474531303749 4452628891826713974619453)
            ·
              refine ⟨1669735834435017740482295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4452628891826713974619453 1669735834435017740482295)
              ·
                refine ⟨2504603751652526610723443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669735834435017740482295 2504603751652526610723443)
                ·
                  refine ⟨3756905627478789916085165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504603751652526610723443 3756905627478789916085165)
                  ·
                    refine ⟨1408839610304546218531937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3756905627478789916085165 1408839610304546218531937)
                    ·
                      refine ⟨1056629707728409663898953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1408839610304546218531937 1056629707728409663898953)
                      ·
                        rfl

theorem cell23_2057779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 3, 2].length) (baseStart_2057779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057779 prefixEnd_2057779 := by exact prefixLift 2057779
  have htrace : WordTrace (prefixWord ++ tailWord_2057779) baseStart_2057779 baseEnd_2057779 := by
    simpa [prefixWord, tailWord_2057779, baseEnd_2057779] using wordTrace_append hprefix tailTrace_2057779
  have hstable : (prefixWord ++ tailWord_2057779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057779).length < 2 ^ (prefixWord ++ tailWord_2057779).sum := by decide
  have hdescent : baseEnd_2057779 < baseStart_2057779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057832 : List Nat := [2, 1, 4, 3, 1, 1, 1, 5, 5]
def baseStart_2057832 : Nat := 118140960795 + 2057832 * 2 ^ 59
def prefixEnd_2057832 : Nat := 4983230072969 + 3 ^ 40 * 2057832 * 2
def baseEnd_2057832 : Nat := 117406324689233106281801

theorem tailTrace_2057832 : CollatzResearch.WordTrace tailWord_2057832 prefixEnd_2057832 117406324689233106281801 := by
  unfold tailWord_2057832
  simp only [CollatzResearch.WordTrace]
  refine ⟨37527649540416794285183875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50036866053889059046911833 37527649540416794285183875)
  ·
    refine ⟨56291474310625191427775813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37527649540416794285183875 56291474310625191427775813)
    ·
      refine ⟨10554651433242223392707965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56291474310625191427775813 10554651433242223392707965)
      ·
        refine ⟨3957994287465833772265487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10554651433242223392707965 3957994287465833772265487)
        ·
          refine ⟨5936991431198750658398231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957994287465833772265487 5936991431198750658398231)
          ·
            refine ⟨8905487146798125987597347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936991431198750658398231 8905487146798125987597347)
            ·
              refine ⟨13358230720197188981396021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905487146798125987597347 13358230720197188981396021)
              ·
                refine ⟨1252334130018486467005877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13358230720197188981396021 1252334130018486467005877)
                ·
                  refine ⟨117406324689233106281801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1252334130018486467005877 117406324689233106281801)
                  ·
                    rfl

theorem cell23_2057832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 5].length) (baseStart_2057832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057832 prefixEnd_2057832 := by exact prefixLift 2057832
  have htrace : WordTrace (prefixWord ++ tailWord_2057832) baseStart_2057832 baseEnd_2057832 := by
    simpa [prefixWord, tailWord_2057832, baseEnd_2057832] using wordTrace_append hprefix tailTrace_2057832
  have hstable : (prefixWord ++ tailWord_2057832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057832).length < 2 ^ (prefixWord ++ tailWord_2057832).sum := by decide
  have hdescent : baseEnd_2057832 < baseStart_2057832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057848 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2057848 : Nat := 118140960795 + 2057848 * 2 ^ 59
def prefixEnd_2057848 : Nat := 4983230072969 + 3 ^ 40 * 2057848 * 2
def baseEnd_2057848 : Nat := 1056665137893569893936135

theorem tailTrace_2057848 : CollatzResearch.WordTrace tailWord_2057848 prefixEnd_2057848 1056665137893569893936135 := by
  unfold tailWord_2057848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37527941324387811651475099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50037255099183748868633465 37527941324387811651475099)
  ·
    refine ⟨56291911986581717477212649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37527941324387811651475099 56291911986581717477212649)
    ·
      refine ⟨42218933989936288107909487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56291911986581717477212649 42218933989936288107909487)
      ·
        refine ⟨63328400984904432161864231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42218933989936288107909487 63328400984904432161864231)
        ·
          refine ⟨94992601477356648242796347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63328400984904432161864231 94992601477356648242796347)
          ·
            refine ⟨142488902216034972364194521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94992601477356648242796347 142488902216034972364194521)
            ·
              refine ⟨106866676662026229273145891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142488902216034972364194521 106866676662026229273145891)
              ·
                refine ⟨160300014993039343909718837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106866676662026229273145891 160300014993039343909718837)
                ·
                  refine ⟨15028126405597438491536141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160300014993039343909718837 15028126405597438491536141)
                  ·
                    refine ⟨5635547402099039434326053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15028126405597438491536141 5635547402099039434326053)
                    ·
                      refine ⟨1056665137893569893936135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5635547402099039434326053 1056665137893569893936135)
                      ·
                        rfl

theorem cell23_2057848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2057848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057848 prefixEnd_2057848 := by exact prefixLift 2057848
  have htrace : WordTrace (prefixWord ++ tailWord_2057848) baseStart_2057848 baseEnd_2057848 := by
    simpa [prefixWord, tailWord_2057848, baseEnd_2057848] using wordTrace_append hprefix tailTrace_2057848
  have hstable : (prefixWord ++ tailWord_2057848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057848).length < 2 ^ (prefixWord ++ tailWord_2057848).sum := by decide
  have hdescent : baseEnd_2057848 < baseStart_2057848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057896 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2057896 : Nat := 118140960795 + 2057896 * 2 ^ 59
def prefixEnd_2057896 : Nat := 4983230072969 + 3 ^ 40 * 2057896 * 2
def baseEnd_2057896 : Nat := 352229928321661902045305

theorem tailTrace_2057896 : CollatzResearch.WordTrace tailWord_2057896 prefixEnd_2057896 352229928321661902045305 := by
  unfold tailWord_2057896
  simp only [CollatzResearch.WordTrace]
  refine ⟨37528816676300863750348771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50038422235067818333798361 37528816676300863750348771)
  ·
    refine ⟨56293225014451295625523157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37528816676300863750348771 56293225014451295625523157)
    ·
      refine ⟨1319372461276202241223199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56293225014451295625523157 1319372461276202241223199)
      ·
        refine ⟨1979058691914303361834799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319372461276202241223199 1979058691914303361834799)
        ·
          refine ⟨2968588037871455042752199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979058691914303361834799 2968588037871455042752199)
          ·
            refine ⟨4452882056807182564128299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968588037871455042752199 4452882056807182564128299)
            ·
              refine ⟨6679323085210773846192449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452882056807182564128299 6679323085210773846192449)
              ·
                refine ⟨5009492313908080384644337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6679323085210773846192449 5009492313908080384644337)
                ·
                  refine ⟨3757119235431060288483253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5009492313908080384644337 3757119235431060288483253)
                  ·
                    refine ⟨352229928321661902045305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3757119235431060288483253 352229928321661902045305)
                    ·
                      rfl

theorem cell23_2057896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2057896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057896 prefixEnd_2057896 := by exact prefixLift 2057896
  have htrace : WordTrace (prefixWord ++ tailWord_2057896) baseStart_2057896 baseEnd_2057896 := by
    simpa [prefixWord, tailWord_2057896, baseEnd_2057896] using wordTrace_append hprefix tailTrace_2057896
  have hstable : (prefixWord ++ tailWord_2057896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057896).length < 2 ^ (prefixWord ++ tailWord_2057896).sum := by decide
  have hdescent : baseEnd_2057896 < baseStart_2057896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057966 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_2057966 : Nat := 118140960795 + 2057966 * 2 ^ 59
def prefixEnd_2057966 : Nat := 4983230072969 + 3 ^ 40 * 2057966 * 2
def baseEnd_2057966 : Nat := 1056725728610800432260593

theorem tailTrace_2057966 : CollatzResearch.WordTrace tailWord_2057966 prefixEnd_2057966 1056725728610800432260593 := by
  unfold tailWord_2057966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9382523307793516181968219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50040124308232086303830501 9382523307793516181968219)
  ·
    refine ⟨14073784961690274272952329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9382523307793516181968219 14073784961690274272952329)
    ·
      refine ⟨10555338721267705704714247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073784961690274272952329 10555338721267705704714247)
      ·
        refine ⟨15833008081901558557071371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555338721267705704714247 15833008081901558557071371)
        ·
          refine ⟨23749512122852337835607057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833008081901558557071371 23749512122852337835607057)
          ·
            refine ⟨17812134092139253376705293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23749512122852337835607057 17812134092139253376705293)
            ·
              refine ⟨6679550284552220016264485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17812134092139253376705293 6679550284552220016264485)
              ·
                refine ⟨1252415678353541253049591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6679550284552220016264485 1252415678353541253049591)
                ·
                  refine ⟨1878623517530311879574387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1252415678353541253049591 1878623517530311879574387)
                  ·
                    refine ⟨2817935276295467819361581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1878623517530311879574387 2817935276295467819361581)
                    ·
                      refine ⟨1056725728610800432260593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817935276295467819361581 1056725728610800432260593)
                      ·
                        rfl

theorem cell23_2057966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_2057966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057966 prefixEnd_2057966 := by exact prefixLift 2057966
  have htrace : WordTrace (prefixWord ++ tailWord_2057966) baseStart_2057966 baseEnd_2057966 := by
    simpa [prefixWord, tailWord_2057966, baseEnd_2057966] using wordTrace_append hprefix tailTrace_2057966
  have hstable : (prefixWord ++ tailWord_2057966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057966).length < 2 ^ (prefixWord ++ tailWord_2057966).sum := by decide
  have hdescent : baseEnd_2057966 < baseStart_2057966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057975 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_2057975 : Nat := 118140960795 + 2057975 * 2 ^ 59
def prefixEnd_2057975 : Nat := 4983230072969 + 3 ^ 40 * 2057975 * 2
def baseEnd_2057975 : Nat := 1056730349936690897048051

theorem tailTrace_2057975 : CollatzResearch.WordTrace tailWord_2057975 prefixEnd_2057975 1056730349936690897048051 := by
  unfold tailWord_2057975
  simp only [CollatzResearch.WordTrace]
  refine ⟨75060514719315523992823379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50040343146210349328548919 75060514719315523992823379)
  ·
    refine ⟨112590772078973285989235069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75060514719315523992823379 112590772078973285989235069)
    ·
      refine ⟨42221539529614982245963151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112590772078973285989235069 42221539529614982245963151)
      ·
        refine ⟨63332309294422473368944727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42221539529614982245963151 63332309294422473368944727)
        ·
          refine ⟨94998463941633710053417091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63332309294422473368944727 94998463941633710053417091)
          ·
            refine ⟨142497695912450565080125637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94998463941633710053417091 142497695912450565080125637)
            ·
              refine ⟨26718317983584480952523557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142497695912450565080125637 26718317983584480952523557)
              ·
                refine ⟨5009684621922090178598167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26718317983584480952523557 5009684621922090178598167)
                ·
                  refine ⟨7514526932883135267897251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009684621922090178598167 7514526932883135267897251)
                  ·
                    refine ⟨11271790399324702901845877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7514526932883135267897251 11271790399324702901845877)
                    ·
                      refine ⟨1056730349936690897048051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11271790399324702901845877 1056730349936690897048051)
                      ·
                        rfl

theorem cell23_2057975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_2057975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057975 prefixEnd_2057975 := by exact prefixLift 2057975
  have htrace : WordTrace (prefixWord ++ tailWord_2057975) baseStart_2057975 baseEnd_2057975 := by
    simpa [prefixWord, tailWord_2057975, baseEnd_2057975] using wordTrace_append hprefix tailTrace_2057975
  have hstable : (prefixWord ++ tailWord_2057975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057975).length < 2 ^ (prefixWord ++ tailWord_2057975).sum := by decide
  have hdescent : baseEnd_2057975 < baseStart_2057975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057985 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2057985 : Nat := 118140960795 + 2057985 * 2 ^ 59
def prefixEnd_2057985 : Nat := 4983230072969 + 3 ^ 40 * 2057985 * 2
def baseEnd_2057985 : Nat := 1056735484743235857923005

theorem tailTrace_2057985 : CollatzResearch.WordTrace tailWord_2057985 prefixEnd_2057985 1056735484743235857923005 := by
  unfold tailWord_2057985
  simp only [CollatzResearch.WordTrace]
  refine ⟨75060879449279295700687409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50040586299519530467124939 75060879449279295700687409)
  ·
    refine ⟨56295659586959471775515557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75060879449279295700687409 56295659586959471775515557)
    ·
      refine ⟨10555436172554900957909167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56295659586959471775515557 10555436172554900957909167)
      ·
        refine ⟨15833154258832351436863751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555436172554900957909167 15833154258832351436863751)
        ·
          refine ⟨23749731388248527155295627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833154258832351436863751 23749731388248527155295627)
          ·
            refine ⟨35624597082372790732943441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23749731388248527155295627 35624597082372790732943441)
            ·
              refine ⟨26718447811779593049707581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35624597082372790732943441 26718447811779593049707581)
              ·
                refine ⟨10019417929417347393640343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26718447811779593049707581 10019417929417347393640343)
                ·
                  refine ⟨15029126894126021090460515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10019417929417347393640343 15029126894126021090460515)
                  ·
                    refine ⟨22543690341189031635690773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15029126894126021090460515 22543690341189031635690773)
                    ·
                      refine ⟨1056735484743235857923005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22543690341189031635690773 1056735484743235857923005)
                      ·
                        rfl

theorem cell23_2057985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2057985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057985 prefixEnd_2057985 := by exact prefixLift 2057985
  have htrace : WordTrace (prefixWord ++ tailWord_2057985) baseStart_2057985 baseEnd_2057985 := by
    simpa [prefixWord, tailWord_2057985, baseEnd_2057985] using wordTrace_append hprefix tailTrace_2057985
  have hstable : (prefixWord ++ tailWord_2057985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057985).length < 2 ^ (prefixWord ++ tailWord_2057985).sum := by decide
  have hdescent : baseEnd_2057985 < baseStart_2057985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057992 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_2057992 : Nat := 118140960795 + 2057992 * 2 ^ 59
def prefixEnd_2057992 : Nat := 4983230072969 + 3 ^ 40 * 2057992 * 2
def baseEnd_2057992 : Nat := 1056739079107817330535473

theorem tailTrace_2057992 : CollatzResearch.WordTrace tailWord_2057992 prefixEnd_2057992 1056739079107817330535473 := by
  unfold tailWord_2057992
  simp only [CollatzResearch.WordTrace]
  refine ⟨37530567380126967948096115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50040756506835957264128153 37530567380126967948096115)
  ·
    refine ⟨56295851070190451922144173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37530567380126967948096115 56295851070190451922144173)
    ·
      refine ⟨21110944151321419470804065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56295851070190451922144173 21110944151321419470804065)
      ·
        refine ⟨15833208113491064603103049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21110944151321419470804065 15833208113491064603103049)
        ·
          refine ⟨11874906085118298452327287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15833208113491064603103049 11874906085118298452327287)
          ·
            refine ⟨17812359127677447678490931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11874906085118298452327287 17812359127677447678490931)
            ·
              refine ⟨26718538691516171517736397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17812359127677447678490931 26718538691516171517736397)
              ·
                refine ⟨10019452009318564319151149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26718538691516171517736397 10019452009318564319151149)
                ·
                  refine ⟨3757294503494461619681681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10019452009318564319151149 3757294503494461619681681)
                  ·
                    refine ⟨2817970877620846214761261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3757294503494461619681681 2817970877620846214761261)
                    ·
                      refine ⟨1056739079107817330535473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2817970877620846214761261 1056739079107817330535473)
                      ·
                        rfl

theorem cell23_2057992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_2057992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2057992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2057992 prefixEnd_2057992 := by exact prefixLift 2057992
  have htrace : WordTrace (prefixWord ++ tailWord_2057992) baseStart_2057992 baseEnd_2057992 := by
    simpa [prefixWord, tailWord_2057992, baseEnd_2057992] using wordTrace_append hprefix tailTrace_2057992
  have hstable : (prefixWord ++ tailWord_2057992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057992).length < 2 ^ (prefixWord ++ tailWord_2057992).sum := by decide
  have hdescent : baseEnd_2057992 < baseStart_2057992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058036 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2058036 : Nat := 118140960795 + 2058036 * 2 ^ 59
def prefixEnd_2058036 : Nat := 4983230072969 + 3 ^ 40 * 2058036 * 2
def baseEnd_2058036 : Nat := 1056761672256615158385271

theorem tailTrace_2058036 : CollatzResearch.WordTrace tailWord_2058036 prefixEnd_2058036 1056761672256615158385271 := by
  unfold tailWord_2058036
  simp only [CollatzResearch.WordTrace]
  refine ⟨37531369786047265705396981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50041826381396354273862641 37531369786047265705396981)
  ·
    refine ⟨3518565917441931159880967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37531369786047265705396981 3518565917441931159880967)
    ·
      refine ⟨5277848876162896739821451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518565917441931159880967 5277848876162896739821451)
      ·
        refine ⟨7916773314244345109732177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277848876162896739821451 7916773314244345109732177)
        ·
          refine ⟨5937579985683258832299133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916773314244345109732177 5937579985683258832299133)
          ·
            refine ⟨2226592494631222062112175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5937579985683258832299133 2226592494631222062112175)
            ·
              refine ⟨3339888741946833093168263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226592494631222062112175 3339888741946833093168263)
              ·
                refine ⟨5009833112920249639752395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339888741946833093168263 5009833112920249639752395)
                ·
                  refine ⟨7514749669380374459628593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5009833112920249639752395 7514749669380374459628593)
                  ·
                    refine ⟨5636062252035280844721445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7514749669380374459628593 5636062252035280844721445)
                    ·
                      refine ⟨1056761672256615158385271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5636062252035280844721445 1056761672256615158385271)
                      ·
                        rfl

theorem cell23_2058036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2058036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058036 prefixEnd_2058036 := by exact prefixLift 2058036
  have htrace : WordTrace (prefixWord ++ tailWord_2058036) baseStart_2058036 baseEnd_2058036 := by
    simpa [prefixWord, tailWord_2058036, baseEnd_2058036] using wordTrace_append hprefix tailTrace_2058036
  have hstable : (prefixWord ++ tailWord_2058036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058036).length < 2 ^ (prefixWord ++ tailWord_2058036).sum := by decide
  have hdescent : baseEnd_2058036 < baseStart_2058036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058055 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2058055 : Nat := 118140960795 + 2058055 * 2 ^ 59
def prefixEnd_2058055 : Nat := 4983230072969 + 3 ^ 40 * 2058055 * 2
def baseEnd_2058055 : Nat := 352257142796350194682561

theorem tailTrace_2058055 : CollatzResearch.WordTrace tailWord_2058055 prefixEnd_2058055 352257142796350194682561 := by
  unfold tailWord_2058055
  simp only [CollatzResearch.WordTrace]
  refine ⟨75063432559025697655735619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50042288372683798437157079 75063432559025697655735619)
  ·
    refine ⟨112595148838538546483603429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75063432559025697655735619 112595148838538546483603429)
    ·
      refine ⟨21111590407225977465675643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112595148838538546483603429 21111590407225977465675643)
      ·
        refine ⟨31667385610838966198513465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111590407225977465675643 31667385610838966198513465)
        ·
          refine ⟨23750539208129224648885099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31667385610838966198513465 23750539208129224648885099)
          ·
            refine ⟨35625808812193836973327649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23750539208129224648885099 35625808812193836973327649)
            ·
              refine ⟨26719356609145377729995737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35625808812193836973327649 26719356609145377729995737)
              ·
                refine ⟨20039517456859033297496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26719356609145377729995737 20039517456859033297496803)
                ·
                  refine ⟨30059276185288549946245205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20039517456859033297496803 30059276185288549946245205)
                  ·
                    refine ⟨352257142796350194682561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30059276185288549946245205 352257142796350194682561)
                    ·
                      rfl

theorem cell23_2058055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2058055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058055 prefixEnd_2058055 := by exact prefixLift 2058055
  have htrace : WordTrace (prefixWord ++ tailWord_2058055) baseStart_2058055 baseEnd_2058055 := by
    simpa [prefixWord, tailWord_2058055, baseEnd_2058055] using wordTrace_append hprefix tailTrace_2058055
  have hstable : (prefixWord ++ tailWord_2058055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058055).length < 2 ^ (prefixWord ++ tailWord_2058055).sum := by decide
  have hdescent : baseEnd_2058055 < baseStart_2058055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058066 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_2058066 : Nat := 118140960795 + 2058066 * 2 ^ 59
def prefixEnd_2058066 : Nat := 4983230072969 + 3 ^ 40 * 2058066 * 2
def baseEnd_2058066 : Nat := 1056777076676250041010133

theorem tailTrace_2058066 : CollatzResearch.WordTrace tailWord_2058066 prefixEnd_2058066 1056777076676250041010133 := by
  unfold tailWord_2058066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18765958440496461633596513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50042555841323897689590701 18765958440496461633596513)
  ·
    refine ⟨14074468830372346225197385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18765958440496461633596513 14074468830372346225197385)
    ·
      refine ⟨10555851622779259668898039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14074468830372346225197385 10555851622779259668898039)
      ·
        refine ⟨15833777434168889503347059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555851622779259668898039 15833777434168889503347059)
        ·
          refine ⟨23750666151253334255020589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833777434168889503347059 23750666151253334255020589)
          ·
            refine ⟨8906499806720000345632721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23750666151253334255020589 8906499806720000345632721)
            ·
              refine ⟨6679874855040000259224541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8906499806720000345632721 6679874855040000259224541)
              ·
                refine ⟨2504953070640000097209203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6679874855040000259224541 2504953070640000097209203)
                ·
                  refine ⟨3757429605960000145813805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504953070640000097209203 3757429605960000145813805)
                  ·
                    refine ⟨1409036102235000054680177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757429605960000145813805 1409036102235000054680177)
                    ·
                      refine ⟨1056777076676250041010133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409036102235000054680177 1056777076676250041010133)
                      ·
                        rfl

theorem cell23_2058066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_2058066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058066 prefixEnd_2058066 := by exact prefixLift 2058066
  have htrace : WordTrace (prefixWord ++ tailWord_2058066) baseStart_2058066 baseEnd_2058066 := by
    simpa [prefixWord, tailWord_2058066, baseEnd_2058066] using wordTrace_append hprefix tailTrace_2058066
  have hstable : (prefixWord ++ tailWord_2058066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058066).length < 2 ^ (prefixWord ++ tailWord_2058066).sum := by decide
  have hdescent : baseEnd_2058066 < baseStart_2058066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058113 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2058113 : Nat := 118140960795 + 2058113 * 2 ^ 59
def prefixEnd_2058113 : Nat := 4983230072969 + 3 ^ 40 * 2058113 * 2
def baseEnd_2058113 : Nat := 1056801210267011357122417

theorem tailTrace_2058113 : CollatzResearch.WordTrace tailWord_2058113 prefixEnd_2058113 1056801210267011357122417 := by
  unfold tailWord_2058113
  simp only [CollatzResearch.WordTrace]
  refine ⟨75065547992815573561346993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50043698661877049040897995 75065547992815573561346993)
  ·
    refine ⟨56299160994611680171010245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75065547992815573561346993 56299160994611680171010245)
    ·
      refine ⟨10556092686489690032064421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56299160994611680171010245 10556092686489690032064421)
      ·
        refine ⟨1979267378716816881012079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10556092686489690032064421 1979267378716816881012079)
        ·
          refine ⟨2968901068075225321518119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979267378716816881012079 2968901068075225321518119)
          ·
            refine ⟨4453351602112837982277179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968901068075225321518119 4453351602112837982277179)
            ·
              refine ⟨6680027403169256973415769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453351602112837982277179 6680027403169256973415769)
              ·
                refine ⟨5010020552376942730061827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680027403169256973415769 5010020552376942730061827)
                ·
                  refine ⟨7515030828565414095092741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010020552376942730061827 7515030828565414095092741)
                  ·
                    refine ⟨1409068280356015142829889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7515030828565414095092741 1409068280356015142829889)
                    ·
                      refine ⟨1056801210267011357122417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409068280356015142829889 1056801210267011357122417)
                      ·
                        rfl

theorem cell23_2058113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2058113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058113 prefixEnd_2058113 := by exact prefixLift 2058113
  have htrace : WordTrace (prefixWord ++ tailWord_2058113) baseStart_2058113 baseEnd_2058113 := by
    simpa [prefixWord, tailWord_2058113, baseEnd_2058113] using wordTrace_append hprefix tailTrace_2058113
  have hstable : (prefixWord ++ tailWord_2058113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058113).length < 2 ^ (prefixWord ++ tailWord_2058113).sum := by decide
  have hdescent : baseEnd_2058113 < baseStart_2058113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058130 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2058130 : Nat := 118140960795 + 2058130 * 2 ^ 59
def prefixEnd_2058130 : Nat := 4983230072969 + 3 ^ 40 * 2058130 * 2
def baseEnd_2058130 : Nat := 1056809939438137790609839

theorem tailTrace_2058130 : CollatzResearch.WordTrace tailWord_2058130 prefixEnd_2058130 1056809939438137790609839 := by
  unfold tailWord_2058130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766542008438496366178961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50044112022502656976477229 18766542008438496366178961)
  ·
    refine ⟨14074906506328872274634221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18766542008438496366178961 14074906506328872274634221)
    ·
      refine ⟨5278089939873327102987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14074906506328872274634221 5278089939873327102987833)
      ·
        refine ⟨3958567454904995327240875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5278089939873327102987833 3958567454904995327240875)
        ·
          refine ⟨5937851182357492990861313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958567454904995327240875 5937851182357492990861313)
          ·
            refine ⟨4453388386768119743145985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937851182357492990861313 4453388386768119743145985)
            ·
              refine ⟨3340041290076089807359489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453388386768119743145985 3340041290076089807359489)
              ·
                refine ⟨2505030967557067355519617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340041290076089807359489 2505030967557067355519617)
                ·
                  refine ⟨1878773225667800516639713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2505030967557067355519617 1878773225667800516639713)
                  ·
                    refine ⟨1409079919250850387479785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1878773225667800516639713 1409079919250850387479785)
                    ·
                      refine ⟨1056809939438137790609839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409079919250850387479785 1056809939438137790609839)
                      ·
                        rfl

theorem cell23_2058130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2058130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058130 prefixEnd_2058130 := by exact prefixLift 2058130
  have htrace : WordTrace (prefixWord ++ tailWord_2058130) baseStart_2058130 baseEnd_2058130 := by
    simpa [prefixWord, tailWord_2058130, baseEnd_2058130] using wordTrace_append hprefix tailTrace_2058130
  have hstable : (prefixWord ++ tailWord_2058130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058130).length < 2 ^ (prefixWord ++ tailWord_2058130).sum := by decide
  have hdescent : baseEnd_2058130 < baseStart_2058130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058146 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2058146 : Nat := 118140960795 + 2058146 * 2 ^ 59
def prefixEnd_2058146 : Nat := 4983230072969 + 3 ^ 40 * 2058146 * 2
def baseEnd_2058146 : Nat := 1056818155128609728009765

theorem tailTrace_2058146 : CollatzResearch.WordTrace tailWord_2058146 prefixEnd_2058146 1056818155128609728009765 := by
  unfold tailWord_2058146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18766687900424005049324573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50044501067797346798198861 18766687900424005049324573)
  ·
    refine ⟨7037507962659001893496715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18766687900424005049324573 7037507962659001893496715)
    ·
      refine ⟨10556261943988502840245073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037507962659001893496715 10556261943988502840245073)
      ·
        refine ⟨7917196457991377130183805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10556261943988502840245073 7917196457991377130183805)
        ·
          refine ⟨2968948671746766423818927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7917196457991377130183805 2968948671746766423818927)
          ·
            refine ⟨4453423007620149635728391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968948671746766423818927 4453423007620149635728391)
            ·
              refine ⟨6680134511430224453592587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453423007620149635728391 6680134511430224453592587)
              ·
                refine ⟨10020201767145336680388881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680134511430224453592587 10020201767145336680388881)
                ·
                  refine ⟨7515151325359002510291661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10020201767145336680388881 7515151325359002510291661)
                  ·
                    refine ⟨2818181747009625941359373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515151325359002510291661 2818181747009625941359373)
                    ·
                      refine ⟨1056818155128609728009765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2818181747009625941359373 1056818155128609728009765)
                      ·
                        rfl

theorem cell23_2058146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2058146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058146 prefixEnd_2058146 := by exact prefixLift 2058146
  have htrace : WordTrace (prefixWord ++ tailWord_2058146) baseStart_2058146 baseEnd_2058146 := by
    simpa [prefixWord, tailWord_2058146, baseEnd_2058146] using wordTrace_append hprefix tailTrace_2058146
  have hstable : (prefixWord ++ tailWord_2058146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058146).length < 2 ^ (prefixWord ++ tailWord_2058146).sum := by decide
  have hdescent : baseEnd_2058146 < baseStart_2058146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058169 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2058169 : Nat := 118140960795 + 2058169 * 2 ^ 59
def prefixEnd_2058169 : Nat := 4983230072969 + 3 ^ 40 * 2058169 * 2
def baseEnd_2058169 : Nat := 1056829965183663138022159

theorem tailTrace_2058169 : CollatzResearch.WordTrace tailWord_2058169 prefixEnd_2058169 1056829965183663138022159 := by
  unfold tailWord_2058169
  simp only [CollatzResearch.WordTrace]
  refine ⟨75067590480612695125385561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50045060320408463416923707 75067590480612695125385561)
  ·
    refine ⟨56300692860459521344039171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75067590480612695125385561 56300692860459521344039171)
    ·
      refine ⟨84451039290689282016058757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56300692860459521344039171 84451039290689282016058757)
      ·
        refine ⟨15834569867004240378011017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84451039290689282016058757 15834569867004240378011017)
        ·
          refine ⟨11875927400253180283508263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15834569867004240378011017 11875927400253180283508263)
          ·
            refine ⟨17813891100379770425262395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11875927400253180283508263 17813891100379770425262395)
            ·
              refine ⟨26720836650569655637893593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17813891100379770425262395 26720836650569655637893593)
              ·
                refine ⟨20040627487927241728420195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26720836650569655637893593 20040627487927241728420195)
                ·
                  refine ⟨30060941231890862592630293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20040627487927241728420195 30060941231890862592630293)
                  ·
                    refine ⟨1409106620244884184029545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30060941231890862592630293 1409106620244884184029545)
                    ·
                      refine ⟨1056829965183663138022159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409106620244884184029545 1056829965183663138022159)
                      ·
                        rfl

theorem cell23_2058169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2058169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058169 prefixEnd_2058169 := by exact prefixLift 2058169
  have htrace : WordTrace (prefixWord ++ tailWord_2058169) baseStart_2058169 baseEnd_2058169 := by
    simpa [prefixWord, tailWord_2058169, baseEnd_2058169] using wordTrace_append hprefix tailTrace_2058169
  have hstable : (prefixWord ++ tailWord_2058169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058169).length < 2 ^ (prefixWord ++ tailWord_2058169).sum := by decide
  have hdescent : baseEnd_2058169 < baseStart_2058169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058196 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2058196 : Nat := 118140960795 + 2058196 * 2 ^ 59
def prefixEnd_2058196 : Nat := 4983230072969 + 3 ^ 40 * 2058196 * 2
def baseEnd_2058196 : Nat := 352281276387111510794845

theorem tailTrace_2058196 : CollatzResearch.WordTrace tailWord_2058196 prefixEnd_2058196 352281276387111510794845 := by
  unfold tailWord_2058196
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534287625757439368309221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50045716834343252491078961 37534287625757439368309221)
  ·
    refine ⟨7037678929829519881557979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37534287625757439368309221 7037678929829519881557979)
    ·
      refine ⟨10556518394744279822336969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037678929829519881557979 10556518394744279822336969)
      ·
        refine ⟨7917388796058209866752727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10556518394744279822336969 7917388796058209866752727)
        ·
          refine ⟨11876083194087314800129091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917388796058209866752727 11876083194087314800129091)
          ·
            refine ⟨17814124791130972200193637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11876083194087314800129091 17814124791130972200193637)
            ·
              refine ⟨3340148398337057287536307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17814124791130972200193637 3340148398337057287536307)
              ·
                refine ⟨5010222597505585931304461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340148398337057287536307 5010222597505585931304461)
                ·
                  refine ⟨1878833474064594724239173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5010222597505585931304461 1878833474064594724239173)
                  ·
                    refine ⟨352281276387111510794845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1878833474064594724239173 352281276387111510794845)
                    ·
                      rfl

theorem cell23_2058196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2058196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058196 prefixEnd_2058196 := by exact prefixLift 2058196
  have htrace : WordTrace (prefixWord ++ tailWord_2058196) baseStart_2058196 baseEnd_2058196 := by
    simpa [prefixWord, tailWord_2058196, baseEnd_2058196] using wordTrace_append hprefix tailTrace_2058196
  have hstable : (prefixWord ++ tailWord_2058196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058196).length < 2 ^ (prefixWord ++ tailWord_2058196).sum := by decide
  have hdescent : baseEnd_2058196 < baseStart_2058196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058212 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2058212 : Nat := 118140960795 + 2058212 * 2 ^ 59
def prefixEnd_2058212 : Nat := 4983230072969 + 3 ^ 40 * 2058212 * 2
def baseEnd_2058212 : Nat := 1056852044851806469784461

theorem tailTrace_2058212 : CollatzResearch.WordTrace tailWord_2058212 prefixEnd_2058212 1056852044851806469784461 := by
  unfold tailWord_2058212
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534579409728456734600445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50046105879637942312800593 37534579409728456734600445)
  ·
    refine ⟨14075467278648171275475167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37534579409728456734600445 14075467278648171275475167)
    ·
      refine ⟨21113200917972256913212751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14075467278648171275475167 21113200917972256913212751)
      ·
        refine ⟨31669801376958385369819127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21113200917972256913212751 31669801376958385369819127)
        ·
          refine ⟨47504702065437578054728691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31669801376958385369819127 47504702065437578054728691)
          ·
            refine ⟨71257053098156367082093037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47504702065437578054728691 71257053098156367082093037)
            ·
              refine ⟨26721394911808637655784889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71257053098156367082093037 26721394911808637655784889)
              ·
                refine ⟨20041046183856478241838667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26721394911808637655784889 20041046183856478241838667)
                ·
                  refine ⟨30061569275784717362758001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20041046183856478241838667 30061569275784717362758001)
                  ·
                    refine ⟨22546176956838538022068501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30061569275784717362758001 22546176956838538022068501)
                    ·
                      refine ⟨1056852044851806469784461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22546176956838538022068501 1056852044851806469784461)
                      ·
                        rfl

theorem cell23_2058212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2058212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058212 prefixEnd_2058212 := by exact prefixLift 2058212
  have htrace : WordTrace (prefixWord ++ tailWord_2058212) baseStart_2058212 baseEnd_2058212 := by
    simpa [prefixWord, tailWord_2058212, baseEnd_2058212] using wordTrace_append hprefix tailTrace_2058212
  have hstable : (prefixWord ++ tailWord_2058212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058212).length < 2 ^ (prefixWord ++ tailWord_2058212).sum := by decide
  have hdescent : baseEnd_2058212 < baseStart_2058212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058273 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2058273 : Nat := 118140960795 + 2058273 * 2 ^ 59
def prefixEnd_2058273 : Nat := 4983230072969 + 3 ^ 40 * 2058273 * 2
def baseEnd_2058273 : Nat := 352294455723910243707227

theorem tailTrace_2058273 : CollatzResearch.WordTrace tailWord_2058273 prefixEnd_2058273 352294455723910243707227 := by
  unfold tailWord_2058273
  simp only [CollatzResearch.WordTrace]
  refine ⟨75071383672235920887171473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50047589114823947258114315 75071383672235920887171473)
  ·
    refine ⟨56303537754176940665378605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75071383672235920887171473 56303537754176940665378605)
    ·
      refine ⟨21113826657816352749516977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56303537754176940665378605 21113826657816352749516977)
      ·
        refine ⟨15835369993362264562137733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21113826657816352749516977 15835369993362264562137733)
        ·
          refine ⟨2969131873755424605400825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15835369993362264562137733 2969131873755424605400825)
          ·
            refine ⟨2226848905316568454050619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969131873755424605400825 2226848905316568454050619)
            ·
              refine ⟨3340273357974852681075929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226848905316568454050619 3340273357974852681075929)
              ·
                refine ⟨2505205018481139510806947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340273357974852681075929 2505205018481139510806947)
                ·
                  refine ⟨3757807527721709266210421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505205018481139510806947 3757807527721709266210421)
                  ·
                    refine ⟨352294455723910243707227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3757807527721709266210421 352294455723910243707227)
                    ·
                      rfl

theorem cell23_2058273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2058273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058273 prefixEnd_2058273 := by exact prefixLift 2058273
  have htrace : WordTrace (prefixWord ++ tailWord_2058273) baseStart_2058273 baseEnd_2058273 := by
    simpa [prefixWord, tailWord_2058273, baseEnd_2058273] using wordTrace_append hprefix tailTrace_2058273
  have hstable : (prefixWord ++ tailWord_2058273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058273).length < 2 ^ (prefixWord ++ tailWord_2058273).sum := by decide
  have hdescent : baseEnd_2058273 < baseStart_2058273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058286 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2058286 : Nat := 118140960795 + 2058286 * 2 ^ 59
def prefixEnd_2058286 : Nat := 4983230072969 + 3 ^ 40 * 2058286 * 2
def baseEnd_2058286 : Nat := 352296680806746393419707

theorem tailTrace_2058286 : CollatzResearch.WordTrace tailWord_2058286 prefixEnd_2058286 352296680806746393419707 := by
  unfold tailWord_2058286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383982227648603013424339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50047905214125882738263141 9383982227648603013424339)
  ·
    refine ⟨14075973341472904520136509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383982227648603013424339 14075973341472904520136509)
    ·
      refine ⟨5278490003052339195051191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14075973341472904520136509 5278490003052339195051191)
      ·
        refine ⟨7917735004578508792576787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278490003052339195051191 7917735004578508792576787)
        ·
          refine ⟨11876602506867763188865181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917735004578508792576787 11876602506867763188865181)
          ·
            refine ⟨4453725940075411195824443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11876602506867763188865181 4453725940075411195824443)
            ·
              refine ⟨6680588910113116793736665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453725940075411195824443 6680588910113116793736665)
              ·
                refine ⟨5010441682584837595302499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680588910113116793736665 5010441682584837595302499)
                ·
                  refine ⟨7515662523877256392953749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5010441682584837595302499 7515662523877256392953749)
                  ·
                    refine ⟨352296680806746393419707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7515662523877256392953749 352296680806746393419707)
                    ·
                      rfl

theorem cell23_2058286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2058286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058286 prefixEnd_2058286 := by exact prefixLift 2058286
  have htrace : WordTrace (prefixWord ++ tailWord_2058286) baseStart_2058286 baseEnd_2058286 := by
    simpa [prefixWord, tailWord_2058286, baseEnd_2058286] using wordTrace_append hprefix tailTrace_2058286
  have hstable : (prefixWord ++ tailWord_2058286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058286).length < 2 ^ (prefixWord ++ tailWord_2058286).sum := by decide
  have hdescent : baseEnd_2058286 < baseStart_2058286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058289 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2058289 : Nat := 118140960795 + 2058289 * 2 ^ 59
def prefixEnd_2058289 : Nat := 4983230072969 + 3 ^ 40 * 2058289 * 2
def baseEnd_2058289 : Nat := 1056891582862202668521607

theorem tailTrace_2058289 : CollatzResearch.WordTrace tailWord_2058289 prefixEnd_2058289 1056891582862202668521607 := by
  unfold tailWord_2058289
  simp only [CollatzResearch.WordTrace]
  refine ⟨75071967240177955619753921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50047978160118637079835947 75071967240177955619753921)
  ·
    refine ⟨56303975430133466714815441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75071967240177955619753921 56303975430133466714815441)
    ·
      refine ⟨42227981572600100036111581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56303975430133466714815441 42227981572600100036111581)
      ·
        refine ⟨15835493089725037513541843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42227981572600100036111581 15835493089725037513541843)
        ·
          refine ⟨23753239634587556270312765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15835493089725037513541843 23753239634587556270312765)
          ·
            refine ⟨8907464862970333601367287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23753239634587556270312765 8907464862970333601367287)
            ·
              refine ⟨13361197294455500402050931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907464862970333601367287 13361197294455500402050931)
              ·
                refine ⟨20041795941683250603076397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361197294455500402050931 20041795941683250603076397)
                ·
                  refine ⟨7515673478131218976153649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20041795941683250603076397 7515673478131218976153649)
                  ·
                    refine ⟨5636755108598414232115237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7515673478131218976153649 5636755108598414232115237)
                    ·
                      refine ⟨1056891582862202668521607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5636755108598414232115237 1056891582862202668521607)
                      ·
                        rfl

theorem cell23_2058289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2058289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058289 prefixEnd_2058289 := by exact prefixLift 2058289
  have htrace : WordTrace (prefixWord ++ tailWord_2058289) baseStart_2058289 baseEnd_2058289 := by
    simpa [prefixWord, tailWord_2058289, baseEnd_2058289] using wordTrace_append hprefix tailTrace_2058289
  have hstable : (prefixWord ++ tailWord_2058289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058289).length < 2 ^ (prefixWord ++ tailWord_2058289).sum := by decide
  have hdescent : baseEnd_2058289 < baseStart_2058289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058309 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_2058309 : Nat := 118140960795 + 2058309 * 2 ^ 59
def prefixEnd_2058309 : Nat := 4983230072969 + 3 ^ 40 * 2058309 * 2
def baseEnd_2058309 : Nat := 1056901852475292590271515

theorem tailTrace_2058309 : CollatzResearch.WordTrace tailWord_2058309 prefixEnd_2058309 1056901852475292590271515 := by
  unfold tailWord_2058309
  simp only [CollatzResearch.WordTrace]
  refine ⟨75072696700105499035481981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50048464466736999356987987 75072696700105499035481981)
  ·
    refine ⟨28152261262539562138305743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75072696700105499035481981 28152261262539562138305743)
    ·
      refine ⟨42228391893809343207458615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28152261262539562138305743 42228391893809343207458615)
      ·
        refine ⟨63342587840714014811187923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42228391893809343207458615 63342587840714014811187923)
        ·
          refine ⟨95013881761071022216781885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63342587840714014811187923 95013881761071022216781885)
          ·
            refine ⟨35630205660401633331293207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95013881761071022216781885 35630205660401633331293207)
            ·
              refine ⟨53445308490602449996939811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35630205660401633331293207 53445308490602449996939811)
              ·
                refine ⟨80167962735903674995409717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53445308490602449996939811 80167962735903674995409717)
                ·
                  refine ⟨7515746506490969530819661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80167962735903674995409717 7515746506490969530819661)
                  ·
                    refine ⟨2818404939934113574057373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7515746506490969530819661 2818404939934113574057373)
                    ·
                      refine ⟨1056901852475292590271515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2818404939934113574057373 1056901852475292590271515)
                      ·
                        rfl

theorem cell23_2058309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_2058309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058309 prefixEnd_2058309 := by exact prefixLift 2058309
  have htrace : WordTrace (prefixWord ++ tailWord_2058309) baseStart_2058309 baseEnd_2058309 := by
    simpa [prefixWord, tailWord_2058309, baseEnd_2058309] using wordTrace_append hprefix tailTrace_2058309
  have hstable : (prefixWord ++ tailWord_2058309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058309).length < 2 ^ (prefixWord ++ tailWord_2058309).sum := by decide
  have hdescent : baseEnd_2058309 < baseStart_2058309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058333 : List Nat := [1, 4, 4, 1, 1, 2, 3, 7]
def baseStart_2058333 : Nat := 118140960795 + 2058333 * 2 ^ 59
def prefixEnd_2058333 : Nat := 4983230072969 + 3 ^ 40 * 2058333 * 2
def baseEnd_2058333 : Nat := 39144969481888907273015

theorem tailTrace_2058333 : CollatzResearch.WordTrace tailWord_2058333 prefixEnd_2058333 39144969481888907273015 := by
  unfold tailWord_2058333
  simp only [CollatzResearch.WordTrace]
  refine ⟨75073572052018551134355653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50049048034679034089570435 75073572052018551134355653)
  ·
    refine ⟨14076294759753478337691685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75073572052018551134355653 14076294759753478337691685)
    ·
      refine ⟨2639305267453777188317191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14076294759753478337691685 2639305267453777188317191)
      ·
        refine ⟨3958957901180665782475787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639305267453777188317191 3958957901180665782475787)
        ·
          refine ⟨5938436851770998673713681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958957901180665782475787 5938436851770998673713681)
          ·
            refine ⟨4453827638828249005285261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938436851770998673713681 4453827638828249005285261)
            ·
              refine ⟨1670185364560593376981973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4453827638828249005285261 1670185364560593376981973)
              ·
                refine ⟨39144969481888907273015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1670185364560593376981973 39144969481888907273015)
                ·
                  rfl

theorem cell23_2058333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 7].length) (baseStart_2058333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058333 prefixEnd_2058333 := by exact prefixLift 2058333
  have htrace : WordTrace (prefixWord ++ tailWord_2058333) baseStart_2058333 baseEnd_2058333 := by
    simpa [prefixWord, tailWord_2058333, baseEnd_2058333] using wordTrace_append hprefix tailTrace_2058333
  have hstable : (prefixWord ++ tailWord_2058333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058333).length < 2 ^ (prefixWord ++ tailWord_2058333).sum := by decide
  have hdescent : baseEnd_2058333 < baseStart_2058333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058353 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_2058353 : Nat := 118140960795 + 2058353 * 2 ^ 59
def prefixEnd_2058353 : Nat := 4983230072969 + 3 ^ 40 * 2058353 * 2
def baseEnd_2058353 : Nat := 1056924445624090418121313

theorem tailTrace_2058353 : CollatzResearch.WordTrace tailWord_2058353 prefixEnd_2058353 1056924445624090418121313 := by
  unfold tailWord_2058353
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074301511946094550083713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50049534341297396366722475 75074301511946094550083713)
  ·
    refine ⟨56305726133959570912562785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75074301511946094550083713 56305726133959570912562785)
    ·
      refine ⟨42229294600469678184422089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56305726133959570912562785 42229294600469678184422089)
      ·
        refine ⟨31671970950352258638316567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42229294600469678184422089 31671970950352258638316567)
        ·
          refine ⟨47507956425528387957474851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31671970950352258638316567 47507956425528387957474851)
          ·
            refine ⟨71261934638292581936212277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47507956425528387957474851 71261934638292581936212277)
            ·
              refine ⟨6680806372339929556519901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71261934638292581936212277 6680806372339929556519901)
              ·
                refine ⟨2505302389627473583694963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6680806372339929556519901 2505302389627473583694963)
                ·
                  refine ⟨3757953584441210375542445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2505302389627473583694963 3757953584441210375542445)
                  ·
                    refine ⟨1409232594165453890828417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3757953584441210375542445 1409232594165453890828417)
                    ·
                      refine ⟨1056924445624090418121313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1409232594165453890828417 1056924445624090418121313)
                      ·
                        rfl

theorem cell23_2058353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_2058353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058353 prefixEnd_2058353 := by exact prefixLift 2058353
  have htrace : WordTrace (prefixWord ++ tailWord_2058353) baseStart_2058353 baseEnd_2058353 := by
    simpa [prefixWord, tailWord_2058353, baseEnd_2058353] using wordTrace_append hprefix tailTrace_2058353
  have hstable : (prefixWord ++ tailWord_2058353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058353).length < 2 ^ (prefixWord ++ tailWord_2058353).sum := by decide
  have hdescent : baseEnd_2058353 < baseStart_2058353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058359 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 2, 6]
def baseStart_2058359 : Nat := 118140960795 + 2058359 * 2 ^ 59
def prefixEnd_2058359 : Nat := 4983230072969 + 3 ^ 40 * 2058359 * 2
def baseEnd_2058359 : Nat := 352309175502672464882095

theorem tailTrace_2058359 : CollatzResearch.WordTrace tailWord_2058359 prefixEnd_2058359 352309175502672464882095 := by
  unfold tailWord_2058359
  simp only [CollatzResearch.WordTrace]
  refine ⟨75074520349924357574802131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50049680233282905049868087 75074520349924357574802131)
  ·
    refine ⟨112611780524886536362203197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75074520349924357574802131 112611780524886536362203197)
    ·
      refine ⟨42229417696832451135826199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112611780524886536362203197 42229417696832451135826199)
      ·
        refine ⟨63344126545248676703739299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42229417696832451135826199 63344126545248676703739299)
        ·
          refine ⟨95016189817873015055608949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63344126545248676703739299 95016189817873015055608949)
          ·
            refine ⟨8907767795425595161463339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95016189817873015055608949 8907767795425595161463339)
            ·
              refine ⟨13361651693138392742195009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8907767795425595161463339 13361651693138392742195009)
              ·
                refine ⟨10021238769853794556646257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13361651693138392742195009 10021238769853794556646257)
                ·
                  refine ⟨7515929077390345917484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021238769853794556646257 7515929077390345917484693)
                  ·
                    refine ⟨352309175502672464882095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7515929077390345917484693 352309175502672464882095)
                    ·
                      rfl

theorem cell23_2058359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_2058359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058359 prefixEnd_2058359 := by exact prefixLift 2058359
  have htrace : WordTrace (prefixWord ++ tailWord_2058359) baseStart_2058359 baseEnd_2058359 := by
    simpa [prefixWord, tailWord_2058359, baseEnd_2058359] using wordTrace_append hprefix tailTrace_2058359
  have hstable : (prefixWord ++ tailWord_2058359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058359).length < 2 ^ (prefixWord ++ tailWord_2058359).sum := by decide
  have hdescent : baseEnd_2058359 < baseStart_2058359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058376 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_2058376 : Nat := 118140960795 + 2058376 * 2 ^ 59
def prefixEnd_2058376 : Nat := 4983230072969 + 3 ^ 40 * 2058376 * 2
def baseEnd_2058376 : Nat := 352312085226381276044569

theorem tailTrace_2058376 : CollatzResearch.WordTrace tailWord_2058376 prefixEnd_2058376 352312085226381276044569 := by
  unfold tailWord_2058376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537570195431384739085491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50050093593908512985447321 37537570195431384739085491)
  ·
    refine ⟨56306355293147077108628237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37537570195431384739085491 56306355293147077108628237)
    ·
      refine ⟨21114883234930153915735589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56306355293147077108628237 21114883234930153915735589)
      ·
        refine ⟨3959040606549403859200423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21114883234930153915735589 3959040606549403859200423)
        ·
          refine ⟨5938560909824105788800635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959040606549403859200423 5938560909824105788800635)
          ·
            refine ⟨8907841364736158683200953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938560909824105788800635 8907841364736158683200953)
            ·
              refine ⟨6680881023552119012400715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8907841364736158683200953 6680881023552119012400715)
              ·
                refine ⟨10021321535328178518601073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680881023552119012400715 10021321535328178518601073)
                ·
                  refine ⟨7515991151496133888950805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021321535328178518601073 7515991151496133888950805)
                  ·
                    refine ⟨352312085226381276044569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7515991151496133888950805 352312085226381276044569)
                    ·
                      rfl

theorem cell23_2058376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_2058376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058376 prefixEnd_2058376 := by exact prefixLift 2058376
  have htrace : WordTrace (prefixWord ++ tailWord_2058376) baseStart_2058376 baseEnd_2058376 := by
    simpa [prefixWord, tailWord_2058376, baseEnd_2058376] using wordTrace_append hprefix tailTrace_2058376
  have hstable : (prefixWord ++ tailWord_2058376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058376).length < 2 ^ (prefixWord ++ tailWord_2058376).sum := by decide
  have hdescent : baseEnd_2058376 < baseStart_2058376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058386 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2058386 : Nat := 118140960795 + 2058386 * 2 ^ 59
def prefixEnd_2058386 : Nat := 4983230072969 + 3 ^ 40 * 2058386 * 2
def baseEnd_2058386 : Nat := 1056941390485688789008661

theorem tailTrace_2058386 : CollatzResearch.WordTrace tailWord_2058386 prefixEnd_2058386 1056941390485688789008661 := by
  unfold tailWord_2058386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18768876280206635296508753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50050336747217694124023341 18768876280206635296508753)
  ·
    refine ⟨14076657210154976472381565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18768876280206635296508753 14076657210154976472381565)
    ·
      refine ⟨5278746453808116177143087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14076657210154976472381565 5278746453808116177143087)
      ·
        refine ⟨7918119680712174265714631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278746453808116177143087 7918119680712174265714631)
        ·
          refine ⟨11877179521068261398571947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918119680712174265714631 11877179521068261398571947)
          ·
            refine ⟨17815769281602392097857921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11877179521068261398571947 17815769281602392097857921)
            ·
              refine ⟨13361826961201794073393441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17815769281602392097857921 13361826961201794073393441)
              ·
                refine ⟨10021370220901345555045081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13361826961201794073393441 10021370220901345555045081)
                ·
                  refine ⟨7516027665676009166283811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10021370220901345555045081 7516027665676009166283811)
                  ·
                    refine ⟨11274041498514013749425717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7516027665676009166283811 11274041498514013749425717)
                    ·
                      refine ⟨1056941390485688789008661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11274041498514013749425717 1056941390485688789008661)
                      ·
                        rfl

theorem cell23_2058386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2058386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058386 prefixEnd_2058386 := by exact prefixLift 2058386
  have htrace : WordTrace (prefixWord ++ tailWord_2058386) baseStart_2058386 baseEnd_2058386 := by
    simpa [prefixWord, tailWord_2058386, baseEnd_2058386] using wordTrace_append hprefix tailTrace_2058386
  have hstable : (prefixWord ++ tailWord_2058386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058386).length < 2 ^ (prefixWord ++ tailWord_2058386).sum := by decide
  have hdescent : baseEnd_2058386 < baseStart_2058386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058389 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 7]
def baseStart_2058389 : Nat := 118140960795 + 2058389 * 2 ^ 59
def prefixEnd_2058389 : Nat := 4983230072969 + 3 ^ 40 * 2058389 * 2
def baseEnd_2058389 : Nat := 117438103436405808585683

theorem tailTrace_2058389 : CollatzResearch.WordTrace tailWord_2058389 prefixEnd_2058389 117438103436405808585683 := by
  unfold tailWord_2058389
  simp only [CollatzResearch.WordTrace]
  refine ⟨75075614539815672698394221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50050409693210448465596147 75075614539815672698394221)
  ·
    refine ⟨28153355452430877261897833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75075614539815672698394221 28153355452430877261897833)
    ·
      refine ⟨21115016589323157946423375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28153355452430877261897833 21115016589323157946423375)
      ·
        refine ⟨31672524883984736919635063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21115016589323157946423375 31672524883984736919635063)
        ·
          refine ⟨47508787325977105379452595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31672524883984736919635063 47508787325977105379452595)
          ·
            refine ⟨71263180988965658069178893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47508787325977105379452595 71263180988965658069178893)
            ·
              refine ⟨26723692870862121775942085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71263180988965658069178893 26723692870862121775942085)
              ·
                refine ⟨5010692413286647832989141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26723692870862121775942085 5010692413286647832989141)
                ·
                  refine ⟨117438103436405808585683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5010692413286647832989141 117438103436405808585683)
                  ·
                    rfl

theorem cell23_2058389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_2058389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058389 prefixEnd_2058389 := by exact prefixLift 2058389
  have htrace : WordTrace (prefixWord ++ tailWord_2058389) baseStart_2058389 baseEnd_2058389 := by
    simpa [prefixWord, tailWord_2058389, baseEnd_2058389] using wordTrace_append hprefix tailTrace_2058389
  have hstable : (prefixWord ++ tailWord_2058389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058389).length < 2 ^ (prefixWord ++ tailWord_2058389).sum := by decide
  have hdescent : baseEnd_2058389 < baseStart_2058389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058449 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2058449 : Nat := 118140960795 + 2058449 * 2 ^ 59
def prefixEnd_2058449 : Nat := 4983230072969 + 3 ^ 40 * 2058449 * 2
def baseEnd_2058449 : Nat := 352324579922307347506957

theorem tailTrace_2058449 : CollatzResearch.WordTrace tailWord_2058449 prefixEnd_2058449 352324579922307347506957 := by
  unfold tailWord_2058449
  simp only [CollatzResearch.WordTrace]
  refine ⟨75077802919598302945578401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50051868613065535297052267 75077802919598302945578401)
  ·
    refine ⟨56308352189698727209183801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75077802919598302945578401 56308352189698727209183801)
    ·
      refine ⟨42231264142274045406887851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56308352189698727209183801 42231264142274045406887851)
      ·
        refine ⟨63346896213411068110331777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42231264142274045406887851 63346896213411068110331777)
        ·
          refine ⟨47510172160058301082748833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63346896213411068110331777 47510172160058301082748833)
          ·
            refine ⟨35632629120043725812061625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47510172160058301082748833 35632629120043725812061625)
            ·
              refine ⟨26724471840032794359046219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35632629120043725812061625 26724471840032794359046219)
              ·
                refine ⟨40086707760049191538569329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26724471840032794359046219 40086707760049191538569329)
                ·
                  refine ⟨30065030820036893653926997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40086707760049191538569329 30065030820036893653926997)
                  ·
                    refine ⟨352324579922307347506957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30065030820036893653926997 352324579922307347506957)
                    ·
                      rfl

theorem cell23_2058449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2058449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058449 prefixEnd_2058449 := by exact prefixLift 2058449
  have htrace : WordTrace (prefixWord ++ tailWord_2058449) baseStart_2058449 baseEnd_2058449 := by
    simpa [prefixWord, tailWord_2058449, baseEnd_2058449] using wordTrace_append hprefix tailTrace_2058449
  have hstable : (prefixWord ++ tailWord_2058449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058449).length < 2 ^ (prefixWord ++ tailWord_2058449).sum := by decide
  have hdescent : baseEnd_2058449 < baseStart_2058449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058459 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_2058459 : Nat := 118140960795 + 2058459 * 2 ^ 59
def prefixEnd_2058459 : Nat := 4983230072969 + 3 ^ 40 * 2058459 * 2
def baseEnd_2058459 : Nat := 1056978874573467003395825

theorem tailTrace_2058459 : CollatzResearch.WordTrace tailWord_2058459 prefixEnd_2058459 1056978874573467003395825 := by
  unfold tailWord_2058459
  simp only [CollatzResearch.WordTrace]
  refine ⟨75078167649562074653442431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50052111766374716435628287 75078167649562074653442431)
  ·
    refine ⟨112617251474343111980163647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75078167649562074653442431 112617251474343111980163647)
    ·
      refine ⟨168925877211514667970245471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112617251474343111980163647 168925877211514667970245471)
      ·
        refine ⟨253388815817272001955368207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168925877211514667970245471 253388815817272001955368207)
        ·
          refine ⟨380083223725908002933052311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253388815817272001955368207 380083223725908002933052311)
          ·
            refine ⟨570124835588862004399578467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380083223725908002933052311 570124835588862004399578467)
            ·
              refine ⟨855187253383293006599367701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570124835588862004399578467 855187253383293006599367701)
              ·
                refine ⟨40086902502341859684345361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 855187253383293006599367701 40086902502341859684345361)
                ·
                  refine ⟨30065176876756394763259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40086902502341859684345361 30065176876756394763259021)
                  ·
                    refine ⟨11274441328783648036222133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30065176876756394763259021 11274441328783648036222133)
                    ·
                      refine ⟨1056978874573467003395825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11274441328783648036222133 1056978874573467003395825)
                      ·
                        rfl

theorem cell23_2058459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_2058459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2058459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2058459 prefixEnd_2058459 := by exact prefixLift 2058459
  have htrace : WordTrace (prefixWord ++ tailWord_2058459) baseStart_2058459 baseEnd_2058459 := by
    simpa [prefixWord, tailWord_2058459, baseEnd_2058459] using wordTrace_append hprefix tailTrace_2058459
  have hstable : (prefixWord ++ tailWord_2058459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058459).length < 2 ^ (prefixWord ++ tailWord_2058459).sum := by decide
  have hdescent : baseEnd_2058459 < baseStart_2058459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
